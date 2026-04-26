module SAPICPrinter where
import Text.PrettyPrint
import Term
import SAPIC
import SAPICSetup
import Data.Char (toUpper)
import Prelude hiding ((<>))

-- | Tamarin facts (and SAPIC+ events) must start with an uppercase letter.
capitalize :: String -> String
capitalize "" = ""
capitalize (c:cs) = toUpper c : cs

-- | Sanitize identifiers so they're valid Tamarin/SAPIC+ variable names.
-- The IR carries labels like @l[A]@ from termToLabel; SAPIC+ identifiers
-- are alphanumeric+underscore only.
sanitizeIdent :: String -> String
sanitizeIdent = concatMap esc
  where
    esc '['  = "_"
    esc ']'  = ""
    esc '('  = "_"
    esc ')'  = ""
    esc ','  = "_"
    esc ' '  = ""
    esc c    = [c]

-- | Map ProVerif helpers to their Tamarin builtin counterparts where the
-- arity and semantics match cleanly. Names that collide with Tamarin
-- builtins but can't be cleanly mapped are prefixed with @pv_@.
renameFun :: String -> String
renameFun f = case f of
    -- Symmetric encryption: equation sdec(senc(m,k),k)=m only needs the
    -- same key term on both sides; our IR uses the same opaque expression,
    -- so the builtin equation fires correctly.
    "scrypt"  -> "senc"            -- builtin: symmetric-encryption
    "dscrypt" -> "sdec"            -- builtin: symmetric-encryption
    -- Asymmetric encryption: we keep ProVerif's agent-indexed-keypair
    -- algebra (pv_pk, pv_inv, pubk, crypt, dcrypt) and declare it as a
    -- user equational theory in SAPICSetup, instead of trying to bridge
    -- to Tamarin's pk(sk) builtin (which rejects user equations on its
    -- constructor symbols).
    -- Conflicts with builtins, no clean rewrite available: keep prefixed.
    _ | f `elem` reserved -> "pv_" ++ f
      | otherwise         -> f
  where
    -- Note: fst, snd, pair are NOT in this list. They are Tamarin's
    -- builtin pair destructors (fst(<x,y>)=x, snd(<x,y>)=y), and our
    -- IR's fst/snd are pair destructors with the same semantics, so we
    -- want them to share the equation. Renaming them to pv_fst/pv_snd
    -- left them opaque and made every pair-destructuring check fail,
    -- killing the protocol.
    reserved =
      [ "pk", "inv", "sign", "verify"
      , "aenc", "adec", "senc", "sdec"
      , "mac", "h", "kdf"
      , "exp", "g", "mun"
      , "true", "false"
      ]

-- | ProVerif's typeConverter functions are no-ops in Tamarin's untyped
-- world; we drop them so structural unification under the equational
-- theory can fire (e.g., vsign(t, kdf(pk(A))) becomes vsign(t, pk(A))
-- which can unify with vsign(sign(m, inv(pk(A))), pk(A)) = pv_true).
typeConverters :: [String]
typeConverters =
    [ "kdf", "invkdf", "skdf"
    , "pubkey2bitstring", "privkey2bitstring", "agent2bitstring", "skey2bitstring"
    ]

ppTerm :: Term String String -> Doc
ppTerm (Var v) = text (sanitizeIdent v)
-- Pair constructor in the IR is Fun "" [a, b, ...]; SAPIC+ writes it as <a, b, ...>.
ppTerm (Fun "" args) = text "<" <> hcat (punctuate comma (map ppTerm args)) <> text ">"
-- DH: exp(t1, t2) is the builtin infix t1 ^ t2.
ppTerm (Fun "exp" [a, b]) = parens (ppTerm a) <> text "^" <> parens (ppTerm b)
-- DH: g is the builtin constant 'g'.
ppTerm (Fun "g" []) = text "'g'"
-- ProVerif type-converters are erased.
ppTerm (Fun f [arg]) | f `elem` typeConverters = ppTerm arg
ppTerm (Fun f []) = text (renameFun f)
ppTerm (Fun f args) = text (renameFun f) <> parens (hcat $ punctuate comma (map ppTerm args))

-- | Pretty-print the body of a sequential prefix (in/out/new/let/event).
-- SAPIC+'s ';' binds tighter than '||', so when the body is a parallel
-- composition we must wrap it in parens or the binding scope shrinks
-- to just the first parallel branch.
ppBody :: SapicProcess -> Doc
ppBody p@(SPar _ _) = parens (ppSapic p)
ppBody p            = ppSapic p

ppSapic :: SapicProcess -> Doc
ppSapic SZero = text "0"
ppSapic (SOut t p) =
    text "out" <> parens (ppTerm t) <> semi $$ ppBody p
ppSapic (SIn t p) =
    text "in"  <> parens (ppTerm t) <> semi $$ ppBody p
ppSapic (SNew x p) =
    text "new" <+> text x <> semi $$ ppBody p
ppSapic (SLet x t p) =
    text "let" <+> text x <+> equals <+> ppTerm t <+> text "in" $$ ppBody p
ppSapic (SEvent name args p) =
    text "event" <+> text (capitalize name) <> parens (hcat $ punctuate comma (map ppTerm args)) <> semi $$ ppBody p
ppSapic (SIf t1 t2 p q) =
    text "if" <+> ppTerm t1 <+> equals <+> ppTerm t2 <+> text "then" $$
    nest 2 (ppSapic p) $$
    text "else" $$
    nest 2 (ppSapic q)
ppSapic (SChoice []) = text "0"
ppSapic (SChoice [p]) = ppSapic p
ppSapic (SChoice (p:ps)) =
    parens (ppSapic p) <+> text "+" <+> ppSapic (SChoice ps)
ppSapic (SPar p q) =
    parens (ppSapic p) $$ text "||" $$ parens (ppSapic q)
ppSapic (SBang p) =
    text "!" <> parens (ppSapic p)
ppSapic (SLookup t x p q) =
    text "lookup" <+> ppTerm t <+> text "as" <+> text x <+> text "in" $$
    nest 2 (ppSapic p) $$
    text "else" $$
    nest 2 (ppSapic q)
ppSapic (SInsert t1 t2 p) =
    text "insert" <+> ppTerm t1 <> comma <+> ppTerm t2 <> semi $$ ppSapic p
ppSapic (SLock t p)   = text "lock"   <+> ppTerm t <> semi $$ ppSapic p
ppSapic (SUnlock t p) = text "unlock" <+> ppTerm t <> semi $$ ppSapic p

-- | Wrap a single process in a complete SAPIC+ theory, plus lemma blocks
-- derived from the choreography's security goals. The goal arguments
-- are: weak-auth goals, strong-auth goals, secrecy goals.
-- Each (begin/end) auth event has the shape (verifier, claimant, term).
-- Each secrecy event has shape (agent_1, ..., agent_n, secret).
generateCompleteSapicFile
    :: String
    -> Bool                                                       -- emit sanity (exists-trace) lemmas?
    -> [(String, Int)]                                            -- user-defined functions (name, arity)
    -> [(String, Int)]                                            -- secrecy goals: (event name, arity)
    -> [String]                                                   -- weak-auth event names
    -> [String]                                                   -- strong-auth event names
    -> SapicProcess
    -> String
generateCompleteSapicFile theoryName sanity userFuncs secrecyGoals weakAuths strongAuths p =
    sapicTheoryHeader theoryName ++
    userFunctionDeclarations userFuncs ++
    concatMap (\(name, n) -> secrecyLemma name n ++ "\n") secrecyGoals ++
    concatMap (\name -> weakAuthLemma name ++ "\n") weakAuths ++
    concatMap (\name -> strongAuthLemma name ++ "\n") strongAuths ++
    (if sanity then sanityBlock secrecyGoals weakAuths strongAuths else "") ++
    "process:\n" ++
    render (nest 2 (ppSapic p)) ++ "\n\n" ++
    sapicTheoryFooter

-- | Exists-trace executability lemmas. If any of these is falsified,
-- the corresponding all-traces lemma above it is vacuously true and
-- the verification result is meaningless.
sanityBlock :: [(String, Int)] -> [String] -> [String] -> String
sanityBlock secrecyGoals weakAuths strongAuths =
    "// --- Sanity (executability) lemmas ---\n" ++
    "// If any of these is FALSIFIED the protocol is dead in Tamarin's\n" ++
    "// semantics and the all-traces lemmas above are vacuously true.\n" ++
    concatMap (\(name, n) -> sanitySecrecy name n ++ "\n") secrecyGoals ++
    concatMap (\name -> sanityAuth name ++ "\n") (weakAuths ++ strongAuths)

-- | Exists-trace check that the secrecy event itself ever fires.
sanitySecrecy :: String -> Int -> String
sanitySecrecy name nArgs =
    let vars = ["x" ++ show i | i <- [1..nArgs]]
        argList = unwords vars
        argTuple = intercalate ", " vars
    in "lemma exec_" ++ name ++ ":\n" ++
       "  exists-trace\n" ++
       "  \"Ex " ++ argList ++ " #i. " ++ capitalize name ++ "(" ++ argTuple ++ ") @ #i\"\n"

-- | Exists-trace check that the End-event of an auth goal ever fires.
sanityAuth :: String -> String
sanityAuth name =
    let endName = capitalize ("end" ++ name)
    in "lemma exec_" ++ endName ++ ":\n" ++
       "  exists-trace\n" ++
       "  \"Ex a b m #i. " ++ endName ++ "(a, b, m) @ #i\"\n"

-- | Emit a "functions:" block for user-declared symbols from the
-- choreography (tags, public constants, hash families, etc.). Names that
-- collide with Tamarin builtins are pv_-prefixed so the declarations
-- stay consistent with what ppTerm prints in process bodies.
userFunctionDeclarations :: [(String, Int)] -> String
userFunctionDeclarations [] = ""
userFunctionDeclarations funcs =
    "// User-defined functions and constants from the choreography.\n" ++
    "functions:\n  " ++
    intercalate ",\n  " [renameFun n ++ "/" ++ show ar | (n, ar) <- funcs] ++
    "\n\n"

-- | Secrecy lemma: the secret (last argument) is never derivable by the
-- attacker in any trace where the secrecy event fires. We don't model
-- corruption explicitly, so this lemma will fail whenever any of the
-- listed agents is the intruder; the ProVerif backend handles this with
-- A <> i clauses, which Tamarin doesn't support directly without an
-- explicit corruption model.
secrecyLemma :: String -> Int -> String
secrecyLemma name nArgs =
    let vars = ["x" ++ show i | i <- [1..nArgs]]
        secret = last vars
        argList = unwords vars
        argTuple = intercalate ", " vars
    in "lemma " ++ name ++ "_secrecy:\n" ++
       "  \"All " ++ argList ++ " #i.\n" ++
       "    " ++ capitalize name ++ "(" ++ argTuple ++ ") @ #i\n" ++
       "    ==> not (Ex #j. K(" ++ secret ++ ") @ #j)\"\n"

-- | Weak (non-injective) authentication: every End-event is preceded by
-- a matching Begin-event with the same arguments.
-- The event names in the IR are already "begin{name}"/"end{name}" and
-- only the first letter is capitalized on emit, so the lemma must
-- reference "End{name}" / "Begin{name}" with that same casing.
weakAuthLemma :: String -> String
weakAuthLemma name =
    let endName   = capitalize ("end"   ++ name)
        beginName = capitalize ("begin" ++ name)
    in "lemma " ++ name ++ ":\n" ++
       "  \"All a b m #i.\n" ++
       "    " ++ endName ++ "(a, b, m) @ #i\n" ++
       "    ==> Ex #j. " ++ beginName ++ "(a, b, m) @ #j\"\n"

-- | Strong (injective) authentication: every End-event is preceded by a
-- distinct matching Begin-event (no two End-events share a Begin).
strongAuthLemma :: String -> String
strongAuthLemma name =
    let endName   = capitalize ("end"   ++ name)
        beginName = capitalize ("begin" ++ name)
    in "lemma " ++ name ++ "_inj:\n" ++
       "  \"All a b m #i.\n" ++
       "    " ++ endName ++ "(a, b, m) @ #i\n" ++
       "    ==> (Ex #j. " ++ beginName ++ "(a, b, m) @ #j & #j < #i)\n" ++
       "      & (All #i2. " ++ endName ++ "(a, b, m) @ #i2 ==> #i = #i2)\"\n"

intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs
