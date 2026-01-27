module LocalPretty where

import Text.PrettyPrint as PP
import Local
import Term  
import Choreo
import Data.List (intercalate, intersperse)
import Prelude hiding ((<>))
import Data.Function ((&))



prettyTerm :: (f -> String) -> (v -> String) -> Term f v -> Doc
prettyTerm funcRender varRender term = case term of
    Var v -> text (varRender v)
    Fun f args -> text (funcRender f) <> parens (prettyTermList funcRender varRender args)

prettyTermList :: (f -> String) -> (v -> String) -> [Term f v] -> Doc
prettyTermList funcRender varRender terms = 
    hsep $ punctuate comma $ map (prettyTerm funcRender varRender) terms

prettyLocal :: (f -> String) -> (v -> String) -> Local f v -> Doc
prettyLocal funcRender varRender LEnd = text "end"
prettyLocal funcRender varRender (LSend term cont) =
    text "send" <> parens (prettyTerm funcRender varRender term) <> char '.' $$
    prettyLocal funcRender varRender cont
prettyLocal funcRender varRender (LReceive var cont) =
    text "receive" <> parens (text (varRender var)) <> char '.' $$
    prettyLocal funcRender varRender cont
prettyLocal funcRender varRender (LAtomic atomic) =
    prettyLAtomic funcRender varRender atomic

prettyLAtomic :: (f -> String) -> (v -> String) -> LAtomic f v -> Doc
prettyLAtomic funcRender varRender (LNonce var cont) =
    text "new" <+> text (varRender var) <> char '.' $$
    prettyLAtomic funcRender varRender cont
prettyLAtomic funcRender varRender (LLet var term cont) =
    text "let" <+> text (varRender var) <+> text "<-" <+> prettyTerm funcRender varRender term <+> text "in" $$
    prettyLAtomic funcRender varRender cont
prettyLAtomic funcRender varRender (LEvent name terms cont) =
    text "event" <+> text name <> parens (prettyTermList funcRender varRender terms) <> char '.' $$
    prettyLAtomic funcRender varRender cont
prettyLAtomic funcRender varRender (LChoice atomics) =
    char '{' $$
    (
        map (nest 2 . prettyLAtomic funcRender varRender) atomics
        & intersperse (char '+')
        & vcat
    ) $$
    char '}'
prettyLAtomic funcRender varRender (LBranch cond1 cond2 trueBranch falseBranch) =
    text "if" <+> prettyTerm funcRender varRender cond1 <+> text "==" <+> prettyTerm funcRender varRender cond2 <+> text "then" $$
    nest 2 (prettyLAtomic funcRender varRender trueBranch) $$
    text "else" $$
    nest 2 (prettyLAtomic funcRender varRender falseBranch)
prettyLAtomic funcRender varRender (LRead name v term cont) =
    prettyTerm funcRender varRender term <+> text ":=" <+> text name <> brackets (text (varRender v)) <> char '.' $$
    prettyLAtomic funcRender varRender cont
prettyLAtomic funcRender varRender (LWrites writes) =
    prettyLWrites funcRender varRender writes

prettyLWrites :: (f -> String) -> (v -> String) -> LWrites f v -> Doc
prettyLWrites funcRender varRender (LWrite name addr value cont) =
    text name <> brackets (prettyTerm funcRender varRender addr) <+> text ":=" <+> prettyTerm funcRender varRender value <> char '.' $$
    prettyLWrites funcRender varRender cont
prettyLWrites funcRender varRender (Local local) =
    prettyLocal funcRender varRender local

-- | Pretty-print local protocol using string representations.
prettyLocalString :: Local String String -> Doc
prettyLocalString = prettyLocal id id


renderLocal :: (f -> String) -> (v -> String) -> Local f v -> String
renderLocal funcRender varRender = render . prettyLocal funcRender varRender

renderLocalString :: Local String String -> String
renderLocalString = render . prettyLocalString
