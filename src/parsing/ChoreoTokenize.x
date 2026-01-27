{
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module ChoreoTokenize where
}

%wrapper "posn"

$digit = 0-9
$alphaL = [a-zæøå]
$alphaU = [A-ZÆØÅ]
$alpha = [a-zæøåA-ZÆØÅ]


tokens :-
    $white+                       ;
    "#".*                         ;
    "->"                          { \p s -> Tok (p,TRIGHTARROW) }
    "<-"                          { \p s -> Tok (p,TLEFTARROW) }
    "==>"                         { \p s -> Tok (p,TLONGRIGHTARROW)}
    "&&"                          { \p s -> Tok (p,TAND)}
    "<>"                          { \p s -> Tok (p,TNEQ)}
    ":="                          { \p s -> Tok (p,TASSIGN) }
    "=="                          { \p s -> Tok (p,TEQ) }
    "."                           { \p s -> Tok (p,TDOT) }
    ","                           { \p s -> Tok (p,TCOMMA) }
    ":"                           { \p s -> Tok (p,TCOLON) }
    ";"                           { \p s -> Tok (p,TSEMI) }
    "+"                           { \p s -> Tok (p,TPLUS) }
    "/"                           { \p s -> Tok (p,TSLASH) }
    \{                            { \p s -> Tok (p,TLCURL) }
    \}                            { \p s -> Tok (p,TRCURL) }
    \(                            { \p s -> Tok (p,TLPAR) }
    \)                            { \p s -> Tok (p,TRPAR) }
    \[                            { \p s -> Tok (p,TLSQR) }
    \]                            { \p s -> Tok (p,TRSQR) }
    init                          { \p s -> Tok (p,TINIT) }
    forall                        { \p s -> Tok (p,TFORALL) }
    attacker                      { \p s -> Tok (p,TATTACKER) }
    event                         { \p s -> Tok (p,TEVENT) }
    "inj-event"                   { \p s -> Tok (p,TINJEVENT) }
    0                             { \p s -> Tok (p,TEND) }
    end                           { \p s -> Tok (p,TEND) }
    lock                          { \p s -> Tok (p,TLOCK) }
    unlock                        { \p s -> Tok (p,TUNLOCK) }
    new                           { \p s -> Tok (p,TNEW) }
    if                            { \p s -> Tok (p,TIF) }
    then                          { \p s -> Tok (p,TTHEN) }
    else                          { \p s -> Tok (p,TELSE) }
    let                           { \p s -> Tok (p,TLET) }
    in                            { \p s -> Tok (p,TIN) }
    secret                        { \p s -> Tok (p,TSECRET) }
    between                       { \p s -> Tok (p,TBETWEEN) }
    authenticates                 { \p s -> Tok (p,TAUTHENTICATES) }
    on                            { \p s -> Tok (p,TON) }
    weakly                        { \p s -> Tok (p,TWEAKLY) }
    cell                          { \p s -> Tok (p,TCELL) }
    choreo                        { \p s -> Tok (p,TCHOREO) }
    knowledge                     { \p s -> Tok (p,TKNOWLEDGE) }
    functions                     { \p s -> Tok (p,TFUNCTIONS) }
    cells                         { \p s -> Tok (p,TCELLS) }
    public                        { \p s -> Tok (p,TPUBLIC) }
    private                       { \p s -> Tok (p,TPRIVATE) }
    agents                        { \p s -> Tok (p,TAGENTS) }
    trusted                       { \p s -> Tok (p,TTRUSTED) }
    untrusted                     { \p s -> Tok (p,TUNTRUSTED) }
    types                         { \p s -> Tok (p,TTYPES) }
    events                        { \p s -> Tok (p,TEVENTS) }
    queries                       { \p s -> Tok (p,TQUERIES) }
    query                         { \p s -> Tok (p,TQUERY) }
    knows                         { \p s -> Tok (p,TKNOWS) }
    $alphaL [$alpha $digit \_ \']* { \p s -> Tok (p,SymL s) }
    $alphaU [$alpha $digit \_ \']* { \p s -> Tok (p,SymU s) }


{
data TokenName
    = TRIGHTARROW 
    | TLEFTARROW
    | TSLASH
    | TASSIGN
    | TINIT
    | TEQ
    | TDOT
    | TCOMMA
    | TCOLON
    | TSEMI
    | TPLUS
    | TLCURL
    | TRCURL
    | TLPAR
    | TRPAR
    | TLSQR
    | TRSQR
    | TEND
    | TLOCK
    | TUNLOCK
    | TNEW
    | TIF
    | TTHEN
    | TELSE 
    | TIN
    | TLET 
    | TSECRET
    | TBETWEEN
    | TON
    | TAUTHENTICATES
    | TWEAKLY
    | TCELL
    | TCHOREO
    | TKNOWLEDGE
    | TFUNCTIONS
    | TCELLS
    | TPUBLIC
    | TPRIVATE
    | TAGENTS
    | TTRUSTED
    | TUNTRUSTED
    | TTYPES
    | TQUERIES
    | TQUERY
    | TEVENTS
    | TKNOWS
    | TLONGRIGHTARROW
    | TAND
    | TOR
    | TNEQ
    | TFORALL
    | TATTACKER
    | TEVENT
    | TINJEVENT
    | SymU String
    | SymL String
    deriving (Show,Eq)

data Token = Tok (AlexPosn,TokenName)
    deriving (Show,Eq)

token_posn (Tok (p,_)) = p
token_name (Tok (_,n)) = n
}