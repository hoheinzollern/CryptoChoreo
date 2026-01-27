{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
module ChoreoParser (parseChoreo,parseTerm) where
import ChoreoTokenize
import Term
import Choreo
import ProVerif (PVFormula(..))
import Util (insertSetSetMap)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Bifunctor as Bifunctor
}


%name parseChoreo Main
%name parseTerm Term
%tokentype { Token }
%error { parseError }

%token 
    rightarrow { Tok(_,TRIGHTARROW) }
    leftarrow  { Tok(_,TLEFTARROW) }
    slash   { Tok(_,TSLASH) }
    assign  { Tok(_,TASSIGN) }
    init    { Tok(_,TINIT) }
    eq      { Tok(_,TEQ) }
    dot     { Tok(_,TDOT) }
    comma   { Tok(_,TCOMMA) }
    colon   { Tok(_,TCOLON) }
    plus    { Tok(_,TPLUS) }
    lcurl   { Tok(_,TLCURL) }
    rcurl   { Tok(_,TRCURL) }
    lpar    { Tok(_,TLPAR) }
    rpar    { Tok(_,TRPAR) }
    lsqr    { Tok(_,TLSQR) }
    rsqr    { Tok(_,TRSQR) }
    end     { Tok(_,TEND) }
    lock    { Tok(_,TLOCK) }
    unlock  { Tok(_,TUNLOCK) }
    new     { Tok(_,TNEW) }
    if      { Tok(_,TIF) }
    then    { Tok(_,TTHEN) }
    else    { Tok(_,TELSE) }
    let     { Tok(_,TLET) }
    in      { Tok(_,TIN) }
    secret  { Tok(_,TSECRET) }
    between { Tok(_,TBETWEEN) }
    on      { Tok(_,TON) }
    authenticates  { Tok(_,TAUTHENTICATES) }
    cell    { Tok(_,TCELL) }
    weakly  { Tok(_,TWEAKLY) }
    choreo  { Tok(_,TCHOREO) }
    knowledge { Tok(_,TKNOWLEDGE) }
    functions { Tok(_,TFUNCTIONS) }
    cells   { Tok(_,TCELLS) }
    public  { Tok(_,TPUBLIC) }
    private { Tok(_,TPRIVATE) }
    agents  { Tok(_,TAGENTS) }
    trusted { Tok(_,TTRUSTED) }
    untrusted { Tok(_,TUNTRUSTED) }
    types { Tok(_,TTYPES) }
    queries { Tok(_,TQUERIES) }
    query { Tok(_,TQUERY) }
    events { Tok(_,TEVENTS) }
    knows   { Tok(_,TKNOWS) }
    longrightarrow { Tok(_,TLONGRIGHTARROW) }
    and     { Tok(_,TAND) }
    neq     { Tok(_,TNEQ) }
    semi    { Tok(_,TSEMI) }
    forall  { Tok(_,TFORALL) }
    attacker{ Tok(_,TATTACKER) }
    event   { Tok(_,TEVENT) }
    injevent   { Tok(_,TINJEVENT) }
    symL    { Tok(_,SymL $$) }
    symU    { Tok(_,SymU $$) }

%right longrightarrow
%left and

%%

Term :: { Term String String }
    : symL lpar TermList rpar  { Fun $1 $3 }
    | symL lpar rpar           { Fun $1 [] }
    | symL                     { Fun $1 [] }
    | symU                     { Var $1 }
    | lpar TermList rpar       { pairify $2 }
TermList :: { [Term String String] }
    : Term comma TermList      { $1 : $3 }
    | Term                     { [$1] }
TermList2 :: { Set.Set (Term String String) }
    : Term TermList2           { Set.insert $1 $2 }
    | Term                     { Set.singleton $1 }

Agent :: { Agent String String }
    : symL  { Trusted $1 }
    | symU  { Untrusted $1 }
AgentList :: { [Agent String String] }
    : Agent AgentList { $1 : $2 }
    | Agent           { [$1] }

Goals :: { Goals String String }
    : Goal dot Goals { $1 $3 }
    | Goal           { $1 EndGoals }
    | end            { EndGoals }
Goal :: { Goals String String -> Goals String String }
    : Term secret between AgentList            { Secret $4 $1 }
    | Agent authenticates Agent on Term        { StrongAuth $3 $1 $5 }
    | Agent weakly authenticates Agent on Term { WeakAuth $4 $1 $6 }


Atomic :: { InitialAtomic String String }
    : Term assign symL lsqr Term rsqr dot Atomic { IRead $3 $1 $5 $8 }
    | if Term eq Term then Atomic else Atomic    { IBranch $2 $4 $6 $8 }
    | if Term eq Term then Atomic                { IBranch $2 $4 $6 (IWrites (IChoreo (IEnd EndGoals))) }
    --| let symU leftarrow Term in Atomic          { ILet2 $2 $4 $6 } nice to have, but causes reduce/reduce conflicts
    | event symL lpar rpar dot Atomic            { IEvent $2 [] $6 }
    | event symL lpar TermList rpar dot Atomic   { IEvent $2 $4 $7 }
    | new symU NewList dot Atomic                { INonce $2 $3 $5 }
    | lcurl AtomicList rcurl                     { IChoice $2 }
    | Writes                                     { IWrites $1 }

Writes :: { InitialWrites String String }
    : symL lsqr  Term rsqr assign Term dot Writes      { IWrite $1 $3 $6 $8 }
    | Choreo                                                     { IChoreo $1 }

AtomicList :: { [InitialAtomic String String] }
    : Atomic plus AtomicList { $1 : $3 }
    | Atomic                 { [$1] }
Choreo :: { InitialChoreo String String }
    : Agent rightarrow Agent colon Term dot Choreo         { ISend $1 $3 $5 $7 }
    | let symU leftarrow Term in Choreo                    { ILet1 $2 $4 $6 } 
    | Agent colon Atomic                                   { IAtomic $1 $3 }
    | Goals                                                { IEnd $1 }

NewList :: { [Term String String] }
    : slash Term NewList  { $2 : $3 }
    |                     { [] }



Knowledge :: { Map.Map (Agent String String) (Set.Set (Term String String)) }
    : Agent knows TermList2 dot Knowledge { insertSetSetMap $1 $3 $5 }
    | Agent knows TermList2     { insertSetSetMap $1 $3 Map.empty }
    |                           { Map.empty }



Queries :: { [([(String,String)],PVFormula)] }
    : Query Queries { $1 : $2 }
    |               { [] }

Query :: { ([(String,String)],PVFormula) }
    : query QuantifyList semi Formula { ($2,$4) }
    | query semi Formula { ([],$3) }

QuantifyList :: { [(String,String)] }
    : symU colon symL comma QuantifyList { ($1,$3) : $5 }
    | symU colon symL                    { [($1,$3)] }

Formula :: { PVFormula }
    : Formula longrightarrow Formula { PVImply $1 $3 }
    | Formula and Formula            { PVAnd $1 $3 }
    | Term eq Term                   { PVEq $1 $3 }
    | Term neq Term                  { PVNeq $1 $3 }
    | event lpar symL lpar rpar rpar { PVEvent $3 [] }
    | event lpar symL lpar TermList rpar rpar { PVEvent $3 $5 }
    | injevent lpar symL lpar rpar rpar { PVInjEvent $3 [] }
    | injevent lpar symL lpar TermList rpar rpar { PVInjEvent $3 $5 }
    | attacker lpar Term rpar        { PVAttacker $3 }


StringList :: { [String] }
    : symL comma StringList { $1 : $3 }
    | symL StringList       { $1 : $2 }
    |                       { [] }

StringListComma :: { [String] }
    : symL comma StringListComma { $1 : $3 }
    | symL                      { [$1] }
    |                           { [] }

StringListNonEmpty :: { [String] }
    : symL comma StringListNonEmpty { $1 : $3 }
    | symL                          { [$1] }

StringTuple :: { [String] }
    : symL              { [$1] }
    | lpar StringListComma rpar { $2 }


FunDecl :: { (String,[String],[String]) }
    : symL colon StringTuple rightarrow StringTuple { ($1,$3,$5) }
    | symL colon StringTuple                        { ($1,[],$3) }

FunDeclList :: { ([(String,[String],[String])],[(String,[String],[String])]) }
    : public FunDecl FunDeclList  { Bifunctor.first ($2:) $3 }
    | private FunDecl FunDeclList { Bifunctor.second ($2:) $3 }
    |                             { ([],[]) }

EventDeclList :: { Map.Map String [String] }
    : event symL lpar StringListComma rpar EventDeclList { Map.insert $2 $4 $6 }
    |                                    { Map.empty }


Main :: { ([String], ([(String,[String],[String])],[(String,[String],[String])]), [String], [Agent String String], Map.Map (Agent String String) (Set.Set (Term String String)), Map.Map String [String], [([(String,String)],PVFormula)],InitialChoreo String String) }
    : MainTypes MainFunctions MainCells MainAgents MainKnowledge MainEvents MainQueries MainChoreo { ($1,$2,$3,$4,$5,$6,$7,$8) }

MainTypes :: { [String] }
    : types colon StringList       { $3 }
    |                              { [] }

MainFunctions :: { ([(String,[String],[String])],[(String,[String],[String])]) }
    : functions colon FunDeclList { $3 }
    |                             { ([],[]) }

MainCells :: { [String] }
    : cells colon StringList       { $3 }
    |                              { [] }

MainAgents :: { [Agent String String] }
    : agents colon AgentList       { $3 }
    | agents colon                 { [] } 
    |                              { [] }

MainKnowledge :: { Map.Map (Agent String String) (Set.Set (Term String String)) }
    : knowledge colon Knowledge { $3 }
    |                           { Map.empty }

MainEvents :: { Map.Map String [String] }
    : events colon EventDeclList { $3 }
    |                            { Map.empty }

MainQueries :: { [([(String,String)],PVFormula)] }
    : queries colon Queries { $3 }
    |                       { [] }

MainChoreo :: { InitialChoreo String String }
    : choreo colon Choreo { $3 }


{

pairify :: [Term String String] -> Term String String
pairify [t] = t
pairify (t : ts) = Fun "pair" [t,pairify ts]

parseError :: [Token] -> a
parseError tks = error ("Transaction Parse error at " ++ lcn ++ "\n" )
	where
	lcn = 	case tks of
		  [] -> "end of file"
		  tk:_ -> "line " ++ show l ++ ", column " ++ show c ++ " - Token: " ++ show (token_name tk)
			where
			AlexPn _ l c = token_posn tk
}
