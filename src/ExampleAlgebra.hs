{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module ExampleAlgebra where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Term
import Algebraic
import Util
import Topdec

data Func =
  Scrypt | DScrypt | VScrypt |
  Crypt | DCrypt | VCrypt |
  Sign | Open | VSign |
  Pair | Fst | Snd | VPair |
  Inv | Pubk | VInv |
  PK | SK |
  Exp | InvExp | VExp |
  -- XOR | --ZEROS | 
  TT | G |
  Other String
  deriving (Eq, Ord)

instance Show Func where
    show Scrypt = "scrypt"
    show DScrypt = "dscrypt"
    show VScrypt = "vscrypt"
    show Crypt = "crypt"
    show DCrypt = "dcrypt"
    show VCrypt = "vcrypt"
    show Sign = "sign"
    show Open = "open"
    show VSign = "vsign"
    show Inv = "inv"
    show VInv = "vinv"
    show Pubk = "pubk"
    show Pair = "pair"
    show Fst = "fst"
    show Snd = "snd"
    show VPair = "vpair"
    show PK = "pk"
    show SK = "sk"
    show Exp = "exp"
    show InvExp = "invexp"
    show VExp = "vexp"
    -- show XOR = "xor"
    --show ZEROS = "zeros"
    show TT = "true"
    show G = "g"
    show (Other s) = s

-- | Convert a string to an ExampleAlgebra Func.
stringToFunc :: String -> Maybe Func
stringToFunc "scrypt" = Just Scrypt
stringToFunc "dscrypt" = Just DScrypt
stringToFunc "vscrypt" = Just VScrypt
stringToFunc "crypt" = Just Crypt
stringToFunc "dcrypt" = Just DCrypt
stringToFunc "vcrypt" = Just VCrypt
stringToFunc "sign" = Just Sign
stringToFunc "open" = Just Open
stringToFunc "vsign" = Just VSign
stringToFunc "inv" = Just Inv
stringToFunc "vinv" = Just VInv
stringToFunc "pubk" = Just Pubk
stringToFunc "pair" = Just Pair
stringToFunc "p" = Just Pair  -- abbreviation
stringToFunc "fst" = Just Fst
stringToFunc "snd" = Just Snd
stringToFunc "vpair" = Just VPair
stringToFunc "pk" = Just PK
stringToFunc "sk" = Just SK
stringToFunc "exp" = Just Exp
stringToFunc "invexp" = Just InvExp
stringToFunc "vexp" = Just VExp
-- stringToFunc "xor" = Just XOR
stringToFunc "T" = Just TT
stringToFunc "g" = Just G
stringToFunc s
  | all (`elem` "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'") s = Just (Other s)
stringToFunc _ = Nothing


exAlgPublic :: Set (String,Int) -> Func -> Int -> Bool
exAlgPublic otherPubs (Other f) n = (f,n) `Set.member` otherPubs
exAlgPublic _ f n = (f,n) `elem` [
  (Scrypt,2),(DScrypt,2),(VScrypt,2),
  (Crypt,2),(DCrypt,2),(VCrypt,2),
  (Sign,2),(Open,2),(VSign,2),
  (Pair,2),(Fst,1),(Snd,1),
  (Pubk,1),(VInv,1),
  (Exp,2),(InvExp,2),(VExp,2),
  -- (XOR,2),--(ZEROS,0),<
  (TT,0),(G,0)
  ]

exAlgDl :: Map Func (Either Func [Func])
exAlgDl = Map.fromList [
  (Scrypt,Left DScrypt),
  (Crypt,Left DCrypt),
  (Sign,Left Open),
  (Exp,Left InvExp),
  -- (XOR,Left XOR),
  (Pair,Right [Fst,Snd]),
  (Inv,Right [Pubk])]

exAlgVl :: Map Func (Either Func Func)
exAlgVl = Map.fromList [
  (Scrypt,Left VScrypt),
  (Crypt,Left VCrypt),
  (Sign,Left VSign),
  (Exp,Left VExp),
  (Pair,Right VPair),
  (Inv,Right VInv)
  ]

exAlgKr :: Map Func (Term Func v -> Maybe (Term Func v))
exAlgKr = Map.fromList [
  (DCrypt, Just . Fun Inv . (: [])),
  (VCrypt, Just . Fun Inv . (: [])),
  (Open, \case Fun Inv [k] -> Just k; _ -> Nothing),
  (VSign, \case Fun Inv [k] -> Just k; _ -> Nothing),
  (DScrypt, Just),(VScrypt, Just),
  (InvExp, Just),(VExp, Just)
  --, (XOR, Just)
  ]


exAlgTopdec :: Ord v => Func -> Term Func v -> Set [Term Func v]
exAlgTopdec Exp (Fun Exp [t,x]) =
  Set.insert [t,x] ((\case [t',y] -> Set.singleton [Fun Exp [t',x],y]; _ -> Set.empty) =<<< exAlgTopdec Exp t)
-- exAlgTopdec XOR (Fun XOR [Fun XOR [t1,t2], Fun XOR [t3,t4]]) =
--   Set.fromList [
--     [t1,Fun XOR [t2, Fun XOR [t3,t4]]],
--     [t2,Fun XOR [t1, Fun XOR [t3,t4]]],
--     [t3,Fun XOR [t2, Fun XOR [t1,t4]]],
--     [t4,Fun XOR [t2, Fun XOR [t3,t1]]],
--     [Fun XOR [t1,t2], Fun XOR [t3,t4]],
--     [Fun XOR [t1,t3], Fun XOR [t2,t4]],
--     [Fun XOR [t1,t4], Fun XOR [t2,t3]],
--     [Fun XOR [t3,t4], Fun XOR [t1,t2]],
--     [Fun XOR [t2,t4], Fun XOR [t1,t3]],
--     [Fun XOR [t3,t2], Fun XOR [t1,t4]],
--     [Fun XOR [t1,Fun XOR [t2,t3]], t4],
--     [Fun XOR [t1,Fun XOR [t2,t4]], t3],
--     [Fun XOR [t1,Fun XOR [t4,t3]], t2],
--     [Fun XOR [t4,Fun XOR [t2,t3]], t1]
--   ]
-- exAlgTopdec XOR (Fun XOR [t1, Fun XOR [t2,t3]]) =
--   Set.fromList [
--     [t1, Fun XOR [t2,t3]],
--     [t2, Fun XOR [t1,t3]],
--     [t3, Fun XOR [t2,t1]],
--     [Fun XOR [t1,t2],t3],
--     [Fun XOR [t1,t3],t2],
--     [Fun XOR [t3,t2],t1]
--   ]
-- exAlgTopdec XOR (Fun XOR [Fun XOR [t1,t2],t3]) =
--   Set.fromList [
--     [t1, Fun XOR [t2,t3]],
--     [t2, Fun XOR [t1,t3]],
--     [t3, Fun XOR [t2,t1]],
--     [Fun XOR [t1,t2],t3],
--     [Fun XOR [t1,t3],t2],
--     [Fun XOR [t3,t2],t1]
--   ]
-- exAlgTopdec XOR (Fun XOR [t1,t2]) =
--   Set.fromList [
--     [t1,t2],
--     [t2,t1]
--   ]
exAlgTopdec f (Fun g ts)
  | f == g = Set.singleton ts
exAlgTopdec _ _ = Set.empty

exAlgSynonyms :: a -> Set a
exAlgSynonyms = Set.singleton

exAlg :: Set (String,Int) -> Algebra Func
exAlg otherPubs = Algebra exAlgReduces (exAlgPublic otherPubs) exAlgDl exAlgVl exAlgKr exAlgTopdec exAlgSynonyms TT
  where
    exAlgReduces (Fun DScrypt [Fun Scrypt [t, key'], key])
      | aeq (exAlg otherPubs) key key' = Just t
    exAlgReduces (Fun VScrypt [Fun Scrypt [_, key'], key])
      | aeq (exAlg otherPubs) key key' = Just (Fun TT [])
    exAlgReduces (Fun DCrypt [Fun Crypt [t, key'], key])
      | aeq (exAlg otherPubs) key (Fun Inv [key']) = Just t
    exAlgReduces (Fun VCrypt [Fun Crypt [_, key'], key])
      | aeq (exAlg otherPubs) key (Fun Inv [key']) = Just (Fun TT [])
    exAlgReduces (Fun Open [Fun Sign [t, key'], key])
      | aeq (exAlg otherPubs) (Fun Inv [key]) key' = Just t
    exAlgReduces (Fun VSign [Fun Sign [_, key'], key])
      | aeq (exAlg otherPubs) (Fun Inv [key]) key' = Just (Fun TT [])
    exAlgReduces (Fun InvExp [t,x]) =
      findJust (\case [t',y] -> if aeq (exAlg otherPubs) x y then Just t' else Nothing; _ -> Nothing) (topdec (exAlg otherPubs) Exp t)
    exAlgReduces (Fun Exp [t,x]) =
      findJust (\case [t',y] -> if aeq (exAlg otherPubs) x y then Just t' else Nothing; _ -> Nothing) (topdec (exAlg otherPubs) InvExp t)
    exAlgReduces (Fun VExp [t,x]) =
      findJust (\case [_,y] -> if aeq (exAlg otherPubs) x y then Just (Fun TT []) else Nothing; _ -> Nothing) (topdec (exAlg otherPubs) Exp t)
    -- exAlgReduces (Fun XOR [t1,t2]) =
    --   case findJust (\case [t2a,t2b] -> if aeq exAlg t1 t2a then Just t2b else Nothing; _ -> Nothing) (topdec exAlg XOR t2) of 
    --     Just t -> Just t 
    --     Nothing ->
    --       findJust (\case [t1a,t1b] -> if aeq exAlg t1a t2 then Just t1b else Nothing; _ -> Nothing) (topdec exAlg XOR t1)
    exAlgReduces (Fun Fst [Fun Pair [t1, _]]) = Just t1
    exAlgReduces (Fun Snd [Fun Pair [_, t2]]) = Just t2
    exAlgReduces (Fun VPair [Fun Pair [_, _]]) = Just (Fun TT [])
    exAlgReduces (Fun Pubk [Fun Inv [t]]) = Just t
    exAlgReduces (Fun VInv [Fun Inv [_]]) = Just (Fun TT [])
    exAlgReduces _ = Nothing