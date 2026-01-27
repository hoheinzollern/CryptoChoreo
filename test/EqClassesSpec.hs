{-# LANGUAGE ScopedTypeVariables #-}
module EqClassesSpec where

import EqClasses
import Test.Hspec
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

spec :: Spec
spec = do
  describe "EqClasses" $ do
    describe "Equivalence Classes" $ do
      describe "emptyEC" $ do
        it "creates empty equivalence class structure" $ do
          let ec = emptyEC :: EqClasses Int
          toList ec `shouldBe` []

      describe "insertECFresh" $ do
        it "inserts element with fresh ID" $ do
          let (id1, ec1) = State.runState (insertECFresh 'a') emptyEC
          id1 `shouldBe` 0
          toList ec1 `shouldBe` ['a']
          
        it "assigns different IDs to different elements" $ do
          let (_, ec) = State.runState (insertECFresh 'a' >> insertECFresh 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` False

      describe "setEq" $ do
        it "sets two fresh elements as equal" $ do
          let (_, ec) = State.runState (setEq 'a' 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` True
          
        it "uses existing ID when first element exists" $ do
          let (_, ec) = State.runState (insertECFresh 'a' >> setEq 'a' 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` True
          
        it "uses existing ID when second element exists" $ do
          let (_, ec) = State.runState (insertECFresh 'b' >> setEq 'a' 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` True

      describe "isEq" $ do
        it "returns False for unrelated elements" $ do
          let ec = State.execState (insertECFresh 'a' >> insertECFresh 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` False
          
        it "returns True for equal elements" $ do
          let ec = State.execState (setEq 'a' 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` True
          
        it "returns False when element not in classes" $ do
          let ec = State.execState (insertECFresh 'a') emptyEC
          isEq ec 'a' 'b' `shouldBe` False

      describe "findEqs" $ do
        it "returns singleton for element not in classes" $ do
          findEqs emptyEC 'a' `shouldBe` Set.singleton 'a'
          
        it "returns all equal elements" $ do
          let ec = State.execState (setEq 'a' 'b' >> setEq 'b' 'c') emptyEC
          findEqs ec 'a' `shouldBe` Set.fromList ['a', 'b', 'c']
          findEqs ec 'b' `shouldBe` Set.fromList ['a', 'b', 'c']
          findEqs ec 'c' `shouldBe` Set.fromList ['a', 'b', 'c']

      describe "setEqModulo" $ do
        it "removes duplicates according to equivalence" $ do
          let ec = State.execState (setEq 'a' 'b' >> setEq 'c' 'd') emptyEC
          let s = Set.fromList ['a', 'b', 'c', 'd', 'e']
          Set.size (setEqModulo ec s) `shouldBe` 3
          
        it "keeps unrelated elements" $ do
          let ec = State.execState (setEq 'a' 'b') emptyEC
          let s = Set.fromList ['a', 'b', 'c', 'd']
          -- Should have one representative from {a,b} plus c and d
          let result = setEqModulo ec s
          Set.size result `shouldBe` 3
          Set.member 'c' result `shouldBe` True
          Set.member 'd' result `shouldBe` True

      describe "toList and toListModulo" $ do
        it "toList returns all elements" $ do
          let ec = State.execState (setEq 'a' 'b' >> insertECFresh 'c') emptyEC
          Set.fromList (toList ec) `shouldBe` Set.fromList ['a', 'b', 'c']
          
        it "toListModulo returns one representative per class" $ do
          let ec = State.execState (setEq 'a' 'b' >> setEq 'c' 'd' >> insertECFresh 'e') emptyEC
          length (toListModulo ec) `shouldBe` 3

      describe "insertECRel" $ do
        it "creates new class when no equivalent element exists" $ do
          let ec = State.execState (insertECRel (==) 'a' >> insertECRel (==) 'b') emptyEC
          isEq ec 'a' 'b' `shouldBe` False
          
        it "joins class when equivalent element exists" $ do
          let relation x y = abs (x - y) <= 1
          let ec = State.execState (insertECRel relation 1 >> insertECRel relation 2) emptyEC
          isEq ec 1 2 `shouldBe` True

    describe "Equivalence Class Maps" $ do
      describe "emptyECMap" $ do
        it "creates empty ECMap" $ do
          let ecm = emptyECMap (==) :: ECMap Char Int
          let values = State.evalState (lookupECMap 'x') ecm
          values `shouldBe` Set.empty

      describe "insertECMap" $ do
        it "inserts single key-value pair" $ do
          let ecm = State.execState (insertECMap 'a' 1) (emptyECMap (==))
          let values = State.evalState (lookupECMap 'a') ecm
          values `shouldBe` Set.singleton 1
          
        it "groups values by equivalence" $ do
          let relation x y = abs (x - y) <= 1
          let ecm = State.execState 
                (insertECMap 1 'a' >> insertECMap 2 'b' >> insertECMap 1 'c')
                (emptyECMap relation)
          let values = State.evalState (lookupECMap 2) ecm
          values `shouldBe` Set.fromList ['a', 'b', 'c']

      describe "lookupECMap" $ do
        it "returns empty set for non-existent key" $ do
          let ecm = emptyECMap (==) :: ECMap Char Int
          let values = State.evalState (lookupECMap 'a') ecm
          values `shouldBe` Set.empty
          
        it "returns all values associated with equivalent keys" $ do
          let ecm = State.execState 
                (insertECMap 'a' 1 >> insertECMap 'a' 2 >> insertECMap 'b' 3)
                (emptyECMap (==))
          let values = State.evalState (lookupECMap 'a') ecm
          values `shouldBe` Set.fromList [1, 2]

    describe "Complex equivalence relations" $ do
      it "works with modulo equivalence" $ do
        let moduloRel x y = x `mod` 3 == y `mod` 3
        let ec = State.execState 
              (insertECRel moduloRel 1 >> insertECRel moduloRel 4 >> insertECRel moduloRel 7)
              emptyEC
        isEq ec 1 4 `shouldBe` True
        isEq ec 4 7 `shouldBe` True
        isEq ec 1 7 `shouldBe` True

      it "maintains transitive equivalence" $ do
        let ec = State.execState (setEq 'a' 'b' >> setEq 'b' 'c' >> setEq 'c' 'd') emptyEC
        isEq ec 'a' 'd' `shouldBe` True
        findEqs ec 'a' `shouldBe` Set.fromList ['a', 'b', 'c', 'd']
