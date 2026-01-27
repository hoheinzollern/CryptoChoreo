{-# LANGUAGE ScopedTypeVariables #-}
module UtilSpec where

import Util
import Test.Hspec
import Control.Monad.Identity
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

spec :: Spec
spec = do
  describe "Util" $ do
    describe "Set utilities" $ do
      describe "setFromMaybe" $ do
        it "converts Nothing to empty set" $ do
          setFromMaybe (Nothing :: Maybe (Set Int)) `shouldBe` Set.empty
        
        it "converts Just set to the set" $ do
          setFromMaybe (Just (Set.fromList [1,2,3])) `shouldBe` Set.fromList [1,2,3]

      describe "insertMaybe" $ do
        it "inserts into Nothing to create singleton" $ do
          insertMaybe 5 Nothing `shouldBe` Set.singleton 5
        
        it "inserts into existing set" $ do
          insertMaybe 4 (Just (Set.fromList [1,2,3])) `shouldBe` Set.fromList [1,2,3,4]

      describe "(=<<<)" $ do
        it "applies function to empty set" $ do
          (\x -> Set.fromList [x, x*2]) =<<< Set.empty `shouldBe` (Set.empty :: Set Int)
        
        it "applies function and unions results" $ do
          (\x -> Set.fromList [x, x*2]) =<<< Set.fromList [1,2] `shouldBe` Set.fromList [1,2,4]

      describe "($<)" $ do
        it "returns Nothing for empty set" $ do
          (Just . (+1)) $< Set.empty `shouldBe` (Nothing :: Maybe Int)
        
        it "finds first successful result" $ do
          let result = (\x -> if x > 2 then Just x else Nothing) $< Set.fromList [1,2,3,4]
          result `shouldSatisfy` (`elem` [Just 3, Just 4])

    describe "Monad utilities" $ do
      describe "monadSwap" $ do
        it "converts Nothing to monadic Nothing" $ do
          monadSwap (Nothing :: Maybe (Identity Int)) `shouldBe` Identity Nothing
        
        it "converts Just of monadic value to monadic Just" $ do
          monadSwap (Just (Identity 42)) `shouldBe` Identity (Just 42)
        
        it "works with IO monad" $ do
          result <- monadSwap (Just (return "test" :: IO String))
          result `shouldBe` Just "test"
        
        it "works with IO monad and Nothing" $ do
          result <- monadSwap (Nothing :: Maybe (IO String))
          result `shouldBe` Nothing

      describe "ensure" $ do
        it "returns Just when predicate holds" $ do
          ensure (> 5) 10 `shouldBe` Just 10
        
        it "returns Nothing when predicate fails" $ do
          ensure (> 5) 3 `shouldBe` Nothing

      describe "(?<<)" $ do
        it "applies monadic function to Just" $ do
          result <- (\x -> return (x * 2)) ?<< Just 5
          result `shouldBe` Just 10
        
        it "returns Nothing for Nothing input" $ do
          result <- (\x -> return (x * 2 :: Int)) ?<< Nothing
          result `shouldBe` Nothing

      describe "eitherSwap" $ do
        it "converts Left to monadic Left" $ do
          eitherSwap (Left "error" :: Either String (Identity Int)) `shouldBe` Identity (Left "error")
        
        it "converts Right of monadic value to monadic Right" $ do
          eitherSwap (Right (Identity 42) :: Either String (Identity Int)) `shouldBe` Identity (Right 42)
        
        it "works with IO monad" $ do
          result <- eitherSwap (Right (return "test" :: IO String) :: Either String (IO String))
          result `shouldBe` Right "test"
        
        it "works with IO monad and Left" $ do
          result <- eitherSwap (Left "error" :: Either String (IO String))
          result `shouldBe` Left "error"

      describe "rightToMaybe" $ do
        it "converts Right to Just" $ do
          rightToMaybe (Right 42 :: Either String Int) `shouldBe` Just 42
        
        it "converts Left to Nothing" $ do
          rightToMaybe (Left "error" :: Either String Int) `shouldBe` Nothing

      describe "leftToMaybe" $ do
        it "converts Left to Just" $ do
          leftToMaybe (Left "error" :: Either String Int) `shouldBe` Just "error"
        
        it "converts Right to Nothing" $ do
          leftToMaybe (Right 42 :: Either String Int) `shouldBe` Nothing

    describe "List and Matrix utilities" $ do
      describe "extractRow" $ do
        it "extracts from empty matrix" $ do
          extractRow ([] :: [[Int]]) `shouldBe` Just ([], [])
        
        it "extracts first row from matrix" $ do
          extractRow [[1,2,3], [4,5,6], [7,8,9]] `shouldBe` Just ([1,4,7], [[2,3], [5,6], [8,9]])
        
        it "extracts what it can from jagged matrix" $ do
          extractRow [[1,2], [3], [4,5]] `shouldBe` Just ([1,3,4], [[2], [], [5]])
        
        it "handles single element matrix" $ do
          extractRow [[1], [2], [3]] `shouldBe` Just ([1,2,3], [[], [], []])

      describe "fullExtraction" $ do
        it "returns True for empty list" $ do
          fullExtraction ([] :: [[Int]]) `shouldBe` True
        
        it "returns True for list of empty lists" $ do
          fullExtraction [[], [], []] `shouldBe` True
        
        it "returns False for non-empty lists" $ do
          fullExtraction [[1], [2], [3]] `shouldBe` False
        
        it "returns False for mixed empty and non-empty" $ do
          fullExtraction [[], [1], []] `shouldBe` False

      describe "transpose" $ do
        it "returns Nothing for empty matrix" $ do
          transpose ([] :: [[Int]]) `shouldBe` (Nothing :: Maybe [[Int]])
        
        it "transposes square matrix" $ do
          transpose [[1,2], [3,4]] `shouldBe` Just [[1,3], [2,4]]
        
        it "transposes rectangular matrix" $ do
          transpose [[1,2,3], [4,5,6]] `shouldBe` Just [[1,4], [2,5], [3,6]]
        
        it "returns Nothing for jagged matrix" $ do
          transpose [[1,2], [3], [4,5]] `shouldBe` (Nothing :: Maybe [[Int]])
        
        it "handles single row matrix" $ do
          transpose [[1,2,3]] `shouldBe` Just [[1], [2], [3]]
        
        it "handles single column matrix" $ do
          transpose [[1], [2], [3]] `shouldBe` Just [[1,2,3]]

        it "returns Just empty list for list of empty lists" $ do
            transpose [[], [], [] :: [String]] `shouldBe` Just []
        
        it "transposes single row matrix" $ do
            transpose [["a", "b", "c"]] `shouldBe` Just [["a"], ["b"], ["c"]]
        
        it "transposes single column matrix" $ do
            transpose [["a"], ["b"], ["c"]] `shouldBe` Just [["a", "b", "c"]]
        
        it "transposes square matrix" $ do
            transpose [["1", "2"], ["3", "4"]] `shouldBe` Just [["1", "3"], ["2", "4"]]
        
        it "transposes rectangular matrix" $ do
            transpose [["a", "b", "c"], ["d", "e", "f"]] `shouldBe` Just [["a", "d"], ["b", "e"], ["c", "f"]]
        
        it "transposes 3x2 matrix" $ do
            transpose [["1", "2"], ["3", "4"], ["5", "6"]] `shouldBe` Just [["1", "3", "5"], ["2", "4", "6"]]
        
        it "returns Nothing for jagged matrix with different lengths" $ do
            transpose [["a", "b"], ["c"]] `shouldBe` Nothing
        
        it "returns Nothing for matrix with missing elements" $ do
            transpose [["a", "b", "c"], ["d"], ["e", "f", "g"]] `shouldBe` Nothing
        
        it "returns Nothing when some rows are longer than others" $ do
            transpose [["1", "2"], ["3", "4", "5"]] `shouldBe` Nothing
        
        it "handles single element matrix" $ do
            transpose [["x"]] `shouldBe` Just [["x"]]
        
        it "handles mix of empty and non-empty rows correctly" $ do
            transpose [["a"], []] `shouldBe` Nothing
        
        it "transposes larger rectangular matrix" $ do
            let input = [["1", "2", "3"], ["4", "5", "6"], ["7", "8", "9"], ["10", "11", "12"]]
            let expected = [["1", "4", "7", "10"], ["2", "5", "8", "11"], ["3", "6", "9", "12"]]
            transpose input `shouldBe` Just expected

    describe "Either utilities" $ do
      describe "combineLeft" $ do
        it "combines two Right values" $ do
          combineLeft (+) (Right 3) (Right 4) `shouldBe` (Right 7 :: Either String Int)
        
        it "preserves Left from first argument" $ do
          combineLeft (+) (Left "error1") (Right 4) `shouldBe` (Left "error1" :: Either String Int)
        
        it "preserves Left from second argument" $ do
          combineLeft (+) (Right 3) (Left "error2") `shouldBe` (Left "error2" :: Either String Int)
        
        it "combines two Left values using Semigroup" $ do
          combineLeft (+) (Left "error1") (Left "error2") `shouldBe` (Left "error1error2" :: Either String Int)

      describe "collectEither" $ do
        it "collects all Right values" $ do
          collectEither [Right 1, Right 2, Right 3] `shouldBe` (Right [1,2,3] :: Either String [Int])
        
        it "returns first Left value when present" $ do
          collectEither [Right 1, Left "error", Right 3] `shouldBe` (Left "error" :: Either String [Int])
        
        it "combines multiple Left values" $ do
          collectEither [Left "error1", Left "error2", Right 3] `shouldBe` (Left "error1error2" :: Either String [Int])
        
        it "handles empty list" $ do
          collectEither ([] :: [Either String Int]) `shouldBe` Right []

      describe "successList" $ do
        it "returns Just for all Right values" $ do
          successList [Right 1, Right 2, Right 3] `shouldBe` Just [1,2,3]
        
        it "returns Nothing when any Left present" $ do
          successList [Right 1, Left "error", Right 3] `shouldBe` (Nothing :: Maybe [Int])
        
        it "handles empty list" $ do
          successList ([] :: [Either String Int]) `shouldBe` Just []

      describe "partitionMaybe" $ do
        it "partitions based on Just True/False" $ do
          let f x = if x `mod` 2 == 0 then Just True else Just False
          partitionMaybe f [1,2,3,4] `shouldBe` Right ([2,4], [1,3])
        
        it "returns Left for first Nothing result" $ do
          let f x = if x == 2 then Nothing else Just (x > 3)
          partitionMaybe f [1,2,3,4] `shouldBe` Left 2
        
        it "handles empty list" $ do
          let f _ = Just True
          partitionMaybe f ([] :: [Int]) `shouldBe` Right ([], [])

      describe "combineMaybe" $ do
        it "applies function to Right value" $ do
          combineMaybe (Just (+ 1)) (Right 5 :: Either String Int) `shouldBe` (Right (Right 6) :: Either String (Either String Int))
        
        it "preserves Left value regardless of function" $ do
          combineMaybe (Just (+ 1)) (Left "error" :: Either String Int) `shouldBe` (Right (Left "error") :: Either String (Either String Int))
          combineMaybe Nothing (Left "error" :: Either String Int) `shouldBe` (Right (Left "error") :: Either String (Either String Int))
        
        it "returns error for Nothing function with Right value" $ do
          combineMaybe Nothing (Right 5 :: Either String Int) `shouldBe` (Left "combineMaybe fail - function to apply was nothing" :: Either String (Either String Int))

      describe "fmapl" $ do
        it "applies function to Left" $ do
          fmapl (+1) (Left 5 :: Either Int String) `shouldBe` Left 6
        
        it "preserves Right" $ do
          fmapl (+1) (Right "test" :: Either Int String) `shouldBe` Right "test"

    describe "General utilities" $ do
      describe "(+>)" $ do
        it "executes state and returns final state" $ do
          (State.modify (+1) +> 5) `shouldBe` 6
        
        it "chains state modifications" $ do
          ((State.modify (*2) >> State.modify (+10)) +> 5) `shouldBe` 20

      describe "insertSetMap" $ do
        it "creates singleton set for new key" $ do
          insertSetMap 'a' 1 Map.empty `shouldBe` Map.singleton 'a' (Set.singleton 1)
        
        it "inserts into existing set" $ do
          let m = Map.singleton 'a' (Set.fromList [1,2])
          insertSetMap 'a' 3 m `shouldBe` Map.singleton 'a' (Set.fromList [1,2,3])

    describe "Search utilities" $ do
      describe "findJust" $ do
        it "finds first Just result" $ do
          findJust (\x -> if x > 3 then Just x else Nothing) [1,2,3,4,5] `shouldBe` Just 4
        
        it "returns Nothing if no Just found" $ do
          findJust (\x -> if x > 10 then Just x else Nothing) [1,2,3] `shouldBe` (Nothing :: Maybe Int)

      describe "anyM" $ do
        it "returns True if any element satisfies predicate" $ do
          result <- anyM (\x -> return (x > 3)) [1,2,3,4,5]
          result `shouldBe` True
        
        it "returns False if no element satisfies predicate" $ do
          result <- anyM (\x -> return (x > 10)) [1,2,3]
          result `shouldBe` False

    describe "State utilities" $ do
      describe "smap" $ do
        it "maps state computation to different state type" $ do
          let computation = State.modify (+1) >> State.get
          let mapped = smap fst (\(_,b) a -> (a,b)) computation
          State.runState mapped (5, "test") `shouldBe` (6, (6, "test"))

      describe "smapFst" $ do
        it "maps computation to first component" $ do
          let computation = State.modify (+1) >> State.get
          State.runState (smapFst computation) (5, "test") `shouldBe` (6, (6, "test"))

      describe "smapSnd" $ do
        it "maps computation to second component" $ do
          let computation = State.modify (+1) >> State.get
          State.runState (smapSnd computation) ("test", 5) `shouldBe` (6, ("test", 6))

      describe "executeIf" $ do
        it "executes computation when condition is true" $ do
          State.runState (executeIf (>3) (State.modify (+10) >> return 15) 0) 5 `shouldBe` (15, 15)
        
        it "returns default when condition is false" $ do
          State.runState (executeIf (>10) (State.modify (+10) >> return 100) 0) 5 `shouldBe` (0, 5)

      describe "(>.>)" $ do
        it "chains state computations keeping second result" $ do
          let s1 = State.modify (+1) >> return "first"
          let s2 = State.modify (*2) >> return "second"
          State.runState (s1 >.> s2) 5 `shouldBe` ("second", 12)

    describe "crossSets" $ do
        it "combines empty sets to empty set" $ do
            crossSets (+) Set.empty (Set.fromList [1, 2]) `shouldBe` Set.empty
            crossSets (+) (Set.fromList [1, 2]) Set.empty `shouldBe` Set.empty

        it "applies function to all combinations" $ do
            crossSets (+) (Set.fromList [1, 2]) (Set.fromList [10, 20]) 
                `shouldBe` Set.fromList [11, 21, 12, 22]

        it "works with single element sets" $ do
            crossSets (*) (Set.singleton 3) (Set.singleton 4) 
                `shouldBe` Set.singleton 12

    describe "expandSetList" $ do
        it "returns singleton empty list for empty input" $ do
            expandSetList ([] :: [Set Int]) `shouldBe` Set.singleton []

        it "expands single set to singleton lists" $ do
            expandSetList [Set.fromList [1, 2]] 
                `shouldBe` Set.fromList [[1], [2]]

        it "expands multiple sets to all combinations" $ do
            expandSetList [Set.fromList ['1', '2'], Set.fromList ['a', 'b']] 
                `shouldBe` Set.fromList [['1', 'a'], ['1', 'b'], ['2', 'a'], ['2', 'b']]

        it "handles empty sets in list" $ do
            expandSetList [Set.fromList [1, 2], Set.empty] 
                `shouldBe` Set.empty

