module TermSpec where
import Term 
import Choreo
import Local
import Test.Hspec

import Data.Set (Set)
import qualified Data.Set as Set

{- Testing Term -}



t1 = Fun "f" [Var "x", Fun "g" [Var "y"]]
t2 = Fun "f" [Var "x", Fun "g" [Var "y",Var "x"]]

spec :: Spec
spec = do
    describe "Term" $ do
        describe "fvt" $ do
            it "should compute free variables in terms" $ do
                fvt t1 `shouldBe` Set.fromList ["x","y"]
                fvt t2 `shouldBe` Set.fromList ["x","y"]

{-Testing ExampleAlgebra-}