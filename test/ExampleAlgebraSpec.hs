module ExampleAlgebraSpec where 
import ExampleAlgebra
import Term
import Algebraic
import Test.Hspec

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

spec :: Spec
spec = do
    describe "ExampleAlgebra" $ do
        it "TODO" $ do 
            True `shouldBe` True