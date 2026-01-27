module AlgebraicSpec where

import Algebraic
import ExampleAlgebra
import Term
import Frame (Frame)
import qualified Frame
import Test.Hspec
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Data.Maybe (listToMaybe, isJust)

spec :: Spec
spec = do
  describe "Algebraic" $ do
    it "TODO" $ do 
      True `shouldBe` True