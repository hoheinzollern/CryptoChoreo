{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module TranslateSpec where 
import Translate
import TranslateState
import Choreo 
import Local
import Term
import Frame (Frame)
import qualified Frame
import ExampleAlgebra
import Util
import Test.Hspec

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map) 
import qualified Data.Map as Map
import Control.Monad.Trans.State (State)
import Control.Monad.Trans.State as State 
import qualified Data.List as List
import qualified Data.Maybe as Maybe


spec :: Spec
spec = do
    describe "TranslateState Functions" $ do
        it "TODO" $ do 
            True `shouldBe` True