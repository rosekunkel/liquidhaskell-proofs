{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Flatten where

import Prelude hiding (flatten, length)
import Language.Haskell.Liquid.ProofCombinators
import Types
