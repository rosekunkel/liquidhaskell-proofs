{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Flatten where

import Prelude hiding (flatten, length, (++))
import Language.Haskell.Liquid.ProofCombinators
import Types hiding (L(..), length)
import Data.List.Verified

flatten :: Tree -> List Int
flatten (Leaf n) = n:::Nil
flatten (Node l r) = flatten l ++ flatten r
