{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Replicate where

import Prelude hiding (replicate, length)
import Language.Haskell.Liquid.ProofCombinators
import Types

{-@ replicate :: Nat -> a -> L a @-}
replicate :: Int -> a -> L a
replicate 0 _ = Nil
replicate n x = Cons x (replicate (n - 1) x)
