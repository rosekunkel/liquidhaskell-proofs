{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Data.List.Verified
  ( List(..)
  , (++)
  , length
  ) where

import Prelude hiding ((++), length)

{-@ infixr 5 ::: @-}
infixr 5 :::
{-@ infixr 5 ++ @-}
infixr 5 ++

{-@ data List [length] @-}
data List a = Nil | a:::(List a)

{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
Nil ++ ys = ys
(x:::xs) ++ ys = x:::xs ++ ys

{-@ measure length @-}
{-@ invariant {v:List a | 0 <= length v} @-}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil = 0
length (x:::xs) = 1 + length xs
