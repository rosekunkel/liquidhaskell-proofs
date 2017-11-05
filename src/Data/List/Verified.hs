{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Data.List.Verified
  ( List(..)
  , (++)
  , reverse
  , length
  , appendRightId
  , appendAssoc
  ) where

import Prelude hiding ((++), length, reverse)
import Language.Haskell.Liquid.ProofCombinators

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

{-@ reflect reverse @-}
reverse :: List a -> List a
reverse Nil = Nil
reverse (x:::xs) = reverse xs ++ (x:::Nil)

{-@ measure length @-}
{-@ invariant {v:List a | 0 <= length v} @-}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil = 0
length (x:::xs) = 1 + length xs

{-@ appendRightId :: xs:List a -> { xs ++ Nil = xs } @-}
appendRightId :: List a -> Proof
appendRightId xs = case xs of
  Nil -> trivial
  x:::xs' -> appendRightId xs'

{-@ appendAssoc :: xs:List a -> ys:List a -> zs:List a -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc xs ys zs = case xs of
  Nil -> trivial
  x:::xs' ->
    ((x:::xs') ++ ys) ++ zs
    ==. (x:::(xs' ++ ys)) ++ zs
    ==. x:::((xs' ++ ys) ++ zs)
    ==. x:::(xs' ++ (ys ++ zs)) ? appendAssoc xs' ys zs
    ==. (x:::xs') ++ (ys ++ zs)
    *** QED
