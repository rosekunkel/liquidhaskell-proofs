{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Proofs where

import Prelude hiding ((++), reverse, length)
import Language.Haskell.Liquid.ProofCombinators 
import Types

infixr 5 ++

{-@ infix ++ @-}
{-@ reflect ++ @-}
(++) :: L a -> L a -> L a
Nil ++ ys = ys
(Cons x xs) ++ ys = Cons x (xs ++ ys)

{-@ reflect reverse @-}
reverse :: L a -> L a
reverse Nil = Nil
reverse (Cons x xs) = reverse xs ++ (Cons x Nil)

{-@ reverseSingletonIdentity :: x:a -> {reverse (Cons x Nil) = Cons x Nil}  @-}
reverseSingletonIdentity :: a -> Proof
reverseSingletonIdentity x = trivial

{-@ reflect add @-}
add :: N -> N -> N
add Zero m = m
add (Succ n) m = Succ (add n m)

{-@ addRightIdentityZero :: n:N -> {add n Zero = n} @-}
addRightIdentityZero :: N -> Proof
addRightIdentityZero m = case m of
  Zero -> trivial
  Succ m' -> addRightIdentityZero m'

{-@ addAssociative :: x:N -> y:N -> z:N -> {add x (add y z) = add (add x y) z} @-}
addAssociative :: N -> N -> N -> Proof
addAssociative x y z = case x of
  Zero -> trivial
  Succ x' -> addAssociative x' y z
