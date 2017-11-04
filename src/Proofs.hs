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

{-@ appendRightIdentityNil :: xs:L a -> { xs ++ Nil = xs } @-}
appendRightIdentityNil :: L a -> Proof
appendRightIdentityNil xs = case xs of
  Nil -> trivial
  Cons x xs' -> appendRightIdentityNil xs'

{-@ appendAssoc :: xs:L a -> ys:L a -> zs:L a -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
appendAssoc :: L a -> L a -> L a -> Proof
appendAssoc xs ys zs = case xs of
  Nil -> trivial
  Cons x xs' ->
    ((Cons x xs') ++ ys) ++ zs
    ==. (Cons x (xs' ++ ys)) ++ zs
    ==. Cons x ((xs' ++ ys) ++ zs)
    ==. Cons x (xs' ++ (ys ++ zs)) ? appendAssoc xs' ys zs
    ==. (Cons x xs') ++ (ys ++ zs)
    *** QED

{-@ reverseAppendFlip :: xs:L a -> ys:L a -> { reverse (xs ++ ys) = reverse ys ++ reverse xs } @-}
reverseAppendFlip :: L a -> L a -> Proof
reverseAppendFlip xs ys = case xs of
  Nil ->
    reverse (Nil ++ ys)
    ==. reverse ys
    ==. reverse ys ++ Nil ? appendRightIdentityNil (reverse ys)
    ==. reverse ys ++ reverse Nil
    *** QED
  Cons x xs' ->
    reverse ((Cons x xs') ++ ys)
    ==. reverse (Cons x (xs' ++ ys))
    ==. reverse (xs' ++ ys) ++ (Cons x Nil)
    ==. (reverse ys ++ reverse xs') ++ (Cons x Nil) ? reverseAppendFlip xs' ys
    ==. reverse ys ++ (reverse xs' ++ (Cons x Nil)) ? appendAssoc (reverse ys) (reverse xs') (Cons x Nil)
    ==. reverse ys ++ reverse (Cons x xs')
    *** QED

{-@ reverseOwnInverse :: xs:L a -> { v:() | reverse (reverse xs) = xs } @-}
reverseOwnInverse :: L a -> Proof
reverseOwnInverse xs = case xs of
  Nil -> trivial
  Cons x xs' ->
    reverse (reverse (Cons x xs'))
    ==. reverse (reverse xs' ++ (Cons x Nil))
    ==. reverse (Cons x Nil) ++ reverse (reverse xs') ? reverseAppendFlip (reverse xs') (Cons x Nil)
    ==. (Cons x Nil) ++ xs' ? reverseOwnInverse xs'
    ==. Cons x xs'
    *** QED
