{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Exercises where

import Prelude hiding ((++), reverse, length, all, replicate)
import Language.Haskell.Liquid.ProofCombinators
import Data.List.Verified
import Types

{-@ infixr 5 ::: @-}
{-@ infixr 5 ++ @-}

{-@ reflect add @-}
add :: N -> N -> N
add Zero m = m
add (Succ n) m = Succ (add n m)

{-@ addSuccR :: n:_ -> m:_ -> { add n (Succ m) = Succ (add n m) } @-}
addSuccR :: N -> N -> Proof
addSuccR n m = case n of
  Zero -> trivial
  Succ n' ->
    add n (Succ m)
    ==. Succ (add n' (Succ m))
    ==. Succ (Succ (add n' m)) ? addSuccR n' m
    ==. Succ (add n m)
    *** QED


{-@ addRightIdentityZero :: n:N -> {add n Zero = n} @-}
addRightIdentityZero :: N -> Proof
addRightIdentityZero m = case m of
  Zero -> trivial
  Succ m' -> addRightIdentityZero m'

{-@ addComm :: n:_ -> m:_ -> { add n m = add m n } @-}
addComm :: N -> N -> Proof
addComm n m = case n of
  Zero ->
    add Zero m
    ==. m
    ==. add m Zero ? addRightIdentityZero m
    *** QED
  Succ n' ->
    add (Succ n') m
    ==. Succ (add n' m)
    ==. Succ (add m n') ? addComm n' m
    ==. add m (Succ n') ? addSuccR m n'
    *** QED

{-@ reflect eqb @-}
eqb :: N -> N -> Bool
eqb Zero Zero = True
eqb (Succ n) (Succ m) = eqb n m
eqb _  _ = False

{-@ reflect all @-}
all :: (a -> Bool) -> List a -> Bool
all p Nil = True
all p (x:::xs) = p x && all p xs

{-@ reflect replicate @-}
{-@ replicate :: Nat -> a -> List a @-}
replicate :: Int -> a -> List a
replicate n x
  | n == 0 = Nil
  | otherwise = x:::(replicate (n - 1) x)

{-@ eqbRefl :: x:_ -> { eqb x x = True } @-}
eqbRefl :: N -> Proof
eqbRefl x = case x of
  Zero -> trivial
  Succ n -> eqbRefl n

{-@ replicateAllEqual :: n:Nat -> x:_ -> { all (eqb x) (replicate n x) = True } @-}
replicateAllEqual :: Int -> N -> Proof
replicateAllEqual n x = case n of
  0 -> trivial
  n ->
    all (eqb x) (replicate n x)
    ==. all (eqb x) (x:::replicate (n - 1) x)
    ==. (eqb x x && all (eqb x) (replicate (n - 1) x))
    ==. (eqb x x && True) ? replicateAllEqual (n - 1) x
    ==. (True && True) ? eqbRefl x
    ==. True
    *** QED

{-@ appNilR :: xs:_ -> { xs ++ Nil = xs } @-}
appNilR :: List a -> Proof
appNilR xs = case xs of
  Nil -> trivial
  x:::xs' ->
    (x:::xs') ++ Nil
    ==. x:::(xs' ++ Nil)
    ==. x:::xs' ? appNilR xs'
    *** QED

{-@ appAssoc :: xs:_ -> ys:_ -> zs:_ -> { xs ++ (ys ++ zs) = (xs ++ ys) ++ zs } @-}
appAssoc :: List a -> List a -> List a -> Proof
appAssoc xs ys zs = case xs of
  Nil -> trivial
  x:::xs' ->
    (x:::xs') ++ (ys ++ zs)
    ==. x:::(xs' ++ (ys ++ zs))
    ==. x:::((xs' ++ ys) ++ zs) ? appAssoc xs' ys zs
    ==. (x:::(xs' ++ ys)) ++ zs
    ==. ((x:::xs') ++ ys) ++ zs
    *** QED
