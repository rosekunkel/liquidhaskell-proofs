{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Exercises where

import Prelude hiding ((++), reverse, length, all, replicate, map, take, drop)
import Language.Haskell.Liquid.ProofCombinators
import Data.List.Verified
import Types

{-@ infixr 5 ::: @-}
{-@ infixr 5 ++ @-}

{-@ reflect add @-}
add :: N -> N -> N
add Zero m = m
add (Succ n) m = Succ (add n m)

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> (a -> c)
compose f g x = f (g x)

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (x:::xs) = (f x):::(map f xs)

{-@ reflect take @-}
{-@ take :: {v:Int | v >= 0} -> List a -> List a @-}
take :: Int -> List a -> List a
take n Nil = Nil
take n (x:::xs) = if n == 0 then Nil else x:::take (n-1) xs

{-@ reflect drop @-}
{-@ drop :: {v:Int | v >= 0} -> List a -> List a @-}
drop :: Int -> List a -> List a
drop n Nil = Nil
drop n (x:::xs) = if n == 0 then (x:::xs) else drop (n-1) xs

{-@ reflect numInodes @-}
numInodes :: Tree -> Int
numInodes (Leaf _) = 0
numInodes (Node l r) = 1 + (numInodes l) + (numInodes r)

{-@ reflect numLeaves @-}
numLeaves :: Tree -> Int
numLeaves (Leaf _) = 1
numLeaves (Node l r) = (numLeaves l) + (numLeaves r)

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

{-@ reverseSingle :: xs:_ -> x:_ -> { reverse (xs ++ (x:::Nil)) = x:::reverse xs } @-}
reverseSingle :: List a -> a -> Proof
reverseSingle xs x = case xs of
  Nil -> trivial
  x':::xs' -> reverseSingle xs' x

{-@ mapCompose :: f:_ -> g:_ -> xs:_ -> { map f (map g xs) = map (compose f g) xs } @-}
mapCompose :: (b -> c) -> (a -> b) -> List a -> Proof
mapCompose f g xs = case xs of
  Nil -> trivial
  x:::xs' -> mapCompose f g xs'

{-@ takeDrop :: n:{v:Int | v >= 0} -> xs:_ -> { take n xs ++ drop n xs = xs } @-}
takeDrop :: Int -> List a -> Proof
takeDrop n xs = case xs of
  Nil -> trivial
  x:::xs' -> if n == 0 then trivial else takeDrop (n-1) xs'

{-@ leavesVsInodes :: t:Tree -> { numLeaves t = numInodes t + 1 } @-}
leavesVsInodes :: Tree -> Proof
leavesVsInodes t = case t of
  Leaf _ -> trivial
  Node l r -> leavesVsInodes l &&& leavesVsInodes r
