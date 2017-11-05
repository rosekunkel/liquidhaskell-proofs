{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module ReverseEfficient where

import Prelude hiding ((++), reverse, length, foldl, flip)
import Language.Haskell.Liquid.ProofCombinators 
import Types
import Data.List.Verified

{-@ infixr 5 ::: @-}
{-@ infixr 5 ++ @-}

{-@ reflect reverse' @-}
reverse' :: List a -> List a -> List a
reverse' Nil ys = ys
reverse' (x:::xs) ys = reverse' xs (x:::ys)

{-@ reverse'Correct :: xs:List a -> { reverse xs = reverse' xs Nil } @-}
reverse'Correct :: List a -> Proof
reverse'Correct xs =
  reverse xs
  ==. reverse xs ++ Nil ? appendRightId (reverse xs)
  ==. reverse' xs Nil ? reverse'Correct' xs Nil
  *** QED

{-@ reverse'Correct' :: xs:List a -> ys:List a -> { reverse' xs ys = reverse xs ++ ys } @-}
reverse'Correct' :: List a -> List a -> Proof
reverse'Correct' xs ys = case xs of
  Nil ->
    reverse' Nil ys
    ==. ys
    ==. Nil ++ ys
    ==. reverse Nil ++ ys
    *** QED
  x:::xs' ->
    reverse' (x:::xs') ys
    ==. reverse' xs' (x:::ys)
    ==. reverse xs' ++ (x:::ys) ? reverse'Correct' xs' (x:::ys)
    ==. reverse xs' ++ (x:::Nil ++ ys)
    ==. (reverse xs' ++ x:::Nil) ++ ys ? appendAssoc (reverse xs') (x:::Nil) ys
    ==. reverse (x:::xs') ++ ys
    *** QED

{-@ reflect foldl @-}
foldl :: (a -> b -> a) -> a -> List b -> a
foldl f c Nil = c
foldl f c (x:::xs) = foldl f (f c x) xs

{-@ reflect flip @-}
flip :: (a -> b -> c) -> (b -> a -> c)
flip f a b = f b a

{-@ reflect listCons @-}
listCons :: a -> List a -> List a
listCons x xs = x:::xs

{-@ reverseFoldCorrect :: xs:List a -> { reverse xs = foldl (flip listCons) Nil xs } @-}
reverseFoldCorrect :: List a -> Proof
reverseFoldCorrect xs =
  reverse xs
  ==. reverse' xs Nil ? reverse'Correct xs
  ==. foldl (flip listCons) Nil xs ? reverseFoldCorrect' Nil xs
  *** QED

{-@ reverseFoldCorrect' :: xs:List a -> ys:List a -> { foldl (flip listCons) xs ys = reverse' ys xs } / [length ys] @-}
reverseFoldCorrect' :: List a -> List a -> Proof
reverseFoldCorrect' xs ys = case ys of
  Nil ->
    foldl (flip listCons) xs Nil
    ==. xs
    ==. reverse' Nil xs
    *** QED
  y:::ys' ->
    foldl (flip listCons) xs (y:::ys')
    ==. foldl (flip listCons) ((flip listCons) xs y) ys'
    ==. foldl (flip listCons) (listCons y xs) ys'
    ==. foldl (flip listCons) (y:::xs) ys'
    ==. reverse' ys' (y:::xs) ? reverseFoldCorrect' (y:::xs) ys'
    ==. reverse' (y:::ys') xs
    *** QED
