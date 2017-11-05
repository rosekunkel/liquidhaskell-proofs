{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Types
  ( L(..), length
  , N(..), value
  , Tree(..), size
  ) where

import Prelude hiding (length)

{-@ data L [length] @-}
data L a = Nil | Cons a (L a)

{-@ measure length @-}
{-@ invariant {v:L a | 0 <= length v} @-}
{-@ length :: L a -> Nat @-}
length :: L a -> Int
length Nil = 0
length (Cons x xs) = 1 + length xs

{-@ data N [value] @-}
data N = Zero | Succ N

{-@ measure value @-}
{-@ invariant {v:N | 0 <= value v} @-}
{-@ value :: N -> Nat @-}
value :: N -> Int
value Zero = 0
value (Succ n) = 1 + value n

{-@ data Tree [size] @-}
data Tree = Leaf Int | Node Tree Tree

{-@ measure size @-}
{-@ invariant {v:Tree | 0 <= size v} @-}
{-@ size :: Tree -> Nat @-}
size :: Tree -> Int
size (Leaf _) = 1
size (Node l r) = 1 + (size l) + (size r)
