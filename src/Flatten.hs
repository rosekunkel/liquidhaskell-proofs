{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Flatten where

import Prelude hiding (flatten, length, (++))
import Language.Haskell.Liquid.ProofCombinators
import Types hiding (L(..), length)
import Data.List.Verified

{-@ infixr 5 ++ @-}

{-@ reflect flatten @-}
flatten :: Tree -> List Int
flatten (Leaf n) = n:::Nil
flatten (Node l r) = flatten l ++ flatten r

{-@ reflect flatten' @-}
flatten' :: Tree -> List Int -> List Int
flatten' (Leaf n) ns = n:::ns
flatten' (Node l r) ns = flatten' l (flatten' r ns)

{-@ reflect flatten'' @-}
flatten'' :: Tree -> List Int
flatten'' t = flatten' t Nil

{-@ flatten'Appends :: t:Tree -> ns:List Int -> { flatten' t ns = flatten t ++ ns } @-}
flatten'Appends :: Tree -> List Int -> Proof
flatten'Appends t ns = case t of
  Leaf _ -> trivial
  Node l r ->
    flatten' t ns
    ==. flatten' l (flatten' r ns)
    ==. flatten' l (flatten r ++ ns) ? flatten'Appends r ns
    ==. flatten l ++ (flatten r ++ ns) ? flatten'Appends l (flatten r ++ ns)
    ==. (flatten l ++ flatten r) ++ ns ? appendAssoc (flatten l) (flatten r) ns
    ==. flatten t ++ ns
    *** QED

{-@ flatten''Correct :: t:Tree -> { flatten'' t = flatten t } @-}
flatten''Correct :: Tree -> Proof
flatten''Correct t =
  flatten'' t
  ==. flatten' t Nil
  ==. flatten t ++ Nil ? flatten'Appends t Nil
  ==. flatten t ? appendRightId (flatten t)
  *** QED
