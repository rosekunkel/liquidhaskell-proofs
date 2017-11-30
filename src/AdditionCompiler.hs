{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module AdditionCompiler where

import Prelude hiding ((++), length, reverse)
import Language.Haskell.Liquid.ProofCombinators
import Data.List.Verified

{-@ data Expr [addCount] @-}
data Expr = Val Int | Add Expr Expr

{-@ measure addCount @-}
{-@ invariant {v:Expr | 0 <= addCount v} @-}
{-@ addCount :: Expr -> Nat @-}
addCount :: Expr -> Int
addCount (Val _) = 0
addCount (Add x y) = 1 + (addCount x) + (addCount y)

{-@ reflect eval @-}
eval :: Expr -> Int
eval (Val n) = n
eval (Add x y) = eval x + eval y

-- Unfortunately the proofs break when I use Stack instead of List
-- Int; I'm not sure why.
type Stack = List Int

data Op = PUSH Int | ADD

type Code = List Op

{-@ reflect exec @-}
exec :: Code -> List Int -> List Int
exec Nil s = s
exec (PUSH n:::c) s = exec c (n:::s)
exec (ADD:::c) (m:::n:::s) = exec c (n + m:::s)
exec (ADD:::c) s = exec c s

{-@ reflect comp @-}
comp :: Expr -> Code
comp (Val n) = PUSH n:::Nil
comp (Add x y) = comp x ++ comp y ++ (ADD:::Nil)

{-@ reflect comp' @-}
comp' :: Expr -> Code -> Code
comp' (Val n) c = PUSH n ::: c
comp' (Add x y) c = comp' x (comp' y (ADD ::: c))

{-@ infixr 5 ::: @-}
{-@ infixr 5 ++ @-}

{-@ execAppendDist :: x:_ -> y:_ -> s:_ -> { exec (x ++ y) s = exec y (exec x s) } @-}
execAppendDist :: Code -> Code -> List Int -> Proof
execAppendDist x y s = case x of
  Nil -> trivial
  PUSH n:::x' ->
    exec (x ++ y) s
    ==. exec ((PUSH n:::x') ++ y) s
    ==. exec (x' ++ y) (n:::s)
    ==. exec y (exec x' (n:::s)) ? execAppendDist x' y (n:::s)
    ==. exec y (exec (PUSH n:::x') s)
    ==. exec y (exec x s)
    *** QED
  ADD:::x' -> case s of
    m:::n:::s' ->
      exec (x ++ y) s
      ==. exec ((ADD:::x') ++ y) (m:::n:::s')
      ==. exec (ADD:::(x' ++ y)) (m:::n:::s')
      ==. exec (x' ++ y) (n + m:::s')
      ==. exec y (exec x' (n + m:::s')) ? execAppendDist x' y (n + m:::s')
      ==. exec y (exec (ADD:::x') (m:::n:::s'))
      ==. exec y (exec x s)
      *** QED
    s ->
      exec (x ++ y) s
      ==. exec ((ADD:::x') ++ y) s
      ==. exec (ADD:::(x' ++ y)) s
      ==. exec (x' ++ y) s
      ==. exec y (exec x' s) ? execAppendDist x' y s
      ==. exec y (exec (ADD:::x') s)
      ==. exec y (exec x s)
      *** QED

{-@ compCorrectAnyStack :: e:Expr -> s:(List Int) -> { exec (comp e) s = eval e:::s } @-}
compCorrectAnyStack :: Expr -> List Int -> Proof
compCorrectAnyStack e s = case e of
  Val n -> trivial
  Add x y ->
    exec (comp e) s
    ==. exec (comp (Add x y)) s
    ==. exec (comp x ++ comp y ++ (ADD:::Nil)) s
    ==. exec (comp y ++ (ADD:::Nil)) (exec (comp x) s) ? execAppendDist (comp x) (comp y ++ (ADD:::Nil)) s
    ==. exec (ADD:::Nil) (exec (comp y) (exec (comp x) s)) ? execAppendDist (comp y) (ADD:::Nil) (exec (comp x) s)
    ==. exec (ADD:::Nil) (exec (comp y) (eval x:::s)) ? compCorrectAnyStack x s
    ==. exec (ADD:::Nil) (eval y:::eval x:::s) ? compCorrectAnyStack y (eval x:::s)
    ==. eval x + eval y:::s
    ==. eval (Add x y):::s
    ==. eval e:::s
    *** QED

{-@ comp'Correct :: e:Expr -> c:Code -> s:(List Int) -> { exec (comp' e c) s = exec c (eval e:::s) } @-}
comp'Correct :: Expr -> Code -> List Int -> Proof
comp'Correct e c s = case e of
  Val n -> trivial
  Add x y ->
    exec (comp' (Add x y) c) s
    ==. exec (comp' x (comp' y (ADD:::c))) s
    ==. exec (comp' y (ADD:::c)) (eval x:::s) ? comp'Correct x (comp' y (ADD:::c)) s
    ==. exec (ADD:::c) (eval y:::eval x:::s) ? comp'Correct y (ADD:::c) (eval x:::s)
    ==. exec c (eval x+eval y:::s)
    ==. exec c (eval (Add x y):::s)
    *** QED
