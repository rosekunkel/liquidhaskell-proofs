module Types (List(..), Nat(..)) where

data List a = Nil | Cons a (List a)

data Nat = Zero | Succ Nat
