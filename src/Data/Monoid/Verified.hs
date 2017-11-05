{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Data.Monoid.Verified where

import Prelude hiding (Monoid(..), (++), length)
import Language.Haskell.Liquid.ProofCombinators
import Data.List.Verified

{-@
  class Monoid a where
    mempty :: a
    mappend :: a -> a -> a

    memptyLeftId :: x:a -> { mappend mempty x = x }
    memptyRightId :: x:a -> { mappend x mempty = x }
    mappendAssoc :: x:a -> y:a -> z:a -> { mappend x (mappend y z) = mappend (mappend x y) z }
@-}
class Monoid a where
  mempty  :: a
  mappend :: a -> a -> a

  memptyLeftId :: a -> Proof
  memptyRightId :: a -> Proof
  mappendAssoc :: a -> a -> a -> Proof

-- Turns out we can't reflect instances, so we can't actually prove
-- any of these theorems, and even if we could, they wouldn't be
-- useful unless we specifically use `mappend` instead of ++.
instance Monoid (List a) where
  mempty = Nil
  mappend xs ys = xs ++ ys

  memptyLeftId xs = undefined
  memptyRightId xs = undefined
  mappendAssoc xs ys zs = undefined
