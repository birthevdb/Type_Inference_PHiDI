{-# LANGUAGE DeriveGeneric,
             UndecidableInstances #-}


module SEDEL.Fix where

import           GHC.Generics (Generic)

-- fix
data Fix f = In {out :: f (Fix f)} deriving (Generic)

cata :: (Functor f) => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . out

--------------------------------------------------------------------------------

instance (Eq (f (Fix f))) => Eq (Fix f) where
  (In x) == (In y) = x == y

instance Show (f (Fix f)) => Show (Fix f) where
  show (In x) = show x
