{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Syntax where

-- import           Data.List
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.TH

-----------
-- TYPES --
-----------

data Type = Nat             -- Int
          | Bool            -- Bool
          | Bot             -- ⊥
          | Top             -- ⊤
          | Arr Type Type   -- t1 -> t2
          | And Type Type   -- t1 & t2
          | Rec Label Type  -- {l : t}
          | Var TyName      -- α
          | Uni TUni        -- u
          deriving (Show, Eq)

type TyName = Name Type
type TUni = Name Type
type Label = String

------------
-- QUEUES --
------------

-- | Queue consisting of labels and/or types
data Queue = EmptyQ
           | QL Label Queue
           | QA Type Queue
           deriving (Show, Eq)

-- Push a label to the queue
pushLabel :: Label -> Queue -> Queue
pushLabel l EmptyQ    = QL l  EmptyQ
pushLabel l (QL l' q) = QL l' (pushLabel l q)
pushLabel l (QA t  q) = QA t  (pushLabel l q)

-- Push a type to the queue
pushType :: Type -> Queue -> Queue
pushType t EmptyQ    = QA t  EmptyQ
pushType t (QL l  q) = QL l  (pushType t q)
pushType t (QA t' q) = QA t' (pushType t q)

---------------------------
-- SUBTYPING CONSTRAINTS --
---------------------------

--   Sub =  Q    ⊢ t1 <: t2
type Sub = (Queue, Type, Type)

type Subs = [Sub]

-------------------
-- SUBSTITUTIONS --
-------------------

-- Polarity can be either positive or negative
data Polarity = PosT | NegT deriving Eq

instance Show Polarity where
  show PosT = "+"
  show NegT = "-"

-- A substitution consists of a unification variable with a given polarity
-- and the type it should be substituted with
type Substitution = [(TUni, Polarity, Type)]

------------
-- TABLES --
------------

-- u | lower | upper
---------------------
--  |        |
---------------------
--  |        |

type Table = [Entry]
data Entry = Entry {uni   :: TUni,
                    lower :: [Type],
                    upper :: [Type]
                    } deriving Eq

instance Show Entry where
  show entry = (show $ uni entry) ++ "  --  " ++
               (show $ lower entry) ++ "  --  " ++
               (show $ upper entry) ++ "\n"
