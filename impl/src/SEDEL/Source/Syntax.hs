{-# LANGUAGE DeriveGeneric,
             MultiParamTypeClasses,
             TemplateHaskell,
             FlexibleInstances,
             DeriveFunctor,
             TypeOperators,
             DeriveFoldable,
             FlexibleContexts,
             DeriveTraversable,
             StandaloneDeriving #-}

module SEDEL.Source.Syntax where

import           Data.Maybe (fromMaybe)
import           Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics (Generic)
import           Text.Megaparsec
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.TH

import           SEDEL.Common
import           SEDEL.Fix


-- | Modules
data Module = Module
  { moduleEntries :: [SDecl]
  , mainExpr      :: SDecl
  } deriving (Show, Generic)

-- | Declarations other than traits
data SDecl
  = DefDecl TmBind
  deriving (Show, Generic)

type RawName = String

-- f t1,...,tn (x1: A1) ... (xn: An): A = e
-- If A is provided, then e can mention f
data TmBind = TmBind
  { bindName            :: RawName                   -- f
  , bindTyParams        :: [(TyName, SType)]         -- t1, ..., tn
  , bindParams          :: [(TmName, Maybe Scheme)]  -- x1: A1, ..., xn: An
  , bindRhs             :: Expr                      -- e
  , bindRhsTyAscription :: Maybe Scheme              -- A
  , isOverride          :: Bool
  } deriving (Show, Generic)

type TmName = Name Expr

-- Expressions
data Expr = Var TmName
          | VarPoly TmName
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | Letrec (Bind (TmName, Embed Scheme) (Expr, Expr))
          | Let (Bind TmName (Expr, Expr))
          | Rec Label Expr
          | Proj Expr Label
          | Merge Expr Expr
          | LitV Double
          | BoolV Bool
          | PrimOp Operation Expr Expr
          | If Expr Expr Expr
          | Top
          -- marked source position, for error messages
          | Pos SourcePos Expr
          -- The following should disappear after desugaring
          | DRec' TmBind
  deriving (Show, Generic)

--------------------------------------------------------------------------------
-- coproduct
data (:+:) f g a = Inl (f a) | Inr (g a) deriving (Generic, Functor)
infixr :+:

composeAlg :: (Functor f, Functor g) => (f a -> a) -> (g a -> a) -> ((f :+: g) a -> a)
composeAlg fAlg gAlg = \fgx -> case fgx of
  (Inl x) -> fAlg x
  (Inr y) -> gAlg y

deriving instance (Foldable f, Foldable g) => Foldable (f :+: g)
--------------------------------------------------------------------------------
-- instances
class (Functor f, Functor g) => f <: g where
  inj :: f a -> g a
  prj :: g a -> Maybe (f a)

instance Functor f => f <: f where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f <: (f :+: g) where
  inj = Inl
  prj (Inl x) = Just x
  prj (Inr _) = Nothing

instance {-# OVERLAPPING #-} (Functor f, Functor g, Functor h, f <: g) => f <: (h :+: g) where
    inj = Inr . inj
    prj (Inl _) = Nothing
    prj (Inr x) = prj x

--------------------------------------------------------------------------------

type Label = String
type TyName = Name SType

data SType' a = NumT
              | BoolT
              | Arr a a
              | And a a
              | TVar TyName
              | SRecT Label a
              | TopT
              | BotT
    deriving (Generic, Functor, Foldable, Traversable)

type SType = Fix SType'

-- smart constructors
mkNumT, mkBoolT, mkBotT, mkTopT :: (SType' <: f) => Fix f
mkNumT  = In (inj NumT)
mkBoolT = In (inj BoolT)
mkBotT  = In (inj BotT)
mkTopT  = In (inj TopT)

mkArr, mkAnd :: (SType' <: f) => Fix f -> Fix f -> Fix f
mkArr t1 t2 = In (inj (Arr t1 t2))
mkAnd t1 t2 = In (inj (And t1 t2))

mkTVar :: (SType' <: f) => TyName -> Fix f
mkTVar name = In (inj (TVar name))

mkSRecT :: (SType' <: f) => Label -> Fix f -> Fix f
mkSRecT l t = In (inj (SRecT l t))

--------------------------------------------------------------------------------

type TUni = Name PType

data AType' a = Uni TUni
              | Join a a
              | Meet a a
      deriving (Generic, Functor, Foldable, Traversable)

type AType = Fix AType'

-- smart constructors
mkUni :: (AType' <: f) => TUni -> Fix f
mkUni u = In (inj (Uni u))

mkJoin, mkMeet :: (AType' <: f) => Fix f -> Fix f -> Fix f
mkJoin t1 t2 = In (inj (Join t1 t2))
mkMeet t1 t2 = In (inj (Meet t1 t2))

--------------------------------------------------------------------------------

type PType' = SType' :+: AType'
type PType = Fix PType'

--------------------------------------------------------------------------------

data Scheme = SType SType | DForall (Bind (TyName, Embed SType) Scheme) deriving (Show,Generic)


data Gam = EmptyG   | Gamma TmName PType Gam deriving (Eq, Show)
data Del = EmptyD   | Delta TyName SType Del deriving (Eq, Show)
data Dis = EmptyDis | Disj  PType  PType Dis deriving (Eq, Show)

data CtxType = CtxSch Gam Del PType deriving (Eq, Show, Generic)

-- Kinds k := * | k -> k
data Kind = Star | KArrow Kind Kind deriving (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- eq instances
instance Eq a => Eq (SType' a) where
  NumT         == NumT        = True
  BoolT        == BoolT       = True
  Arr t1 t2    == Arr t3 t4   = (t1 == t3) && (t2 == t4)
  And t1 t2    == And t3 t4   = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  TVar x1      == TVar x2     =  x1 == x2
  SRecT l1 t1  == SRecT l2 t2 = (l1 == l2) && (t1 == t2)
  TopT         == TopT        = True
  BotT         == BotT        = True
  _           == _           = False

instance Eq a => Eq (AType' a) where
  Uni   u1    == Uni   u2    = u1 == u2
  Join  t1 t2 == Join  t3 t4 = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  Meet  t1 t2 == Meet  t3 t4 = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  _           == _           = False

instance (Eq (f a), Eq (g a)) => Eq ((f :+: g) a) where
  (Inl x1) == (Inl x2) = x1 == x2
  (Inr y1) == (Inr y2) = y1 == y2
  _        == _        = False

--------------------------------------------------------------------------------
-- show instances

binOp :: Show a => a -> String -> a -> String
binOp l op r = concat ["(", show l, " ", op, " ", show r, ")"]

instance Show a => Show (SType' a) where
  show (NumT)        = "Int"
  show (BoolT)       = "Bool"
  show (Arr   t1 t2) = binOp t1 "->" t2
  show (And   t1 t2) = binOp t1 "&" t2
  show (SRecT l1 t1) = "{" ++ (show l1) ++ ":" ++ (show t1) ++ "}"
  show (TVar  u1   ) = "Var " ++ (show u1)
  show (TopT)        = "⊤"
  show (BotT)        = "⊥"

instance Show a => Show (AType' a) where
  show (Uni   u1   ) = "Uni " ++ (show u1)
  show (Join  t1 t2) = binOp t1 "⊔" t2
  show (Meet  t1 t2) = binOp t1 "⊓" t2

instance (Show (f a), Show (g a)) => Show ((f :+: g) a) where
  show (Inl x) = show x
  show (Inr y) = show y

--------------------------------------------------------------------------------

instance Pretty (Name a) where
    pretty v = Pretty.pretty (show v)

-- Unbound library instances

$(makeClosedAlpha ''SourcePos)

instance Alpha SType
instance Alpha PType
instance Alpha Scheme
instance Alpha Expr
instance Alpha TmBind
instance Alpha Kind

instance Alpha (SType' (Fix SType'))
instance Alpha (SType' (Fix (SType' :+: AType')))
instance Alpha (AType' (Fix (SType' :+: AType')))
instance Alpha ((:+:) SType' AType' (Fix (SType' :+: AType')))


instance Subst b SourcePos where
  subst _ _ = id
  substs _ = id

instance Subst Expr SType
instance Subst Expr PType
instance Subst Expr Scheme
instance Subst Expr Kind
instance Subst Expr ArithOp
instance Subst Expr LogicalOp
instance Subst Expr Operation
instance Subst Expr CompOp
instance Subst Expr TmBind

instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst SType Expr
instance Subst SType PType
instance Subst SType Scheme
instance Subst SType Operation
instance Subst SType LogicalOp
instance Subst SType CompOp
instance Subst SType ArithOp
instance Subst SType TmBind
instance Subst SType Kind


instance Subst SType SType where
  isvar (In (TVar v)) = Just (SubstName v)
  isvar _             = Nothing

instance Subst Expr (SType' (Fix SType'))
instance Subst (Fix SType') (SType' (Fix SType'))
instance Subst Expr (AType' (Fix (SType' :+: AType')))
instance Subst Expr (SType' (Fix (SType' :+: AType')))
instance Subst (Fix SType') (SType' (Fix (SType' :+: AType')))
instance Subst (Fix SType') (AType' (Fix (SType' :+: AType')))
instance Subst Expr ((:+:) SType' AType' (Fix (SType' :+: AType')))
instance Subst (Fix SType') ((:+:) SType' AType' (Fix (SType' :+: AType')))

--------------------------------------------------------------------------------

-- | Partial inverse of Pos
unPosExpr :: Expr -> Maybe SourcePos
unPosExpr (Pos p _) = Just p
unPosExpr _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Expr -> Maybe SourcePos
unPosDeep = unPosExpr

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Expr -> SourcePos
unPosFlaky t =
  fromMaybe (SourcePos "unknown location" (mkPos 0) (mkPos 0)) (unPosDeep t)
