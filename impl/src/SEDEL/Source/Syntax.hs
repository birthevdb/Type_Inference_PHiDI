{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, TemplateHaskell, FlexibleInstances #-}

module SEDEL.Source.Syntax where

import           Data.Maybe (fromMaybe)
import           Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics (Generic)
import           Text.Megaparsec
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.TH

import           SEDEL.Common


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
type TyName = Name SType

-- Expression
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

type Label = String

data SType = NumT
          | BoolT
          | Arr SType SType
          | And SType SType
          | TVar TyName
          | SRecT Label SType
          | TopT
          | BotT
    deriving (Generic)

data Scheme = SType SType | DForall (Bind (TyName, Embed SType) Scheme) deriving (Show, Generic)

type TUni = Name PType

data Gam = EmptyG   | Gamma TmName PType Gam deriving (Eq, Show)
data Del = EmptyD   | Delta TUni   SType Del deriving (Eq, Show)
data Dis = EmptyDis | Disj  PType  PType Dis deriving (Eq, Show)

data PType = P SType
           | Uni TUni
           | Join PType PType
           | Meet PType PType
           | PArr PType PType
           | PRecT Label PType
           | PAnd PType PType
   deriving (Generic)

data CtxType = CtxSch Gam Del PType deriving (Eq, Show, Generic)

-- Kinds k := * | k -> k
data Kind = Star | KArrow Kind Kind deriving (Eq, Show, Generic)


instance Eq SType where
  NumT         == NumT        = True
  BoolT        == BoolT       = True
  Arr t1 t2    == Arr t3 t4   = (t1 == t3) && (t2 == t4)
  And t1 t2    == And t3 t4   = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  TVar x1      == TVar x2     =  x1 == x2
  SRecT l1 t1  == SRecT l2 t2 = (l1 == l2) && (t1 == t2)
  TopT         == TopT        = True
  BotT         == BotT        = True
  _            == _           = False


instance Show SType where
  show (NumT)  = "Int"
  show (BoolT) = "Bool"
  show (Arr  t1 t2)  = "(" ++ (show t1) ++ " -> " ++ (show t2) ++ ")"
  show (And  t1 t2)  = "(" ++ (show t1) ++ " & " ++ (show t2) ++ ")"
  show (SRecT l1 t1)  = "{" ++ (show l1) ++ ":" ++ (show t1) ++ "}"
  show (TVar   u1   )  = "Var " ++ (show u1)
  show (TopT)  = "⊤"
  show (BotT)  = "⊥"

instance Eq PType where
  P t1        == P t2        = t1 == t2
  PArr t1 t2  == PArr t3 t4  = (t1 == t3) && (t2 == t4)
  PAnd t1 t2  == PAnd t3 t4  = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  PRecT l1 t1 == PRecT l2 t2 = (l1 == l2) && (t1 == t2)
  Uni   u1    == Uni   u2    = u1 == u2
  Join  t1 t2 == Join  t3 t4 = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  Meet  t1 t2 == Meet  t3 t4 = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  _           == _           = False

instance Show PType where
  show (P     t1   )  = show t1
  show (PArr  t1 t2)  = "(" ++ (show t1) ++ " -> " ++ (show t2) ++ ")"
  show (PAnd  t1 t2)  = "(" ++ (show t1) ++ " & " ++ (show t2) ++ ")"
  show (PRecT l1 t1)  = "{" ++ (show l1) ++ ":" ++ (show t1) ++ "}"
  show (Uni   u1   )  = "Uni " ++ (show u1)
  show (Join  t1 t2)  = "(" ++ (show t1) ++ " ⊔ " ++ (show t2) ++ ")"
  show (Meet  t1 t2)  = "(" ++ (show t1) ++ " ⊓ " ++ (show t2) ++ ")"


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
  isvar (TVar v) = Just (SubstName v)
  isvar _ = Nothing


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
