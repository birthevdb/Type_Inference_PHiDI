{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

module SEDEL.Intermediate.Syntax where

import           Data.Maybe                          (fromMaybe)
import           GHC.Generics                        (Generic)
import           Text.Megaparsec
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.TH

import           SEDEL.Common


-- | Modules
data Module = Module
  { moduleEntries :: [SDecl]
  , mainFExpr     :: SDecl
  } deriving (Show, Generic)

-- | Declarations other than traits
data SDecl
  = DefDecl TmBind
  -- | TypeDecl TypeBind
  deriving (Show, Generic)

type RawName = String


-- f A1,...,An (x1: t1) ... (xn: tn): t = e
-- If t is provided, then e can mention f
data TmBind = TmBind
  { bindName            :: RawName                   -- f
  , bindTyParams        :: [(TyName, FType)]          -- A1, ..., An
  , bindParams          :: [(TmName, Maybe FType)]    -- x1: t1, ..., xn: tn
  , bindRhs             :: FExpr                      -- e
  , bindRhsTyAscription :: Maybe FType                -- t
  , isOverride          :: Bool
  } deriving (Show, Generic)


type TmName = Name FExpr
type TyName = Name FType

-- FExpression
data FExpr = Anno FExpr FType
          | Var TmName
          | App FExpr FExpr
          | Lam (Bind TmName FExpr)
          | Letrec (Bind (TmName, Embed (Maybe FType)) (FExpr, FExpr))
            -- ^ let expression, possibly recursive
          | DLam (Bind (TyName, Embed FType) FExpr)
          | TApp FExpr FType
          | Rec Label FExpr
          | Acc FExpr Label
          | Remove FExpr Label (Maybe FType)
          | Merge FExpr FExpr
          | LitV Double
          | BoolV Bool
          | PrimOp Operation FExpr FExpr
          | If FExpr FExpr FExpr
          | Top
          -- practical matters for surface language
          | Pos SourcePos FExpr
          -- ^ marked source position, for error messages
          | LamA (Bind (TmName, Embed FType) FExpr)
          -- ^ Not exposed to users, for internal use
          | Bot
          -- The following should disappear after desugaring
          | DRec' TmBind
  deriving (Show, Generic)

type Label = String
data FType = NumT
          | BoolT
          | Arr FType FType
          | And FType FType
          | TVar TyName
          | DForall (Bind (TyName, Embed FType) FType)
          | SRecT Label FType
          | TopT
          | BotT
          | OpAbs (Bind (TyName, Embed Kind) FType)
          -- ^ FType-level abstraction: "type T A = t" becomes "type T = \A : *. t",
          | OpApp FType FType
          -- ^ FType-level application: t1 t2

  deriving (Show, Generic)

-- Kinds k := * | k -> k
data Kind = Star | KArrow Kind Kind deriving (Eq, Show, Generic)

-- Unbound library instances

$(makeClosedAlpha ''SourcePos)

instance Alpha FType
instance Alpha FExpr
instance Alpha SDecl
instance Alpha TmBind
instance Alpha Kind


instance Subst b SourcePos where
  subst _ _ = id
  substs _ = id

instance Subst FExpr FType
instance Subst FExpr Kind
instance Subst FExpr ArithOp
instance Subst FExpr LogicalOp
instance Subst FExpr Operation
instance Subst FExpr CompOp
instance Subst FExpr SDecl
instance Subst FExpr TmBind

instance Subst FExpr FExpr where
  isvar (Var v) = Just (SubstName v)
  isvar _       = Nothing

instance Subst FType FExpr
instance Subst FType Operation
instance Subst FType LogicalOp
instance Subst FType CompOp
instance Subst FType ArithOp
instance Subst FType SDecl
instance Subst FType TmBind
instance Subst FType Kind


instance Subst FType FType where
  isvar (TVar v) = Just (SubstName v)
  isvar _        = Nothing


-- | Partial inverse of Pos
unPosFExpr :: FExpr -> Maybe SourcePos
unPosFExpr (Pos p _) = Just p
unPosFExpr _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: FExpr -> Maybe SourcePos
unPosDeep = unPosFExpr

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: FExpr -> SourcePos
unPosFlaky t =
  fromMaybe (SourcePos "unknown location" (mkPos 0) (mkPos 0)) (unPosDeep t)
