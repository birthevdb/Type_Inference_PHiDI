{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses #-}

module SEDEL.Target.Syntax where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)

import SEDEL.Common


---------------------------
-- Untyped lambda calculus
---------------------------

type UName = Name UExpr
type AName = Name UType

data UType = UNumT
           | UBoolT
           | UUnitT
           | UArr UType UType
           | UPairT UType UType
           | UTVar AName
           | UScheme AName UType
           deriving (Show, Generic)

data UExpr = UVar UName
           | UApp UExpr UExpr
           | ULam (Bind UName UExpr)
           -- ^ only for internal use
           | UPair UExpr UExpr
           | UP1 UExpr
           | UP2 UExpr
           | ULitV Double
           | UBoolV Bool
           | UUnit
           | UPrimOp Operation UExpr UExpr
           | UIf UExpr UExpr UExpr
           | UBLam (Bind AName UExpr) -- Big lambda
           | Bot
           deriving (Show, Generic)

instance Alpha UExpr
instance Alpha UType

instance Subst UExpr ArithOp
instance Subst UExpr LogicalOp
instance Subst UExpr Operation
instance Subst UExpr CompOp
instance Subst UExpr UType
instance Subst UExpr UExpr where
  isvar (UVar v) = Just (SubstName v)
  isvar _ = Nothing

evar :: String -> UExpr
evar = UVar . s2n

ebind :: String -> UExpr -> Bind UName UExpr
ebind n = bind (s2n n)

elam :: String -> UExpr -> UExpr
elam b e = ULam (ebind b e)

eapp :: UExpr -> UExpr -> UExpr
eapp = UApp

elet :: UName -> UExpr -> UExpr -> UExpr
elet n e b = UApp (ULam (bind n b)) e
