{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, NoImplicitPrelude #-}

module SEDEL.Common where

import Unbound.Generics.LocallyNameless
import Protolude


data Operation = Arith ArithOp
               | Comp CompOp
               | Logical LogicalOp
               deriving (Eq, Show, Generic)

-- instance Show Operation where
--   show (Arith a)   = show a
--   show (Comp c)    = show c
--   show (Logical l) = show l

data ArithOp = Add | Sub | Mul | Div deriving (Eq, Show, Generic)

data CompOp = Lt | Gt | Equ | Neq deriving (Eq, Show, Generic)

data LogicalOp =  LAnd | LOr deriving (Eq, Show, Generic)

-- instance Show ArithOp where
--   show Add = " + "
--   show Sub = " - "
--   show Mul = " * "
--   show Div = " / "
--
-- instance Show CompOp where
--   show Lt  = " < "
--   show Gt  = " > "
--   show Equ = " == "
--   show Neq = " =/= "
--
-- instance Show LogicalOp where
--   show LAnd = " && "
--   show LOr  = " || "

instance Alpha Operation
instance Alpha ArithOp
instance Alpha LogicalOp
instance Alpha CompOp
