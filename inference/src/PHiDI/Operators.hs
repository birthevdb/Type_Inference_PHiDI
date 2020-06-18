{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}

module PHiDI.Operators where

import           Protolude
import           Unbound.Generics.LocallyNameless


data Operation = Arith ArithOp
               | Comp CompOp
               | Logical LogicalOp
               deriving (Eq, Show, Generic)

data ArithOp = Add | Sub | Mul | Div deriving (Eq, Show, Generic)

data CompOp = Lt | Gt | Equ | Neq deriving (Eq, Show, Generic)

data LogicalOp =  LAnd | LOr deriving (Eq, Show, Generic)

instance Alpha Operation
instance Alpha ArithOp
instance Alpha LogicalOp
instance Alpha CompOp
