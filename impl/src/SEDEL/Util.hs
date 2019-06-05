module SEDEL.Util where

import SEDEL.Source.Syntax
import qualified SEDEL.Intermediate.Syntax as I

import Data.List (foldl', foldl1')
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name

-- Utility for parsing

evar :: String -> Expr
evar = Var . s2n

evarFi :: String -> I.FExpr
evarFi = I.Var . s2n

tvar :: String -> SType
tvar = TVar . s2n

ebind :: String -> Expr -> Bind TmName Expr
ebind n = bind (s2n n)

elam :: String -> Expr -> Expr
elam b e = Lam (ebind b e)

tforall :: (String,  SType) -> Scheme -> Scheme
tforall (s, t) b = DForall (bind (s2n s, embed t) b)

eapp :: Expr -> Expr -> Expr
eapp = App

mkRecds :: [(Label, Expr)] -> Expr
mkRecds [] = Top
mkRecds ((l, e):r) = foldl' (\t (l', e') -> Merge t (Rec l' e')) (Rec l e) r

mkRecds' :: [TmBind] -> Expr
mkRecds' = foldl1' Merge . map DRec'

mkRecdsT :: [(Label, SType)] -> SType
mkRecdsT [] = TopT
mkRecdsT ((l, e):r) = foldl (\t (l', e') -> And t (SRecT l' e')) (SRecT l e) r

mkArr :: SType -> [SType] ->SType
mkArr = foldr Arr

eletr :: String -> I.FType -> I.FExpr -> I.FExpr -> I.FExpr
eletr s t e b = I.Letrec (bind (s2n s, embed (Just t)) (e, b))

elet :: String -> Expr -> Expr -> Expr
elet s e b = Let (bind (s2n s) (e, b))

getFreshUni :: Fresh m => m TUni
getFreshUni = fresh (Fn "u" 0)

topLike :: SType -> Bool
topLike  TopT       = True
topLike (And a b)   = (topLike a) && (topLike b)
topLike (Arr _ b)   = topLike b
topLike (SRecT _ t) = topLike t
topLike  _          = False
