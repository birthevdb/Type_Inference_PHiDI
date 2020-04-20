module SEDEL.Util where

import            SEDEL.Source.Syntax
import qualified  SEDEL.Intermediate.Syntax as I
import            SEDEL.Fix

import Data.List (foldl', foldl1')
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name

-- Utility for parsing

evar :: String -> Expr
evar = Var . s2n

evarpoly :: String -> Expr
evarpoly = VarPoly . s2n

evarFi :: String -> I.FExpr
evarFi = I.Var . s2n

tvar :: String -> SType
tvar = mkTVar . s2n

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
mkRecdsT [] = mkTopT
mkRecdsT ((l, e):r) = foldl (\t (l', e') -> mkAnd t (mkSRecT l' e')) (mkSRecT l e) r

eletr :: String -> I.FType -> I.FExpr -> I.FExpr -> I.FExpr
eletr s t e b = I.Letrec (bind (s2n s, embed (Just t)) (e, b))

elet :: String -> Expr -> Expr -> Expr
elet s e b = Let (bind (s2n s) (e, b))

eletrec :: String -> Scheme -> Expr -> Expr -> Expr
eletrec s t e b = Letrec (bind (s2n s, embed t) (e, b))

getFreshUni :: Fresh m => m TUni
getFreshUni = fresh (Fn "u" 0)

topLike :: SType -> Bool
topLike (In  TopT)       = True
topLike (In (And t1 t2)) = topLike t1 && topLike t2
topLike (In (Arr _   t)) = topLike t
topLike (In (SRecT _ t)) = topLike t
topLike _                = False


topLikeP :: PType -> Bool
topLikeP (In (Inl TopT))        = True
topLikeP (In (Inl (And t1 t2))) = topLikeP t1 && topLikeP t2
topLikeP (In (Inl (Arr _   t))) = topLikeP t
topLikeP (In (Inl (SRecT _ t))) = topLikeP t
topLikeP _                      = False
