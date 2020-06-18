{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module PHiDI.Source.Subtyping (subtype, equalSch) where


import           Data.Sequence ((|>), Seq(..))
import qualified Data.Sequence as Q
import           Protolude
import           Unbound.Generics.LocallyNameless
import           Data.Map as M

import           PHiDI.Environment
import           PHiDI.Source.Syntax
import           PHiDI.Source.Desugar
import           PHiDI.Fix

data L = LTy SType | LLa Label | LAll TyName SType

subtype :: SCtx -> Scheme -> Scheme -> Bool
subtype ctx st tt = runFreshM $ go
  where
    go :: FreshM Bool
    go = do
      let a = expandType ctx st
      let b = expandType ctx tt
      let
      subtypeS Q.empty a b

    subtypeS :: Q.Seq L -> Scheme -> Scheme -> FreshM Bool
    -- Base cases
    subtypeS Empty (SType (In NumT)) (SType (In NumT)) = return True
    subtypeS Empty (SType (In BoolT)) (SType (In BoolT)) = return True
    subtypeS Empty (SType (In BotT)) (SType (In BotT)) = return True
    subtypeS fs _ (SType (In TopT)) = return True
    subtypeS Empty (SType (In (TVar a))) (SType (In (TVar b))) = return $ a == b
    -- NumT
    subtypeS fs (SType (In (And a1 a2))) (SType (In NumT)) = do
      c1 <- subtypeS fs (SType a1) (SType mkNumT)
      c2 <- subtypeS fs (SType a2) (SType mkNumT)
      return $ c1 || c2
    subtypeS (LTy a :<| fs) (SType (In (Arr a1 a2))) (SType (In NumT)) = do
      c1 <- subtypeS Q.empty (SType a) (SType a1)
      c2 <- subtypeS fs (SType a2) (SType mkNumT)
      return $ c1 && c2
    subtypeS (LLa l :<| fs) (SType (In (SRecT l' a))) (SType (In NumT)) = if l == l'
        then subtypeS fs (SType a) (SType mkNumT)
        else return $ False
    subtypeS (LAll tv a :<| fs) (DForall b) (SType (In NumT)) = do
        ((tv' , Embed b'),  t) <- unbind b
        c1 <- subtypeS Q.empty (SType a) (SType b')
        c2 <- subtypeS fs (subst tv' (mkTVar tv) t) (SType mkNumT)
        return $ c1 && c2
    subtypeS _ (SType (In BotT)) (SType (In NumT)) = return True
    -- BoolT
    subtypeS fs (SType (In (And a1 a2))) (SType (In BoolT)) = do
      c1 <- subtypeS fs (SType a1) (SType mkBoolT)
      c2 <- subtypeS fs (SType a2) (SType mkBoolT)
      return $ c1 || c2
    subtypeS (LTy a :<| fs) (SType (In (Arr a1 a2))) (SType (In BoolT)) = do
      c1 <- subtypeS Q.empty (SType a) (SType a1)
      c2 <- subtypeS fs (SType a2) (SType mkBoolT)
      return $ c1 && c2
    subtypeS (LLa l :<| fs) (SType (In (SRecT l' a))) (SType (In BoolT)) = if l == l'
        then subtypeS fs (SType a) (SType mkBoolT)
        else return False
    subtypeS (LAll tv a :<| fs) (DForall b) (SType (In BoolT)) = do
        ((tv' , Embed b'),  t) <- unbind b
        c1 <- subtypeS Q.empty (SType a) (SType b')
        c2 <- subtypeS fs (subst tv' (mkTVar tv) t) (SType mkBoolT)
        return $ c1 && c2
    subtypeS _ (SType (In BotT)) (SType (In BoolT)) = return True
    -- type variable
    subtypeS fs (SType (In (And a1 a2))) (SType (In (TVar x))) = do
      c1 <- subtypeS fs (SType a1) (SType (mkTVar x))
      c2 <- subtypeS fs (SType a2) (SType (mkTVar x))
      return $ c1 || c2
    subtypeS (LTy a :<| fs) (SType (In (Arr a1 a2))) (SType (In (TVar x))) = do
      c1 <- subtypeS Q.empty (SType a) (SType a1)
      c2 <- subtypeS fs (SType a2) (SType (mkTVar x))
      return $ c1 && c2
    subtypeS (LLa l :<| fs) (SType (In (SRecT l' a))) (SType (In (TVar x))) = if l == l'
        then subtypeS fs (SType a) (SType (mkTVar x))
        else return False
    subtypeS (LAll tv a :<| fs) (DForall b) (SType (In (TVar x))) = do
        ((tv' , Embed b'),  t) <- unbind b
        c1 <- subtypeS Q.empty (SType a) (SType b')
        c2 <- subtypeS fs (subst tv' (mkTVar tv) t) (SType (mkTVar x))
        return $ c1 && c2
    subtypeS _ (SType (In BotT)) (SType (In (TVar _))) = return True
    -- Inductive cases
    subtypeS fs (SType a) (SType (In (And b1 b2))) = do
      c1 <- subtypeS fs (SType a) (SType b1)
      c2 <- subtypeS fs (SType a) (SType b2)
      return $ c1 && c2
    subtypeS fs (SType a) (SType (In (Arr b1 b2))) = subtypeS (fs |> LTy b1) (SType a) (SType b2)
    subtypeS fs (SType a) (SType (In (SRecT l b))) = subtypeS (fs |> LLa l) (SType a) (SType b)
    subtypeS fs (SType a) (DForall b) = do
      ((tv, Embed b'), t) <- unbind b
      subtypeS (fs |> LAll tv b') (SType a) t
    subtypeS _ a b = return False

--------------------------------------------------------------------------------

data DeBruijn = VarDB Lvl
              | NumDB
              | BoolDB
              | ArrDB DeBruijn DeBruijn
              | AndDB DeBruijn DeBruijn
              | RecDB Label DeBruijn
              | TopDB
              | BotDB
              | Forall Lvl DeBruijn DeBruijn
              deriving (Show)

type Lvl = Int

instance Eq DeBruijn where
  NumDB           == NumDB           = True
  BoolDB          == BoolDB          = True
  ArrDB t1 t2     == ArrDB t3 t4     = (t1 == t3) && (t2 == t4)
  AndDB t1 t2     == AndDB t3 t4     = ((t1 == t3) && (t2 == t4)) || ((t1 == t4) && (t2 == t3))
  VarDB x1        == VarDB x2        =  x1 == x2
  RecDB l1 t1     == RecDB l2 t2     = (l1 == l2) && (t1 == t2)
  TopDB           == TopDB           = True
  BotDB           == BotDB           = True
  Forall x1 t1 t2 == Forall x2 t3 t4 = (x1 == x2) && (t1 == t3) && (t2 == t4)
  _               == _               = False

equalSch :: Scheme -> Scheme -> Bool
equalSch sch1 sch2 = db1 == db2
  where

    db1 = runFreshM $ deBruijn sch1 M.empty 0
    db2 = runFreshM $ deBruijn sch2 M.empty 0

    deBruijn :: Fresh m => Scheme -> Map TyName Lvl -> Lvl -> m DeBruijn
    deBruijn (SType (In (TVar a))) m _ = return $ VarDB (m M.! a)
    deBruijn (SType (In NumT)) _ _ = return $ NumDB
    deBruijn (SType (In BoolT)) _ _ = return $ BoolDB
    deBruijn (SType (In TopT)) _ _ = return $ TopDB
    deBruijn (SType (In BotT)) _ _ = return $ BotDB
    deBruijn (SType (In (Arr t1 t2))) m l = do
      t1' <- deBruijn (SType t1) m l
      t2' <- deBruijn (SType t2) m l
      return $ ArrDB t1' t2'
    deBruijn (SType (In (And t1 t2))) m l = do
      t1' <- deBruijn (SType t1) m l
      t2' <- deBruijn (SType t2) m l
      return $ AndDB t1' t2'
    deBruijn (SType (In (SRecT l1 t1))) m l = do
      t1' <- deBruijn (SType t1) m l
      return $ RecDB l1 t1'
    deBruijn (DForall b) m l = do
      ((a, Embed t1), t2) <- unbind b
      t1' <- deBruijn (SType t1) m l
      t2' <- deBruijn t2 (M.insert a l m) (l + 1)
      return $ Forall l t1' t2'
