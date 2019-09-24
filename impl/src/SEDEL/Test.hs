{-# LANGUAGE FlexibleContexts, PatternGuards, NoImplicitPrelude, LambdaCase, OverloadedStrings, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

module SEDEL.Test where

import           Protolude
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Name as N
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Test.QuickCheck

import           SEDEL.Source.Syntax
import           SEDEL.Common
import           SEDEL.Util
import           SEDEL.Environment
import           SEDEL.Source.Inference
import           SEDEL.PrettyPrint
import           SEDEL.Source.Subtyping
import           SEDEL.Intermediate.TypeCheck

-------------
-- DATATYPES
-------------

data Derivation = DTop
                | DNum Double
                | DBool Bool
                | DVar TmName
                | DApp Derivation Derivation
                | DAbs Derivation TmName SType
                | DMerge Derivation Derivation
                | DRec Derivation Label
                | DProj Derivation Label
                | DTAbs Derivation TyName SType
                | DTApp Derivation SType
                | DSub Derivation SType
                | DLet TmName Derivation Derivation
                deriving Show

-------------
-- GENERATORS
-------------

-- Generate PHiDI derivations
genDerivation :: Int -> SType -> [(FreshM TmName, SType)] -> Gen (FreshM Derivation)
genDerivation n t ctx = if n < 1 then case t of
  BoolT -> frequency [(1, fmap (return . DBool) arbitrary)]
  NumT -> frequency [(1, fmap (return . DNum) arbitrary)]
  TopT -> frequency [(1, return $ return DTop)]
  Arr t1 t2 -> frequency [(1, do tmn <- genTmName
                                 fd1 <- genDerivation 0 t2 ((tmn, t1) : ctx)
                                 st1 <- elements $ map return [t1]
                                 return $ liftM3 DAbs fd1 tmn st1)]
  SRecT l1 t1 -> frequency [(1, do fd <- genDerivation 0 t1 ctx
                                   return $ liftM2 DRec fd (return l1))]
  And t1 t2 -> frequency [(1, do fd1 <- genDerivation 0 t1 ctx
                                 fd2 <- genDerivation 0 t2 ctx
                                 return $ liftM2 DMerge fd1 fd2)]
  _ -> frequency [(1, return $ return DTop),
                  (1, fmap (return . DNum) arbitrary),
                  (1, fmap (return . DBool) arbitrary)]
    else case (pick t ctx) of
      Nothing -> case t of
        TopT -> frequency [(1, return $ return DTop)]
        NumT -> frequency [(1, fmap (return . DNum) arbitrary),
                           (n, do l  <- genLabel
                                  fd <- genDerivation (n `div` 2) (SRecT l NumT) ctx
                                  return $ liftM2 DProj fd (return l)),
                           (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                  fd1 <- genDerivation (n `div` 2) (Arr st1 NumT) ctx
                                  fd2 <- genDerivation (n `div` 2) st1 ctx
                                  return $ liftM2 DApp fd1 fd2),
                           (n, do tmn <- genTmName
                                  st1 <- runFreshM <$> genSType (n `div` 2)
                                  fd1 <- genDerivation (n `div` 2) st1 ctx
                                  fd2 <- genDerivation (n `div` 2) NumT ((tmn, st1) : ctx)
                                  return $ liftM3 DLet tmn fd1 fd2)
                            ]
        BoolT -> frequency [(1, fmap (return . DBool) arbitrary),
                            (n, do l  <- genLabel
                                   fd <- genDerivation (n `div` 2) (SRecT l BoolT) ctx
                                   return $ liftM2 DProj fd (return l)),
                            (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                   fd1 <- genDerivation (n `div` 2) (Arr st1 BoolT) ctx
                                   fd2 <- genDerivation (n `div` 2) st1 ctx
                                   return $ liftM2 DApp fd1 fd2),
                            (n, do tmn <- genTmName
                                   st1 <- runFreshM <$> genSType (n `div` 2)
                                   fd1 <- genDerivation (n `div` 2) st1 ctx
                                   fd2 <- genDerivation (n `div` 2) BoolT ((tmn, st1) : ctx)
                                   return $ liftM3 DLet tmn fd1 fd2)
                            ]
        Arr t1 t2 -> frequency [(n, do tmn <- genTmName
                                       st1 <- elements $ map return [t1]
                                       fd1 <- genDerivation (n `div` 2) t2 ((tmn, t1) : ctx)
                                       return $ liftM3 DAbs fd1 tmn st1),
                                (n, do l <- genLabel
                                       fd <- genDerivation (n `div` 2) (SRecT l (Arr t1 t2)) ctx
                                       return $ liftM2 DProj fd (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) (Arr st1 (Arr t1 t2)) ctx
                                       fd2 <- genDerivation (n `div` 2) st1 ctx
                                       return $ liftM2 DApp fd1 fd2),
                                (n, do tmn <- genTmName
                                       st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) st1 ctx
                                       fd2 <- genDerivation (n `div` 2) (Arr t1 t2) ((tmn, st1) : ctx)
                                       return $ liftM3 DLet tmn fd1 fd2)
                                ]
        And t1 t2 -> frequency [(n, do fd1 <- genDerivation (n `div` 2) t1 ctx
                                       fd2 <- genDerivation (n `div` 2) t2 ctx
                                       return $ liftM2 DMerge fd1 fd2),
                                (n, do l  <- genLabel
                                       fd <- genDerivation (n `div` 2) (SRecT l (And t1 t2)) ctx
                                       return $ liftM2 DProj fd (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) (Arr st1 (And t1 t2)) ctx
                                       fd2 <- genDerivation (n `div` 2) st1 ctx
                                       return $ liftM2 DApp fd1 fd2),
                                (n, do tmn <- genTmName
                                       st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) st1 ctx
                                       fd2 <- genDerivation (n `div` 2) (And t1 t2) ((tmn, st1) : ctx)
                                       return $ liftM3 DLet tmn fd1 fd2)
                                ]
        SRecT l1 t1 -> frequency [(n, do fd <- genDerivation (n `div` 2) t1 ctx
                                         return $ liftM2 DRec fd (return l1)),
                                  (n, do l  <- genLabel
                                         fd <- genDerivation (n `div` 2) (SRecT l (SRecT l1 t1)) ctx
                                         return $ liftM2 DProj fd (return l)),
                                  (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                         fd1 <- genDerivation (n `div` 2) (Arr st1 (SRecT l1 t1)) ctx
                                         fd2 <- genDerivation (n `div` 2) st1 ctx
                                         return $ liftM2 DApp fd1 fd2),
                                  (n, do tmn <- genTmName
                                         st1 <- runFreshM <$> genSType (n `div` 2)
                                         fd1 <- genDerivation (n `div` 2) st1 ctx
                                         fd2 <- genDerivation (n `div` 2) (SRecT l1 t1) ((tmn, st1) : ctx)
                                         return $ liftM3 DLet tmn fd1 fd2)
                                  ]
        _ -> frequency [(n, fmap (return . DNum) arbitrary),
                        (n, fmap (return . DBool) arbitrary),
                        (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                               fd <- genDerivation (n `div` 2) st1 ctx
                               ft <- genSType (n `div` 2)
                               return $ liftM2 DSub fd ft)]
      Just tmn1 -> case t of
        TopT -> frequency [(1, return $ return DTop),
                           (n, do return $ liftM DVar tmn1)]
        NumT -> frequency [(1, fmap (return . DNum) arbitrary),
                           (n, do return $ liftM DVar tmn1),
                           (n, do l  <- genLabel
                                  fd <- genDerivation (n `div` 2) (SRecT l NumT) ctx
                                  return $ liftM2 DProj fd (return l)),
                           (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                  fd1 <- genDerivation (n `div` 2) (Arr st1 NumT) ctx
                                  fd2 <- genDerivation (n `div` 2) st1 ctx
                                  return $ liftM2 DApp fd1 fd2),
                           (n, do tmn <- genTmName
                                  st1 <- runFreshM <$> genSType (n `div` 2)
                                  fd1 <- genDerivation (n `div` 2) st1 ctx
                                  fd2 <- genDerivation (n `div` 2) NumT ((tmn, st1) : ctx)
                                  return $ liftM3 DLet tmn fd1 fd2)
                            ]
        BoolT -> frequency [(1, fmap (return . DBool) arbitrary),
                            (n, do return $ liftM DVar tmn1),
                            (n, do l  <- genLabel
                                   fd <- genDerivation (n `div` 2) (SRecT l BoolT) ctx
                                   return $ liftM2 DProj fd (return l)),
                            (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                   fd1 <- genDerivation (n `div` 2) (Arr st1 BoolT) ctx
                                   fd2 <- genDerivation (n `div` 2) st1 ctx
                                   return $ liftM2 DApp fd1 fd2),
                            (n, do tmn <- genTmName
                                   st1 <- runFreshM <$> genSType (n `div` 2)
                                   fd1 <- genDerivation (n `div` 2) st1 ctx
                                   fd2 <- genDerivation (n `div` 2) BoolT ((tmn, st1) : ctx)
                                   return $ liftM3 DLet tmn fd1 fd2)
                             ]
        Arr t1 t2 -> frequency [(n, do return $ liftM DVar tmn1),
                                (n, do tmn <- genTmName
                                       st1 <- elements $ map return [t1]
                                       fd1 <- genDerivation (n `div` 2) t2 ((tmn, t1) : ctx)
                                       return $ liftM3 DAbs fd1 tmn st1),
                                (n, do l <- genLabel
                                       fd <- genDerivation (n `div` 2) (SRecT l (Arr t1 t2)) ctx
                                       return $ liftM2 DProj fd (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) (Arr st1 (Arr t1 t2)) ctx
                                       fd2 <- genDerivation (n `div` 2) st1 ctx
                                       return $ liftM2 DApp fd1 fd2),
                                (n, do tmn <- genTmName
                                       st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) st1 ctx
                                       fd2 <- genDerivation (n `div` 2) (Arr t1 t2) ((tmn, st1) : ctx)
                                       return $ liftM3 DLet tmn fd1 fd2)
                                ]
        And t1 t2 -> frequency [(n, do return $ liftM DVar tmn1),
                                (n, do fd1 <- genDerivation (n `div` 2) t1 ctx
                                       fd2 <- genDerivation (n `div` 2) t2 ctx
                                       return $ liftM2 DMerge fd1 fd2),
                                (n, do l  <- genLabel
                                       fd <- genDerivation (n `div` 2) (SRecT l (And t1 t2)) ctx
                                       return $ liftM2 DProj fd (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) (Arr st1 (And t1 t2)) ctx
                                       fd2 <- genDerivation (n `div` 2) st1 ctx
                                       return $ liftM2 DApp fd1 fd2),
                                (n, do tmn <- genTmName
                                       st1 <- runFreshM <$> genSType (n `div` 2)
                                       fd1 <- genDerivation (n `div` 2) st1 ctx
                                       fd2 <- genDerivation (n `div` 2) (And t1 t2) ((tmn, st1) : ctx)
                                       return $ liftM3 DLet tmn fd1 fd2)
                                ]
        SRecT l1 t1 -> frequency [(n, do return $ liftM DVar tmn1),
                                  (n, do fd <- genDerivation (n `div` 2) t1 ctx
                                         return $ liftM2 DRec fd (return l1)),
                                  (n, do l  <- genLabel
                                         fd <- genDerivation (n `div` 2) (SRecT l (SRecT l1 t1)) ctx
                                         return $ liftM2 DProj fd (return l)),
                                  (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                         fd1 <- genDerivation (n `div` 2) (Arr st1 (SRecT l1 t1)) ctx
                                         fd2 <- genDerivation (n `div` 2) st1 ctx
                                         return $ liftM2 DApp fd1 fd2),
                                  (n, do tmn <- genTmName
                                         st1 <- runFreshM <$> genSType (n `div` 2)
                                         fd1 <- genDerivation (n `div` 2) st1 ctx
                                         fd2 <- genDerivation (n `div` 2) (SRecT l1 t1) ((tmn, st1) : ctx)
                                         return $ liftM3 DLet tmn fd1 fd2)
                                  ]
        _ -> frequency [(n, fmap (return . DNum) arbitrary),
                        (n, fmap (return . DBool) arbitrary),
                        (n, do return $ liftM DVar tmn1),
                        (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                               fd <- genDerivation (n `div` 2) st1 ctx
                               ft <- genSType (n `div` 2)
                               return $ liftM2 DSub fd ft)]

-- Generate PHiDI types
genSType :: Int -> Gen (FreshM SType)
genSType n = frequency [ (3, elements $ map return [NumT, BoolT, TopT]),
                         (n, liftM (liftM TVar) genTyName),
                         (n, do ft <- genSType (n `div` 2)
                                l  <- genLabel
                                return $ (SRecT l) <$> ft),
                         (n, do ft1 <- genSType (n `div` 2)
                                ft2 <- genSType (n `div` 2)
                                return $ liftM2 And ft1 ft2),
                         (n, do ft1 <- genSType (n `div` 2)
                                ft2 <- genSType (n `div` 2)
                                return $ liftM2 Arr ft1 ft2)]

-- Generate PHiDI expressions
genExpr :: Int -> SType -> [(FreshM TmName, SType)] -> Gen (FreshM Expr)
genExpr n t ctx = if n < 1 then case t of
  Arr t1 t2 -> frequency [(1, do tmn <- genTmName
                                 fe  <- genExpr (n `div` 2) t2 ((tmn, t1) : ctx)
                                 return ( fe  >>= \e ->
                                          tmn >>= \mn ->
                                          return $ Lam (bind mn e)))]
  SRecT l1 t1 -> frequency [(1, do fe <- genExpr (n `div` 2) t1 ctx
                                   return $ (Rec l1) <$> fe)]
  _ -> frequency [(1, fmap (return . BoolV) arbitrary),
                  (1, fmap (return . LitV) arbitrary)]
    else case (pick t ctx) of
      Nothing -> case t of
        NumT -> frequency [ (1, fmap (return . LitV) arbitrary),
                            (n, do l  <- genLabel
                                   fe <- genExpr (n `div` 2) (SRecT l NumT) ctx
                                   return $ liftM2 Proj fe (return l)),
                            (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                   fe1 <- genExpr (n `div` 2) (Arr st1 NumT) ctx
                                   fe2 <- genExpr (n `div` 2) st1 ctx
                                   return $ liftM2 App fe1 fe2),
                            (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                   tmn <- genTmName
                                   fe1 <- genExpr (n `div` 2) st1 ctx
                                   fe2 <- genExpr (n `div` 2) NumT ((tmn, st1) : ctx)
                                   return ( fe1 >>= \e1 ->
                                            fe2 >>= \e2 ->
                                            tmn >>= \mn ->
                                            return $ Let (bind mn (e1, e2)))),
                            (n, do fe1 <- genExpr (n `div` 2) NumT ctx
                                   fe2 <- genExpr (n `div` 2) NumT ctx
                                   fop <- fmap (return . Arith) arbitrary
                                   return $ liftM3 PrimOp fop fe1 fe2),
                            (n, do fe1 <- genExpr (n `div` 2) BoolT ctx
                                   fe2 <- genExpr (n `div` 2) NumT ctx
                                   fe3 <- genExpr (n `div` 2) NumT ctx
                                   return $ liftM3 If fe1 fe2 fe3)
                                   ]
        BoolT -> frequency [ (1, fmap (return . BoolV) arbitrary),
                             (n, do l  <- genLabel
                                    fe <- genExpr (n `div` 2) (SRecT l BoolT) ctx
                                    return $ liftM2 Proj fe (return l)),
                             (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                    fe1 <- genExpr (n `div` 2) (Arr st1 BoolT) ctx
                                    fe2 <- genExpr (n `div` 2) st1 ctx
                                    return $ liftM2 App fe1 fe2),
                             (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                    tmn <- genTmName
                                    fe1 <- genExpr (n `div` 2) st1 ctx
                                    fe2 <- genExpr (n `div` 2) BoolT ((tmn, st1) : ctx)
                                    return ( fe1 >>= \e1 ->
                                             fe2 >>= \e2 ->
                                             tmn >>= \mn ->
                                             return $ Let (bind mn (e1, e2)))),
                             (n, do fe1 <- genExpr (n `div` 2) NumT ctx
                                    fe2 <- genExpr (n `div` 2) NumT ctx
                                    fop <- fmap (return . Comp) arbitrary
                                    return $ liftM3 PrimOp fop fe1 fe2),
                             (n, do fe1 <- genExpr (n `div` 2) BoolT ctx
                                    fe2 <- genExpr (n `div` 2) BoolT ctx
                                    fop <- fmap (return . Logical) arbitrary
                                    return $ liftM3 PrimOp fop fe1 fe2),
                             (n, do fe1 <- genExpr (n `div` 2) BoolT ctx
                                    fe2 <- genExpr (n `div` 2) BoolT ctx
                                    fe3 <- genExpr (n `div` 2) BoolT ctx
                                    return $ liftM3 If fe1 fe2 fe3)
                                    ]
        Arr t1 t2 -> frequency [(n, do tmn <- genTmName
                                       fe  <- genExpr (n `div` 2) t2 ((tmn, t1) : ctx)
                                       return ( fe  >>= \e ->
                                                tmn >>= \mn ->
                                                return $ Lam (bind mn e))),
                                (n, do l  <- genLabel
                                       fe <- genExpr (n `div` 2) (SRecT l (Arr t1 t2)) ctx
                                       return $ liftM2 Proj fe (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fe1 <- genExpr (n `div` 2) (Arr st1 (Arr t1 t2)) ctx
                                       fe2 <- genExpr (n `div` 2) st1 ctx
                                       return $ liftM2 App fe1 fe2),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       tmn <- genTmName
                                       fe1 <- genExpr (n `div` 2) st1 ctx
                                       fe2 <- genExpr (n `div` 2) (Arr t1 t2) ((tmn, st1) : ctx)
                                       return ( fe1 >>= \e1 ->
                                                fe2 >>= \e2 ->
                                                tmn >>= \mn ->
                                                return $ Let (bind mn (e1, e2))))
                                      ]
        And t1 t2 -> frequency [(n, do fe1 <- genExpr (n `div` 2) t1 ctx
                                       fe2 <- genExpr (n `div` 2) t2 ctx
                                       return $ liftM2 Merge fe1 fe2),
                                (n, do l  <- genLabel
                                       fe <- genExpr (n `div` 2) (SRecT l (And t1 t2)) ctx
                                       return $ liftM2 Proj fe (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fe1 <- genExpr (n `div` 2) (Arr st1 (And t1 t2)) ctx
                                       fe2 <- genExpr (n `div` 2) st1 ctx
                                       return $ liftM2 App fe1 fe2),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       tmn <- genTmName
                                       fe1 <- genExpr (n `div` 2) st1 ctx
                                       fe2 <- genExpr (n `div` 2) (And t1 t2) ((tmn, st1) : ctx)
                                       return ( fe1 >>= \e1 ->
                                                fe2 >>= \e2 ->
                                                tmn >>= \mn ->
                                                return $ Let (bind mn (e1, e2))))
                                      ]
        SRecT l t1 -> frequency [(n, do fe <- genExpr (n `div` 2) t1 ctx
                                        return $ (Rec l) <$> fe),
                                 (n, do l1 <- genLabel
                                        fe <- genExpr (n `div` 2) (SRecT l1 (SRecT l t1)) ctx
                                        return $ liftM2 Proj fe (return l1)),
                                 (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                        fe1 <- genExpr (n `div` 2) (Arr st1 (SRecT l t1)) ctx
                                        fe2 <- genExpr (n `div` 2) st1 ctx
                                        return $ liftM2 App fe1 fe2),
                                 (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                        tmn <- genTmName
                                        fe1 <- genExpr (n `div` 2) st1 ctx
                                        fe2 <- genExpr (n `div` 2) (SRecT l t1) ((tmn, st1) : ctx)
                                        return ( fe1 >>= \e1 ->
                                                 fe2 >>= \e2 ->
                                                 tmn >>= \mn ->
                                                 return $ Let (bind mn (e1, e2))))
                                       ]
        _ -> frequency [(1, fmap (return . BoolV) arbitrary),
                        (1, fmap (return . LitV ) arbitrary)]
      Just tmn1 -> case t of
        NumT -> frequency [(1, fmap (return . LitV ) arbitrary),
                          (n, do return $ liftM Var tmn1),
                          (n, do l  <- genLabel
                                 fe <- genExpr (n `div` 2) (SRecT l NumT) ctx
                                 return $ liftM2 Proj fe (return l)),
                          (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                 fe1 <- genExpr (n `div` 2) (Arr st1 NumT) ctx
                                 fe2 <- genExpr (n `div` 2) st1 ctx
                                 return $ liftM2 App fe1 fe2),
                          (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                 tmn <- genTmName
                                 fe1 <- genExpr (n `div` 2) st1 ctx
                                 fe2 <- genExpr (n `div` 2) NumT ((tmn, st1) : ctx)
                                 return ( fe1 >>= \e1 ->
                                          fe2 >>= \e2 ->
                                          tmn >>= \mn ->
                                          return $ Let (bind mn (e1, e2)))),
                          (n, do fe1 <- genExpr (n `div` 2) NumT ctx
                                 fe2 <- genExpr (n `div` 2) NumT ctx
                                 fop <- fmap (return . Arith) arbitrary
                                 return $ liftM3 PrimOp fop fe1 fe2),
                          (n, do fe1 <- genExpr (n `div` 2) BoolT ctx
                                 fe2 <- genExpr (n `div` 2) NumT ctx
                                 fe3 <- genExpr (n `div` 2) NumT ctx
                                 return $ liftM3 If fe1 fe2 fe3)
                                 ]
        BoolT -> frequency [ (1, fmap (return . BoolV ) arbitrary),
                             (n, do return $ liftM Var tmn1),
                             (n, do l  <- genLabel
                                    fe <- genExpr (n `div` 2) (SRecT l BoolT) ctx
                                    return $ liftM2 Proj fe (return l)),
                             (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                    fe1 <- genExpr (n `div` 2) (Arr st1 BoolT) ctx
                                    fe2 <- genExpr (n `div` 2) st1 ctx
                                    return $ liftM2 App fe1 fe2),
                             (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                    tmn <- genTmName
                                    fe1 <- genExpr (n `div` 2) st1 ctx
                                    fe2 <- genExpr (n `div` 2) BoolT ((tmn, st1) : ctx)
                                    return ( fe1 >>= \e1 ->
                                             fe2 >>= \e2 ->
                                             tmn >>= \mn ->
                                             return $ Let (bind mn (e1, e2)))),
                             (n, do fe1 <- genExpr (n `div` 2) NumT ctx
                                    fe2 <- genExpr (n `div` 2) NumT ctx
                                    fop <- fmap (return . Comp) arbitrary
                                    return $ liftM3 PrimOp fop fe1 fe2),
                             (n, do fe1 <- genExpr (n `div` 2) BoolT ctx
                                    fe2 <- genExpr (n `div` 2) BoolT ctx
                                    fop <- fmap (return . Logical) arbitrary
                                    return $ liftM3 PrimOp fop fe1 fe2),
                             (n, do fe1 <- genExpr (n `div` 2) BoolT ctx
                                    fe2 <- genExpr (n `div` 2) BoolT ctx
                                    fe3 <- genExpr (n `div` 2) BoolT ctx
                                    return $ liftM3 If fe1 fe2 fe3)
                                    ]
        Arr t1 t2 -> frequency [(n, do return $ liftM Var tmn1),
                                (n, do tmn <- genTmName
                                       fe  <- genExpr (n `div` 2) t2 ((tmn, t1) : ctx)
                                       return ( fe  >>= \e ->
                                                tmn >>= \mn ->
                                                return $ Lam (bind mn e))),
                                (n, do l  <- genLabel
                                       fe <- genExpr (n `div` 2) (SRecT l (Arr t1 t2)) ctx
                                       return $ liftM2 Proj fe (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fe1 <- genExpr (n `div` 2) (Arr st1 (Arr t1 t2)) ctx
                                       fe2 <- genExpr (n `div` 2) st1 ctx
                                       return $ liftM2 App fe1 fe2),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       tmn <- genTmName
                                       fe1 <- genExpr (n `div` 2) st1 ctx
                                       fe2 <- genExpr (n `div` 2) (Arr t1 t2) ((tmn, st1) : ctx)
                                       return ( fe1 >>= \e1 ->
                                                fe2 >>= \e2 ->
                                                tmn >>= \mn ->
                                                return $ Let (bind mn (e1, e2))))
                                      ]
        And t1 t2 -> frequency [(n, do return $ liftM Var tmn1),
                                (n, do fe1 <- genExpr (n `div` 2) t1 ctx
                                       fe2 <- genExpr (n `div` 2) t2 ctx
                                       return $ liftM2 Merge fe1 fe2),
                                (n, do l  <- genLabel
                                       fe <- genExpr (n `div` 2) (SRecT l (And t1 t2)) ctx
                                       return $ liftM2 Proj fe (return l)),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       fe1 <- genExpr (n `div` 2) (Arr st1 (And t1 t2)) ctx
                                       fe2 <- genExpr (n `div` 2) st1 ctx
                                       return $ liftM2 App fe1 fe2),
                                (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                       tmn <- genTmName
                                       fe1 <- genExpr (n `div` 2) st1 ctx
                                       fe2 <- genExpr (n `div` 2) (And t1 t2) ((tmn, st1) : ctx)
                                       return ( fe1 >>= \e1 ->
                                                fe2 >>= \e2 ->
                                                tmn >>= \mn ->
                                                return $ Let (bind mn (e1, e2))))
                                      ]
        SRecT l t1 -> frequency [(n, do return $ liftM Var tmn1),
                                 (n, do fe <- genExpr (n `div` 2) t1 ctx
                                        return $ (Rec l) <$> fe),
                                 (n, do l1 <- genLabel
                                        fe <- genExpr (n `div` 2) (SRecT l1 (SRecT l t1)) ctx
                                        return $ liftM2 Proj fe (return l1)),
                                 (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                        fe1 <- genExpr (n `div` 2) (Arr st1 (SRecT l t1)) ctx
                                        fe2 <- genExpr (n `div` 2) st1 ctx
                                        return $ liftM2 App fe1 fe2),
                                 (n, do st1 <- runFreshM <$> genSType (n `div` 2)
                                        tmn <- genTmName
                                        fe1 <- genExpr (n `div` 2) st1 ctx
                                        fe2 <- genExpr (n `div` 2) (SRecT l t1) ((tmn, st1) : ctx)
                                        return ( fe1 >>= \e1 ->
                                                 fe2 >>= \e2 ->
                                                 tmn >>= \mn ->
                                                 return $ Let (bind mn (e1, e2))))
                                       ]
        _ -> frequency [(1, fmap (return . BoolV) arbitrary),
                        (1, fmap (return . LitV ) arbitrary),
                        (1, do return $ liftM Var tmn1)]

-- Generate record labels
genLabel :: Gen Label
genLabel = elements ['a' .. 'z'] >>= \n -> return [n]

-- Generate fresh type variable names
genTyName :: Gen (FreshM TyName)
genTyName = return $ fresh (N.Fn "u" 0)

-- Generate fresh term variable names
genTmName :: Gen (FreshM TmName)
genTmName = return $ fresh (N.Fn "x" 0)

-- Generate operations
genOperation :: Gen Operation
genOperation = oneof [liftM Arith arbitrary,
                      liftM Comp arbitrary,
                      liftM Logical arbitrary]

-------------
-- PROPERTIES
-------------
instance Testable a => Testable (IO a) where
  property = ioProperty

-- The soundness property
prop_soundness :: Expr -> IO Bool
prop_soundness e = do
  res1 <- runTcMonad emptyCtx $ topLevelInfer $ e
  case res1 of
    Left _ -> return True
    Right (scheme, fexpr) -> do
      res2 <- runTcMonad emptyCtx $ bidirect fexpr
      case res2 of
        Left _ -> return False
        Right (ftype, texpr) -> return True

-- The completeness property
prop_completeness :: Derivation -> IO Bool
prop_completeness d = do
  res1 <- runTcMonad emptyCtx $ extractor d
  case res1 of
    Left _ -> return True
    Right (expr, ty1) -> do
      res2 <- runTcMonad emptyCtx $ topLevelInfer expr
      case res2 of
        Left _ -> return False
        Right (scheme, fexpr) -> do
          return True

-- The principality property (not finished)
prop_principality :: Derivation -> IO Bool
prop_principality d = do
  res1 <- runTcMonad emptyCtx $ extractor d
  case res1 of
    Left _ -> return True
    Right (expr, ty1) -> do
      res2 <- runTcMonad emptyCtx $ topLevelInfer expr
      case res2 of
        Left _ -> return False
        Right (scheme, fexpr) -> do
          b <- runTcMonad emptyCtx $ instanceOfScheme ty1 scheme []
          case b of
            Left _ -> return False
            Right bl -> return bl

-------------
-- ARBITRARY
-------------
instance Arbitrary ArithOp where
  arbitrary = elements [Add, Sub, Mul, Div]

instance Arbitrary CompOp where
  arbitrary = elements [Lt, Gt, Equ, Neq]

instance Arbitrary LogicalOp where
  arbitrary = elements [LAnd, LOr]

instance Arbitrary SType where
  arbitrary = sized $ \i -> runFreshM <$> genSType i

instance Arbitrary Expr where
  arbitrary = sized $ \i -> runFreshM <$> genSType i >>= \t
                         -> runFreshM <$> genExpr i t []

instance Arbitrary Derivation where
  arbitrary = sized $ \i -> runFreshM <$> genSType i >>= \t
                         -> runFreshM <$> genDerivation i t []

----------------
-- SUBSTITUTIONS
----------------

-- substitute a given type variable alpha with type t in the given monotype
substitute :: TyName -> SType -> SType -> SType
substitute alph t (Arr t1 t2)  = Arr (substitute alph t t1) (substitute alph t t2)
substitute alph t (And t1 t2)  = And (substitute alph t t1) (substitute alph t t2)
substitute alph t (TVar x)     | x == alph = t
substitute alph t (SRecT l t1) = SRecT l (substitute alph t t1)
substitute _    _  a           = a

-- substitute a given type variable alpha with type t in the given type scheme
substituteScheme :: TyName -> SType -> Scheme -> STcMonad Scheme
substituteScheme alph t (SType ty) = return $ SType (substitute alph t ty)
substituteScheme alph t (DForall b) = do
  ((alph1, Embed t1), a1) <- unbind b
  a1' <- substituteScheme alph t a1
  return $ DForall (bind (alph1, Embed t1) a1')


--------
-- OTHER
--------

-- pick a term variable name from the list with the given type
pick :: SType -> [(FreshM TmName, SType)] -> Maybe (FreshM TmName)
pick _ [] = Nothing
pick t ((tmn, st):rest) = if t == st then Just tmn else pick t rest

-- check if the given type scheme contains type variable alph
contains :: Scheme -> TyName -> STcMonad Bool
contains (SType (TVar alph1)) alph | alph1 == alph = return $ True
contains (SType (Arr t1 t2)) alph = do
  b1 <- contains (SType t1) alph
  b2 <- contains (SType t2) alph
  return $ b1 || b2
contains (SType (And t1 t2)) alph = do
  b1 <- contains (SType t1) alph
  b2 <- contains (SType t2) alph
  return $ b1 || b2
contains (SType (SRecT l t)) alph = do
  b <- contains (SType t) alph
  return $ b
contains (SType _) alph = return $ False
contains (DForall b) alph = do
  ((alph1, Embed t1), a1) <- unbind b
  b1 <- contains a1 alph
  return $ b1

-- Extract the type and term from a given PHiDI specification
extractor :: Derivation -> STcMonad (Expr, Scheme)
extractor  DTop     = return (Top, SType TopT)
extractor (DNum i)  = return (LitV i, SType NumT)
extractor (DBool b) = return (BoolV b, SType BoolT)
extractor (DVar x)  = lookupVarTy x >>= \ty -> case ty of
    CtxUni u   -> errThrow [DS "DVar: Variable not found in term context"]
    CtxSch sch -> return (Var x, sch)
extractor (DApp d1 d2) = extractor d1 >>= \(e1, a1) -> case a1 of
    SType (Arr t1 t2) -> extractor d2 >>= \(e2, a2) -> case a2 of
      SType t3 -> if (t1 == t3)
                  then (return (App e1 e2, SType t2))
                  else errThrow [DS "DApp: No corresponding types"]
      _        -> errThrow [DS "DApp: Type scheme instead of monotype"]
    _                 -> errThrow [DS "DApp: Should be a function type"]
extractor (DAbs d x t1) = localCtx (extendVarCtx x (CtxSch (SType t1))) $ extractor d >>= \(e, a2) -> case a2 of
    SType t2 -> return (Lam (bind x e), SType (Arr t1 t2))
    _        -> errThrow [DS "DAbs: Type scheme instead of monotype"]
extractor (DRec d l) = extractor d >>= \(e, a) -> case a of
    SType t -> return (Rec l e, SType (SRecT l t))
    _       -> errThrow [DS "DRec: Type scheme instead of monotype"]
extractor (DProj d l) = extractor d >>= \(e, a) -> case a of
    SType (SRecT l1 t) -> if (l == l1)
                          then return (Proj e l, SType t)
                          else errThrow [DS "DProj: Not the same label"]
    _                  -> errThrow [DS "DProj: No record type"]
extractor (DMerge d1 d2) = extractor d1 >>= \(e1, a1) -> case a1 of
      SType t1 -> extractor d2 >>= \(e2, a2) -> case a2 of
        SType t2 -> do
          ctx <- askCtx
          disjoint ctx t1 t2
          return (Merge e1 e2, SType (And t1 t2))
        _        -> errThrow [DS "DMerge: Type scheme instead of monotype"]
      _        -> errThrow [DS "DMerge: Type scheme instead of monotype"]
extractor (DTAbs d alph t) = do
    (e, a) <- localCtx (extendConstrainedSTVarCtx alph t) $ extractor d
    wfSType t
    b <- contains a alph
    if b then return (e, DForall (bind (alph, Embed t) a))
                       else errThrow [DS "Ambiguous term"]
extractor (DTApp d ty) = extractor d >>= \(e, a1) -> case a1 of
    DForall b -> do
      ((alph, Embed t), a2) <- unbind b
      ctx <- askCtx
      disjoint ctx ty t
      a2' <- substituteScheme alph ty a2
      return (e, a2')
    _ -> errThrow [DS "DTApp: Monotype instead of type scheme"]
extractor (DSub d t2) = extractor d >>= \(e, a1) -> case a1 of
    SType t1 -> do
      ctx <- askCtx
      let _ = subtype ctx (SType t1) (SType t2)
      return (e, SType t2)
    _ -> errThrow [DS "DSub: Type scheme instead of monotype"]
extractor (DLet x d1 d2) = extractor d1 >>= \(e1, a1) ->
      localCtx (extendVarCtx x (CtxSch a1)) $ extractor d2 >>= \(e2, a2) -> case a2 of
      SType t2 -> return (Let (bind x (e1, e2)), SType t2)
      _        -> errThrow [DS "DLet: Type scheme instead of monotype"]


-- Check if a given type scheme is an instance of another type scheme
-- This will be used for the property of principality
instanceOfScheme :: Scheme -> Scheme -> [(TyName, TyName)] -> STcMonad Bool
instanceOfScheme (SType t1)   (SType t2)   l = return $ isInstanceOf t1 t2 l
instanceOfScheme (DForall b1) (DForall b2) l = do
  ((alph1, Embed t1), a1) <- unbind b1
  ((alph2, Embed t2), a2) <- unbind b2
  if isInstanceOf t1 t2 l
    then instanceOfScheme a1 a2 ((alph1, alph2):l)
    else return $ False
instanceOfScheme  _            _           _ = return $ False

-- Check if a given monotype is an instance of another monotype
-- This will be used for the property of principality
isInstanceOf :: SType -> SType -> [(TyName, TyName)] -> Bool
isInstanceOf NumT  NumT  l = True
isInstanceOf BoolT BoolT l = True
isInstanceOf TopT  TopT  l = True
isInstanceOf BotT  BotT  l = True

isInstanceOf (Arr t1 t2)   (Arr t3 t4)   l  = (isInstanceOf t3 t1 l)  && (isInstanceOf t2 t4 l)
isInstanceOf (And t1 t2)   (And t3 t4)   l  = ((isInstanceOf t1 t3 l) && (isInstanceOf t2 t4 l))
                                                        || ((isInstanceOf t1 t4 l) && (isInstanceOf t2 t3 l))
isInstanceOf (SRecT l1 t1) (SRecT l2 t2) l  = (l1 == l2) && (isInstanceOf t1 t2 l)
isInstanceOf (And t1 t2)    t3           l  = (isInstanceOf t1 t3 l) || (isInstanceOf t2 t3 l)

isInstanceOf (TVar x) (TVar y) ((x1, y1):l) = if x == x1
                                              then (if y == y1 then True else False)
                                              else isInstanceOf (TVar x) (TVar y) l
isInstanceOf _ _ _ = False

-- Check if a type scheme is well-formed
wfScheme :: Scheme -> STcMonad ()
wfScheme (SType t) = wfSType t
wfScheme (DForall b) = do
  ((alph, Embed t), a) <- unbind b
  wfSType t
  localCtx (extendConstrainedSTVarCtx alph t) $ wfScheme a

-- Check if a monotype is well-formed
wfSType :: SType -> STcMonad ()
wfSType NumT = return ()
wfSType BoolT = return ()
wfSType TopT = return ()
wfSType BotT = return ()
wfSType (Arr t1 t2) = wfSType t1 >> wfSType t2
wfSType (And t1 t2) = wfSType t2 >> wfSType t2
wfSType (TVar x) = void $ lookupTVarConstraint x
wfSType (SRecT _ t) = wfSType t

-- Check if two monotypes are disjoint in the given context
disjoint :: SCtx -> SType -> SType -> STcMonad ()
disjoint _ TopT _ = return ()
disjoint _ _ TopT = return ()

disjoint _ BotT a = do
  let isTop = topLike a
  if isTop
    then return ()
    else errThrow
           [ DS $
             "Bottom is only disjoint to top-like types, but" <+>
             Pretty.squotes (pprint a) <+> "is not top-like"
           ]
disjoint _ a BotT = do
  let isTop = topLike a
  if isTop
    then return ()
    else errThrow
           [ DS $
             "Bottom is only disjoint to top-like types, but" <+>
             Pretty.squotes (pprint a) <+> "is not top-like"
           ]

disjoint ctx (TVar x) b
  | Just a <- lookupTVarConstraintMaybe ctx x
  , Right _ <- subtype ctx (SType a) (SType b) = return ()
disjoint ctx b (TVar x)
  | Just a <- lookupTVarConstraintMaybe ctx x
  , Right _ <- subtype ctx (SType a) (SType b) = return ()
disjoint _ (TVar x) (TVar y) =
  errThrow
    [ DS $
      "FType variables" <+>
      Pretty.pretty x <+> "and" <+> Pretty.pretty y <+> "are not disjoint"
    ]
disjoint ctx tm1@(SRecT l a) tm2@(SRecT l' b) =
  when (l == l') $
  disjoint ctx a b `catchError`
  const
    (errThrow
       [ DS $
         Pretty.squotes (pprint tm1) <+>
         "and" <+> Pretty.squotes (pprint tm2) <+> "are not disjoint"
       ])

disjoint ctx (Arr _ a2) (Arr _ b2) = disjoint ctx a2 b2
disjoint ctx (And a1 a2) b = do
  disjoint ctx a1 b
  disjoint ctx a2 b
disjoint ctx a (And b1 b2) = do
  disjoint ctx a b1
  disjoint ctx a b2
disjoint _ a b =
  unless (disjointAx a b) $
  errThrow
    [ DS $
      Pretty.squotes (pprint a) <+>
      "and" <+> Pretty.squotes (pprint b) <+> "are not disjoint"
    ]

-- axiomatic disjointness
disjointAx :: SType -> SType -> Bool
disjointAx t1 t2 =
  type2num t1 < 4 && type2num t2 < 4 && type2num t1 /= type2num t2
  where
    type2num :: SType -> Int
    type2num NumT = 0
    type2num BoolT = 1
    type2num Arr {} = 2
    type2num SRecT {} = 3
    -- The above are basic type
    type2num TopT {} = 4
    type2num And {} = 5
    type2num TVar {} = 6
    type2num BotT {} = 7

--------
-- MAIN
--------
test_soundness :: IO ()
test_soundness = quickCheck (prop_soundness :: Expr -> IO Bool)

test_completeness :: IO ()
test_completeness = quickCheck (prop_completeness :: Derivation -> IO Bool)

test_principality :: IO ()
test_principality = quickCheck (prop_principality :: Derivation -> IO Bool)
