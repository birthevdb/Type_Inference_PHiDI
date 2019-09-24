{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module SEDEL.Source.Subtyping
  ( subtype
  ) where


import           Data.Sequence ((|>), Seq(..))
import qualified Data.Sequence as Q
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Text.Prettyprint.Doc ((<+>))
import           Protolude
import           Unbound.Generics.LocallyNameless

import           SEDEL.Environment
import           SEDEL.PrettyPrint
import           SEDEL.Source.Syntax
import           SEDEL.Source.Desugar
import qualified SEDEL.Target.Syntax as T

data L = LTy SType | LLa Label | LAll TyName SType

{- |

----------------------------
-- Coercion
----------------------------

-}
type Co = T.UExpr


coId :: Co
coId = T.elam "x" (T.evar "x")

coTrans :: Co -> Co -> Co
coTrans c1 c2 = T.elam "x" (T.eapp c1 (T.eapp c2 (T.evar "x")))

coTop :: Co
coTop = T.elam "x" T.UUnit

coTopArr :: Co
coTopArr = T.elam "x" (T.elam "y" T.UUnit)

coArr :: Co -> Co -> Co
coArr c1 c2 =
  let body = T.eapp c2 (T.eapp (T.evar "f") (T.eapp c1 (T.evar "x")))
  in T.elam "f" (T.elam "x" body)

coPair :: Co -> Co -> Co
coPair c1 c2 =
  T.elam "x" (T.UPair (T.eapp c1 (T.evar "x")) (T.eapp c2 (T.evar "x")))


coProj1 :: Co
coProj1 = T.elam "x" (T.UP1 (T.evar "x"))


coProj2 :: Co
coProj2 = T.elam "x" (T.UP2 (T.evar "x"))


coDistArr :: Co
coDistArr = T.elam "x" (T.elam "y" $ T.UPair
                     (T.eapp (T.UP1 (T.evar "x")) (T.evar "y"))
                     (T.eapp (T.UP2 (T.evar "x")) (T.evar "y")))



{- |

----------------------------
-- Meta-function
----------------------------

-}
calTop :: Seq L -> Co
calTop Empty = coTop
calTop (LLa _ :<| fs) = coTrans (calTop fs) coId
calTop (LTy _ :<| fs) =
  coTrans (coArr coTop (calTop fs)) coTopArr
calTop (LAll _ _ :<| fs) = coTrans (calTop fs) coId

calAnd :: Seq L -> Co
calAnd Empty = coId
calAnd (LLa _ :<| fs) = coTrans (calAnd fs) coId
calAnd (LTy _ :<| fs) = coTrans (coArr coId (calAnd fs)) coDistArr
calAnd (LAll _ _ :<| fs) = coTrans (calAnd fs) coId



{- |

----------------------------
-- A <: B ~> E
----------------------------

Subtyping (<:) is defined only between types of kind *.
WARN: They must be expanded first

-}

subtype :: SCtx -> Scheme -> Scheme -> Either FDoc T.UExpr
subtype ctx st tt = runExcept $ runFreshMT go
  where
    go :: (FreshMT (Except FDoc)) T.UExpr
    go = do
      let a = expandType ctx st
      let b = expandType ctx tt
      subtypeS Q.empty a b
    subtypeS :: Q.Seq L -> Scheme -> Scheme -> (FreshMT (Except FDoc)) T.UExpr
    -- Base cases
    subtypeS Empty (SType NumT) (SType NumT) = return coId
    subtypeS Empty (SType BoolT) (SType BoolT) = return coId
    subtypeS Empty (SType BotT) (SType BotT) = return coId
    subtypeS fs _ (SType TopT) = return $ coTrans (calTop fs) coTop
    subtypeS Empty (SType (TVar a)) (SType (TVar b)) =
      if a /= b
        then throwError $
             "variables not equal:" <+>
             Pretty.squotes (Pretty.pretty a) <+>
             "and" <+> Pretty.squotes (Pretty.pretty b)
        else return coId
    -- NumT
    subtypeS fs (SType (And a1 a2)) (SType NumT) = do
      let c1 = do
            c <- subtypeS fs (SType a1) (SType NumT)
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs (SType a2) (SType NumT)
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (SType (Arr a1 a2)) (SType NumT) = do
      c1 <- subtypeS Q.empty (SType a) (SType a1)
      c2 <- subtypeS fs (SType a2) (SType NumT)
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SType (SRecT l' a)) (SType NumT) =
      if l == l'
        then subtypeS fs (SType a) (SType NumT)
        else throwError $
             "Labels" <+>
             Pretty.squotes (Pretty.pretty l) <+>
             "and" <+> Pretty.squotes (Pretty.pretty l') <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) (SType NumT) = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty (SType a) (SType b')
        subtypeS fs (subst tv' (TVar tv) t) (SType NumT)
    subtypeS _ (SType BotT) (SType NumT) = return T.Bot
    -- BoolT
    subtypeS fs (SType (And a1 a2)) (SType BoolT) = do
      let c1 = do
            c <- subtypeS fs (SType a1) (SType BoolT)
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs (SType a2) (SType BoolT)
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (SType (Arr a1 a2)) (SType BoolT) = do
      c1 <- subtypeS Q.empty (SType a) (SType a1)
      c2 <- subtypeS fs (SType a2) (SType BoolT)
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SType (SRecT l' a)) (SType BoolT) =
      if l == l'
        then subtypeS fs (SType a) (SType BoolT)
        else throwError $
             "Labels" <+>
             Pretty.pretty l <+> "and" <+> Pretty.pretty l' <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) (SType BoolT) = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty (SType a) (SType b')
        subtypeS fs (subst tv' (TVar tv) t) (SType BoolT)
    subtypeS _ (SType BotT) (SType BoolT) = return T.Bot
    -- type variable
    subtypeS fs (SType (And a1 a2)) (SType (TVar x)) = do
      let c1 = do
            c <- subtypeS fs (SType a1) (SType (TVar x))
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs (SType a2) (SType (TVar x))
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (SType (Arr a1 a2)) (SType (TVar x)) = do
      c1 <- subtypeS Q.empty (SType a) (SType a1)
      c2 <- subtypeS fs (SType a2) (SType (TVar x))
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SType (SRecT l' a)) (SType (TVar x)) =
      if l == l'
        then subtypeS fs (SType a) (SType (TVar x))
        else throwError $
             "Labels" <+>
             Pretty.squotes (Pretty.pretty l) <+>
             "and" <+> Pretty.squotes (Pretty.pretty l') <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) (SType (TVar x)) = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty (SType a) (SType b')
        subtypeS fs (subst tv' (TVar tv) t) (SType (TVar x))
    subtypeS _ (SType BotT) (SType (TVar _)) = return T.Bot
    -- Inductive cases
    subtypeS fs (SType a) (SType (And b1 b2)) = do
      c1 <- subtypeS fs (SType a) (SType b1)
      c2 <- subtypeS fs (SType a) (SType b2)
      return $ coTrans (calAnd fs) (coPair c1 c2)
    subtypeS fs (SType a) (SType (Arr b1 b2)) = subtypeS (fs |> LTy b1) (SType a) (SType b2)
    subtypeS fs (SType a) (SType (SRecT l b)) = subtypeS (fs |> LLa l) (SType a) (SType b)
    subtypeS fs (SType a) (DForall b) = do
      ((tv, Embed b'), t) <- unbind b
      subtypeS (fs |> LAll tv b') (SType a) t
    subtypeS _ a b =
      throwError $
      "No subtyping relation between" <+>
      Pretty.squotes (pprint a) <+> "and" <+> Pretty.squotes (pprint b)
