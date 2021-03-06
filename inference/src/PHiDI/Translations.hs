module PHiDI.Translations where

import           PHiDI.Environment
import           PHiDI.Fix
import           PHiDI.Intermediate.Syntax             as I
import           PHiDI.Source.Syntax                   as S

import qualified Data.Map.Strict                       as M
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Name

-- | Change the sort of a name.
translate :: Name a -> Name b
translate (Fn x y) = Fn x y
translate (Bn x y) = Bn x y


sCtxtoICtx :: Fresh m => SCtx -> m ICtx
sCtxtoICtx (Ctx var ty bnd src) = do
  ivar <- (translVarCtx var)
  ity <- (translTyCtx ty)
  ibnd <- (translBndCtx bnd)
  return $ Ctx ivar ity ibnd src


translVarCtx :: Fresh m => M.Map S.TmName S.CtxType -> m (M.Map I.TmName I.FType)
translVarCtx m | M.null m = return M.empty
translVarCtx m = do
  let ((n, sch): ls) = M.toList m
  let n' = translate n
  sch' <- translCtxType sch
  let m' = M.fromList ls
  im <- translVarCtx m'
  return $ M.insert n' sch' im


translTyCtx :: Fresh m => M.Map S.TyName (S.Kind, S.SType, TypeValue S.SType) -> m (M.Map I.TyName (I.Kind, I.FType, TypeValue I.FType))
translTyCtx m | M.null m = return M.empty
translTyCtx m = do
  let ((n, (k, ty, val)):ls) = M.toList m
  let n' = translate n
  let k' = translKind k
  ty' <- translSType ty
  val' <- translTypeValue val
  let m' = M.fromList ls
  im <- translTyCtx m'
  return $ M.insert n' (k', ty', val') im


translBndCtx :: Fresh m => M.Map S.TmName S.Expr -> m (M.Map I.TmName I.FExpr)
translBndCtx m | M.null m = return M.empty
translBndCtx m = do
  let ((n, e):ls) = M.toList m
  let n' = translate n
  e' <- translExp e
  let m' = M.fromList ls
  im <- translBndCtx m'
  return $ M.insert n' e' im


translTypeValue :: Fresh m => TypeValue S.SType -> m (TypeValue I.FType)
translTypeValue TerminalType         = return TerminalType
translTypeValue (NonTerminalType ty) = translSType ty >>= \ty' -> return $ NonTerminalType ty'


-- Translation function for types
translType :: Fresh m => S.Scheme -> m I.FType
translType (S.DForall b) = do
  ((alph, Embed t1), a2) <- unbind b
  a1' <- translType (S.SType t1)
  a2' <- translType a2
  return $ I.DForall (bind (translate alph, embed a1') a2')
translType (S.SType t) = translSType t

translCtxType :: Fresh m => S.CtxType -> m I.FType
translCtxType (CtxSch _ ty) = translPType ty

translSType :: Fresh m => S.SType -> m I.FType
translSType = cata sAlg

sAlg :: Fresh m => S.SType' (m I.FType) -> m I.FType
sAlg (S.TVar x)    = return $ I.TVar (translate x)
sAlg S.NumT        = return $ I.NumT
sAlg S.BoolT       = return $ I.BoolT
sAlg S.TopT        = return $ I.TopT
sAlg S.BotT        = return $ I.BotT
sAlg (S.Arr t1 t2) = I.Arr <$> t1 <*> t2
sAlg (S.And t1 t2) = I.And <$> t1 <*> t2
sAlg (S.SRecT l t) = I.SRecT l <$> t

aAlg :: Fresh m => S.AType' (m I.FType) -> m I.FType
aAlg (S.Uni u) = return $ I.TVar (translate u)

translPType :: Fresh m => S.PType -> m I.FType
translPType = cata (sAlg `composeAlg` aAlg)

-- Translation function for expressions
translExp :: Fresh m => S.Expr -> m I.FExpr
translExp (S.Var n) = return $ I.Var (translate n)
translExp (S.VarPoly n) = return $ I.Var (translate n)
translExp (S.App e1 e2) = do
  e1' <- translExp e1
  e2' <- translExp e2
  return $ I.App e1' e2'
translExp (S.Lam b) = do
  (n, e) <- unbind b
  e' <- translExp e
  return $ I.Lam (bind (translate n) e')
translExp (S.Let b) = do
  (x, (e1, e2)) <- unbind b
  e1' <- translExp e1
  e2' <- translExp e2
  return $ I.Letrec (bind (translate x, embed Nothing) (e1', e2'))
translExp (S.Letrec b) = do
  ((x, Embed a), (e1, e2)) <- unbind b
  e1' <- translExp e1
  e2' <- translExp e2
  a'  <- translType a
  return $ I.Letrec (bind (translate x, embed (Just a')) (e1', e2'))
translExp (S.Rec l e) = do
  e' <- translExp e
  return $ I.Rec l e'
translExp (S.Proj e l) = do
  e' <- translExp e
  return $ I.Acc e' l
translExp (S.Merge e1 e2) = do
  e1' <- translExp e1
  e2' <- translExp e2
  return $ I.Merge e1' e2'
translExp (S.LitV d) = return $ I.LitV d
translExp (S.BoolV b) = return $ I.BoolV b
translExp (S.PrimOp op e1 e2) = do
  e1' <- translExp e1
  e2' <- translExp e2
  return $ I.PrimOp op e1' e2'
translExp (S.If e1 e2 e3) = do
  e1' <- translExp e1
  e2' <- translExp e2
  e3' <- translExp e3
  return $ I.If e1' e2' e3'
translExp S.Top = return $ I.Top
translExp (S.Pos p e) = do
  e' <- translExp e
  return $ I.Pos p e'
translExp (S.DRec' b) = do
  b' <- translTmBind b
  return $ I.DRec' b'


-- Translation function for TmBind
translTmBind :: Fresh m => S.TmBind -> m I.TmBind
translTmBind (S.TmBind f typars pars e Nothing b) = do
  typars' <- translTyPars typars
  pars' <- translPars pars
  e' <- translExp e
  return $ I.TmBind f typars' pars' e' Nothing b
translTmBind (S.TmBind f typars pars e (Just sch) b) = do
  typars' <- translTyPars typars
  pars' <- translPars pars
  e' <- translExp e
  sch' <- translType sch
  return $ I.TmBind f typars' pars' e' (Just sch') b


translTyPars :: Fresh m => [(S.TyName, S.SType)] -> m [(I.TyName, I.FType)]
translTyPars [] = return $ []
translTyPars ((n, t):pars) = do
  t' <- translSType t
  pars' <- translTyPars pars
  return $ (translate n, t') : pars'


translPars :: Fresh m => [(S.TmName, Maybe S.Scheme)] -> m [(I.TmName, Maybe I.FType)]
translPars [] = return $ []
translPars ((n, Nothing):pars) = translPars pars >>= \pars' ->
                             return $ (translate n, Nothing) : pars'
translPars ((n, Just ty):pars) = do
  ty' <- translType ty
  pars' <- translPars pars
  return $ (translate n, Just ty') : pars'


-- Translation function for kinds
translKind :: S.Kind -> I.Kind
translKind S.Star           = I.Star
translKind (S.KArrow k1 k2) = I.KArrow (translKind k1) (translKind k2)
