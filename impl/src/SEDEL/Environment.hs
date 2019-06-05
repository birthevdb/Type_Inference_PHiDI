{-# LANGUAGE GADTs, OverloadedStrings, FlexibleContexts, NoImplicitPrelude, RankNTypes #-}

module SEDEL.Environment where


import qualified Data.Map.Strict as M
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Protolude
import           Text.Megaparsec
import           Unbound.Generics.LocallyNameless

import qualified SEDEL.Source.Syntax as S
import qualified SEDEL.Intermediate.Syntax as I
import           SEDEL.PrettyPrint

type TcMonad tm_name scheme ty_name kind typ exp = FreshMT (ReaderT (Ctx tm_name scheme ty_name kind typ exp) (ExceptT Err IO))

runTcMonad :: Ctx tm_name scheme ty_name kind typ exp -> TcMonad tm_name scheme ty_name kind typ exp a -> IO (Either Err a)
runTcMonad env m = runExceptT $ runReaderT (runFreshMT m) env

-- | `TypeValue` is what's put inside a type context.
data TypeValue typ
  = TerminalType
  -- ^ Terminal types, e.g., the `a` of `forall a. `
  | NonTerminalType typ
  -- ^ Non-terminal types, i.e. type synoyms. `SType` holds the RHS to the
  -- equal sign of type synonym definitions.
  -- | `TypeValue` is what's put inside a type context.
  deriving Show

-- | (Polymorphic) environment manipulation and accessing functions
data Ctx tm_name scheme ty_name kind typ exp = Ctx
  { varCtx :: M.Map tm_name scheme
  , tyCtx :: M.Map ty_name (kind, typ, TypeValue typ)
  , bndCtx :: M.Map tm_name exp
  , sourceLocation :: [SourceLocation]
  }

type SCtx = Ctx S.TmName S.CtxType S.TyName S.Kind S.SType S.Expr
type STcMonad = TcMonad S.TmName S.CtxType S.TyName S.Kind S.SType S.Expr

type ICtx = Ctx I.TmName I.FType I.TyName I.Kind I.FType I.FExpr
type ITcMonad = TcMonad I.TmName I.FType I.TyName I.Kind I.FType I.FExpr

askCtx :: TcMonad tm_name scheme ty_name kind typ exp (Ctx tm_name scheme ty_name kind typ exp)
askCtx = ask

localCtx :: (Ctx tm_name scheme ty_name kind typ exp -> Ctx tm_name scheme ty_name kind typ exp ) -> TcMonad tm_name scheme ty_name kind typ exp a -> TcMonad tm_name scheme ty_name kind typ exp a
localCtx = local

emptyCtx :: Ctx tm_name scheme ty_name kind typ exp
emptyCtx =
  Ctx {varCtx = M.empty, tyCtx = M.empty, bndCtx = M.empty, sourceLocation = []}

ctxMap :: (M.Map tm_name scheme -> M.Map tm_name scheme)
       -> (M.Map ty_name (kind, typ, TypeValue typ) -> M.Map ty_name (kind, typ, TypeValue typ))
       -> (M.Map tm_name exp -> M.Map tm_name exp)
       -> Ctx tm_name scheme ty_name kind typ exp
       -> Ctx tm_name scheme ty_name kind typ exp
ctxMap f1 f2 f3 ctx =
  Ctx
  { varCtx = f1 (varCtx ctx)
  , tyCtx = f2 (tyCtx ctx)
  , bndCtx = f3 (bndCtx ctx)
  , sourceLocation = sourceLocation ctx
  }

extendVarCtx :: Ord tm_name => tm_name -> scheme -> Ctx tm_name scheme ty_name kind typ exp -> Ctx tm_name scheme ty_name kind typ exp
extendVarCtx v t = ctxMap (M.insert v t) identity identity

extendTVarCtx :: I.TyName -> I.Kind -> ICtx -> ICtx
extendTVarCtx v k = ctxMap identity (M.insert v (k, I.TopT, TerminalType)) identity

extendConstrainedTVarCtx :: I.TyName -> I.FType -> ICtx -> ICtx
extendConstrainedTVarCtx v t = ctxMap identity (M.insert v (I.Star, t, TerminalType)) identity

extendConstrainedSTVarCtx :: S.TyName -> S.SType -> SCtx -> SCtx
extendConstrainedSTVarCtx v t = ctxMap identity (M.insert v (S.Star, t, TerminalType)) identity

extendVarCtxs :: Ord tm_name => [(tm_name, scheme)] -> Ctx tm_name scheme ty_name kind typ exp -> Ctx tm_name scheme ty_name kind typ exp
extendVarCtxs = flip $ foldr (uncurry extendVarCtx)

addTypeSynonym :: Ord ty_name => ty_name -> typ -> kind -> Ctx tm_name scheme ty_name kind typ exp -> Ctx tm_name scheme ty_name kind typ exp
addTypeSynonym v t k = ctxMap identity (M.insert v (k, t, NonTerminalType t)) identity

addTypeSynonyms :: Ord ty_name => [(ty_name, typ, kind)] -> Ctx tm_name scheme ty_name kind typ exp -> Ctx tm_name scheme ty_name kind typ exp
addTypeSynonyms = flip $ foldr (\(v, t, k) ctx -> addTypeSynonym v t k ctx)

lookupVarTy :: (Ord tm_name, Pretty.Pretty tm_name) => (MonadReader (Ctx tm_name scheme ty_name kind typ exp) m, MonadError Err m) => tm_name -> m scheme
lookupVarTy v = do
  env <- asks varCtx
  case M.lookup v env of
    Nothing -> errThrow [DS $ "Not in scope:" <+> Pretty.pretty v]
    Just res -> return res

lookupTVarConstraint :: (Ord ty_name, Pretty.Pretty ty_name) => (MonadReader (Ctx tm_name scheme ty_name kind typ exp) m, MonadError Err m) => ty_name -> m typ
lookupTVarConstraint v = do
  env <- asks tyCtx
  case M.lookup v env of
    Nothing  -> errThrow [DS $ "Not in scope:" <+> Pretty.pretty v]
    Just (_, c, _) -> return c

lookupTVarKindMaybe :: (Show ty_name, Show kind, Show typ, Ord ty_name) => Ctx tm_name scheme ty_name kind typ exp -> ty_name -> Maybe kind
lookupTVarKindMaybe ctx v = (\(k, _, _) -> k) <$> M.lookup v (tyCtx ctx)

lookupTVarConstraintMaybe :: Ord ty_name => Ctx tm_name scheme ty_name kind typ exp -> ty_name -> Maybe typ
lookupTVarConstraintMaybe ctx v =
  (\(_, t, _) -> t) <$> M.lookup v (tyCtx ctx)

lookupTVarSynMaybe :: Ord ty_name => Ctx tm_name scheme ty_name kind typ exp -> ty_name -> Maybe typ
lookupTVarSynMaybe ctx v =
  case (\(_, _, t) -> t) <$> M.lookup v (tyCtx ctx) of
    Nothing -> Nothing
    Just TerminalType -> Nothing
    Just (NonTerminalType t) -> Just t

lookupTmDef :: Ord tm_name => (MonadReader (Ctx tm_name scheme ty_name kind typ exp) m) => tm_name -> m (Maybe exp)
lookupTmDef v = M.lookup v <$> asks bndCtx

-- | Push a new source position on the location stack.
extendSourceLocation ::
     (MonadReader (Ctx tm_name scheme ty_name kind typ exp) m, FPretty t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t =
  local (\ e@Ctx {sourceLocation = locs} -> e {sourceLocation = SourceLocation p t:locs})


-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. FPretty a => SourcePos -> a -> SourceLocation

-- | An error that should be reported to the user
data Err = Err [SourceLocation] FDoc

instance Semigroup Err where
  (Err src1 d1 ) <> (Err src2 d2) = Err (src1 ++ src2) (d1 <> d2)

instance Monoid Err where
  mempty = Err [] mempty
  mappend = (<>)


instance FPretty Err where
  ppr (Err [] msg) = return msg
  ppr (Err (SourceLocation p term:_) msg) = do
    trm <- ppr term
    return $
      Pretty.vsep [Pretty.pretty p, msg, "In the expression:", trm]


-- | Throw an error
errThrow :: (FPretty a, MonadError Err m, MonadReader (Ctx tm_name scheme ty_name kind typ exp) m) => a -> m b
errThrow d = do
  loc <- getSourceLocation
  throwError $ Err loc (pprint d)


-- | access current source location
getSourceLocation :: MonadReader (Ctx tm_name scheme ty_name kind typ exp) m => m [SourceLocation]
getSourceLocation = asks sourceLocation
