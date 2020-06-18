
import           Control.Monad
import           Test.QuickCheck
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Name as N

import           ConstraintChecker
import           Syntax
import           Unification
import           Util

import           Debug.Trace                           as DT


main :: IO ()
main = verboseCheck (withMaxSuccess 1000 propCons)

propCons :: Type -> Type -> Bool
propCons t1 t2 = DT.trace ("subs:   " ++ show subs ++
                           "\nts:     " ++ show ts ++
                           "\nvalid:  " ++ show valid) $
    if null subs then not $ constraintCheck t1 t2 else foldr (&&) True valid
  where subs  = checkSubtyping t1 t2
        ts    = map (\sub -> applySubst sub t1 t2) subs
        valid = map (\(t1', t2') -> constraintCheck t1' t2') ts


-- Generate PHiDI types
genType :: Int -> Gen Type
genType n = frequency [ (4, elements [Nat, Bool, Top, Bot]),
                        (n, (liftM Var) genTyName),
                        (n, (liftM Uni) genTUni),
                        (n, do ft <- genType (n `div` 2)
                               l  <- genLabel
                               return $ Rec l ft),
                        (n, do ft1 <- genType (n `div` 2)
                               ft2 <- genType (n `div` 2)
                               return $ And ft1 ft2),
                        (n, do ft1 <- genType (n `div` 2)
                               ft2 <- genType (n `div` 2)
                               return $ Arr ft1 ft2)
                       ]

instance Arbitrary Type where
  arbitrary = sized $ \i -> genType i

-- Generate record labels
genLabel :: Gen Label
genLabel = elements ['a' .. 'z'] >>= \n -> return [n]

-- Generate fresh type variable names
genTyName :: Gen TyName
genTyName = choose (0, 4) >>= \n -> return $ N.makeName "A" n

-- Generate fresh type variable names
genTUni :: Gen TUni
genTUni = choose (0, 4) >>= \n -> return $ N.makeName "u" n
