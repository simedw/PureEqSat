{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
module Rule where

import Expr

import Opt hiding (EqRepr)
import Debug.Trace
import Data.Maybe
import Data.List (groupBy,sort, sortBy)
import Control.Monad
import "mtl" Control.Monad.Trans
import Data.List (zipWith4)
import Data.Either
import Data.Function
import qualified Data.Set as S
import Data.Set (Set)

type ID = Int

data Pattern = PExpr (TExpr Pattern)
             | PAny ID
             | PLit Lit Pattern
             | PFun (Lit -> Lit -> Lit) Pattern Pattern

instance Show Pattern where
  show p = case p of
    PExpr t -> "ex: " ++ show t
    PAny i  -> "any " ++ show i

type Constraint = [(ID, EqRepr)] -> Opt Bool
data Rule = Rule Pattern Pattern


(~>) = Rule
infix 0 ~>
forall3 f = f (PAny 1) (PAny 2) (PAny 3)
forall2 f = f (PAny 1) (PAny 2)
forall1 f = f (PAny 1)

rAnd x y  = PExpr (And x y)
rOr x y   = PExpr (Or x y)
rAdd x y  = PExpr (Add x y)
rMul x y  = PExpr (Mul x y)
rInt x    = PExpr (Lit $ LInteger x)
rBool x   = PExpr (Lit $ LBool x)
rTrue     = rBool True
rFalse    = rBool False
rVar x    = PExpr (Var x)
rEq x y   = PExpr (Eq x y)
rIf x y z = PExpr (If x y z)
pInt x    = PLit (LInteger (error "don't peek here")) x
pBool x   = PLit (LBool (error "don't peek here")) x

plus = PFun $ \(LInteger i) (LInteger j) ->  (LInteger $ i + j)
mul  = PFun $ \(LInteger i) (LInteger j) ->  (LInteger $ i * j)
eqI  = PFun $ \(LInteger i) (LInteger j) ->  (LBool $ i == j)
eqB  = PFun $ \(LBool x)    (LBool y)    ->  (LBool $ x == y)

rules :: [(Int,Rule)]
rules = map (\r -> (getRuleDepth r, r)) $
        [ identity rAdd  (rInt 0)
        , identity rMul  (rInt 1)
        , identity rAnd  (rTrue)
        , identity rOr   (rFalse)
        , assoc rAdd
        , assoc rMul
        , assoc rAnd
        , assoc rOr
        , commute rAdd
        , commute rMul
        , commute rAnd
        , commute rOr
        , commute rEq
        , zero rMul (rInt 0)
        , zero rAnd (rFalse)
        , zero rOr  (rTrue)

        , eval (rAdd `on` pInt)  plus pInt
        , eval (rMul `on` pInt)  mul pInt
        , eval (rEq  `on` pInt)  eqI pBool
        , eval (rEq  `on` pBool) eqB pBool

        , distr  rMul rAdd
        , distr' rMul rAdd
        , distr  rAnd rOr
        , distr' rAnd rOr
        , distr  rOr  rAnd
        , distr' rOr  rAnd
        , forall1 $ \x -> x `rEq` x ~> rTrue
        , forall3 $ \x y z -> ((x `rAdd` z) `rEq` (y `rAdd` z)) ~> (x `rEq` y)
        , forall2 $ \x y -> rIf (rTrue) x y ~> x
        , forall2 $ \x y -> rIf (rFalse) x y ~> y
        , forall2 $ \x y -> rIf y x x ~> x
        ] 

distr op1 op2 = forall3 $ \x y z -> x `op1` (y `op2` z) ~> (x `op1` y) `op2` (x `op1` z)
distr' op1 op2 = forall3 $ \x y z -> (x `op1` y) `op2` (x `op1` z) ~> x `op1` (y `op2` z) 
zero op v     = forall1 $ \x -> (x `op` v) ~> v
identity op v = forall1 $ \x -> (x `op` v) ~> x        
commute op    = forall2 $ \x y -> (x `op` y) ~> (y `op` x)
assoc op      = forall3 $ \x y z -> ((x `op` y) `op` z) ~> (x `op` (y `op` z))
eval op sop res = forall2 $ \x y -> (x `op` y) ~> res (x `sop` y)

getRuleDepth :: Rule -> Int
getRuleDepth (Rule r _) = getPDepth r
  where
        getPDepth :: Pattern -> Int
        getPDepth r = case r of
            PExpr (Lit _) -> 0
            PExpr (Var _) -> 0
            PExpr (And p q) -> binDepth p q
            PExpr (Or p q)  -> binDepth p q
            PExpr (Mul p q) -> binDepth p q
            PExpr (Add p q) -> binDepth p q
            PExpr (Eq p q)  -> binDepth p q
            PExpr (If p q z) -> 1 + maximum [getPDepth p, getPDepth q, getPDepth z]
            PAny _          -> 0
            PLit _ _        -> 0
          where
            binDepth p q = 1 + max (getPDepth p) (getPDepth q)


eqRec :: [EqRepr] -> Opt Bool
eqRec [] = return True
eqRec (x:[])   = return True
eqRec (x:y:xs) = liftM2 (&&) (equivalent x y) (eqRec (y:xs))

-- Returns True if it has changed the class
buildPattern :: Maybe EqRepr -> Pattern -> [(ID, Either Lit EqRepr)] -> Opt (Bool, EqRepr)
buildPattern cls p ma = case p of
    PExpr (Lit i) -> addTermToClass (EqExpr $ Lit i) cls
    PExpr (Var x) -> addTermToClass (EqExpr $ Var x) cls
    PExpr (Add q1 q2) -> addBinTermToClass Add q1 q2
    PExpr (Mul q1 q2) -> addBinTermToClass Mul q1 q2
    PExpr (And q1 q2) -> addBinTermToClass And q1 q2
    PExpr (Or q1 q2)  -> addBinTermToClass Or q1 q2
    PExpr (Eq q1 q2)  -> addBinTermToClass Eq q1 q2
    PExpr (If q1 q2 q3) -> do
        p1 <- rec q1
        p2 <- rec q2
        p3 <- rec q3
        c <- addTermToClass (EqExpr $ If p1 p2 p3) cls
        snd c `dependOn` [p1,p2,p3]
        return c
    PAny i     -> do
        let Right c = fromJust $ lookup i $ ma
        maybe (return (False, c)) (myUnion (False, c)) cls
    PLit _ v -> do
        r <- literal v
        c <- addTermToClass (EqExpr $ Lit r) cls
        return c
        
  where
    rec q = snd `fmap` buildPattern Nothing q ma
    addBinTermToClass op q1 q2 = do
        p1 <- rec q1
        p2 <- rec q2
        c <- addTermToClass  (EqExpr $ p1 `op` p2) cls
        snd c `dependOn` [p1,p2]
        return c
    literal :: Pattern -> Opt Lit
    literal p = case p of
       PFun f p1 p2 -> do
         q1 <- literal p1
         q2 <- literal p2
         return $ f q1 q2
       PLit _ v -> literal v
       PAny i -> do  
         let Left c = fromJust $ lookup i ma
         return c 

combineConst2 :: [[a]] -> [[a]] -> Maybe [[a]]
combineConst2 [] _  = Nothing
combineConst2 _ []  = Nothing
combineConst2 xs ys = Just [x ++ y | x <- xs, y <- ys]

combineConst3 :: [[a]] -> [[a]] -> [[a]] -> Maybe [[a]]
combineConst3 [] _  _   = Nothing
combineConst3 _  [] _   = Nothing
combineConst3 _  _  []  = Nothing
combineConst3 xs ys zs = Just [x ++ y ++ z | x <- xs, y <- ys, z <- zs]

applyPattern :: Pattern -> EqRepr -> Opt [[(ID, Either Lit EqRepr)]] -- [[Either (ID, Lit) (ID,EqRepr)]]
applyPattern pattern cls = do 
    elems <- getElems cls
    case pattern of
        PExpr (Lit i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l) | i == l -> return  $ Just []
            _              -> return Nothing
        PExpr (Var x) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Var y) | x == y -> return  $ Just []
            _              -> return Nothing
        PExpr (Add q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Add p1 p2) -> combine2 p1 p2 q1 q2 
            _ -> return Nothing
        PExpr (Mul q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Mul p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (And q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (And p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (Or q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Or p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (Eq q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Eq p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (If q1 q2 q3) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (If p1 p2 p3) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                r3 <- applyPattern q3 p3
                return $ combineConst3 r1 r2 r3
            _ -> return Nothing
        PAny i -> return [[(i,Right cls)]]
        PLit (LInteger _) (PAny i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l@(LInteger _)) -> return  $  Just [(i, Left l)]
            _              -> return Nothing
        PLit (LBool _) (PAny i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l@(LBool _)) -> return  $  Just [(i, Left l)]
            _              -> return Nothing
            
 where
    combine2 p1 p2 q1 q2 = do
       b <- equivalent p1 cls
       b' <- equivalent p2 cls
       if b || b'
            then return Nothing
            else do
              p1 <- root p1
              p2 <- root p2
              r1 <- applyPattern q1 p1 
              r2 <- applyPattern q2 p2
              return $ combineConst2 r1 r2    

applyPattern' :: Pattern -> EqRepr -> Set Int -> Opt [[(ID, Either Lit EqRepr)]] 
applyPattern' pattern cls set = do 
    elems <- getElems cls
    case pattern of
        PExpr (Lit i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l) | i == l -> return  $ Just []
            _              -> return Nothing
        PExpr (Var x) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Var y) | x == y -> return  $ Just []
            _              -> return Nothing
        PExpr (Add q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Add p1 p2) -> combine2 p1 p2 q1 q2 
            _ -> return Nothing
        PExpr (Mul q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Mul p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (And q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (And p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (Or q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Or p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (Eq q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Eq p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        PExpr (If q1 q2 q3) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (If p1 p2 p3) -> do
                p1' <- getPtr p1
                p2' <- getPtr p2
                p3' <- getPtr p3
                if S.fromList [p1',p2',p3'] `S.isSubsetOf` set
                    then return Nothing
                    else do
                        r1 <- applyPattern' q1 p1 (S.insert p1' set) 
                        r2 <- applyPattern' q2 p2 (S.insert p2' set)
                        r3 <- applyPattern' q3 p3 (S.insert p3' set)
                        return $ combineConst3 r1 r2 r3
            _ -> return Nothing
        PAny i -> return [[(i,Right cls)]]
        PLit (LInteger _) (PAny i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l@(LInteger _)) -> return  $  Just [(i, Left l)]
            _              -> return Nothing
        PLit (LBool _) (PAny i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l@(LBool _)) -> return  $  Just [(i, Left l)]
            _              -> return Nothing
            
 where
    combine2 p1 p2 q1 q2 = do
        p1' <- getPtr p1
        p2' <- getPtr p2
        let set' = S.fromList [p1',p2']
        if set' `S.isSubsetOf` set
            then return Nothing
            else do
              p1 <- root p1
              p2 <- root p2
              r1 <- applyPattern' q1 p1 (S.union set set')
              r2 <- applyPattern' q2 p2 (S.union set set')
              return $ combineConst2 r1 r2



-- returns True when it matched
apply :: Rule -> EqRepr -> Opt Bool
apply (Rule p1 p2) cls = do
    p <- getPtr cls
    ma <- applyPattern' p1 cls (S.singleton p)
    -- ma :: [ [ Either (Id, Lit) (id, eqrepr) ]] nagonting med nubclassesRight
    ma <- fun ma S.empty
    let t2 = length ma
    ma <- filterM (\l -> do 
        let same :: [ [EqRepr] ]
            same = map (map  snd) 
                     $ groupBy (\x y -> fst x == fst y) 
                     $ sortBy (\x y -> compare (fst x) (fst y)) 
                     $ [ (x, y) | (x, Right y) <- l ]

        liftM and $ mapM eqRec same
        ) ma
    list <- mapM (buildPattern (Just cls) p2) ma

    -- we should return True something has changed
    return $ any fst list
  where
    fun [] _ = return []
    fun (x:xs) set = do
        x' <- mapM translateConstraint (sortBy (compare `on` fst) x)
        if S.member x' set
            then fun xs set
            else liftM (x:) (fun xs (S.insert x' set))

translateConstraint :: (ID, Either Lit EqRepr) -> Opt (ID, Either Lit Int)
translateConstraint (id, e) = liftM ((,) id) $ case e of
    Left v -> return $ Left v
    Right cls -> do
        cls' <- getPtr cls
        return $  Right  cls'
-- Return True if any rule applied
applyRules :: [(Int, Rule)] -> EqRepr -> Opt Bool
applyRules rules reps = do
    dirty <- getDepth reps
    case dirty of
       Nothing -> return False
       Just d  -> do 
        bs <- mapM (apply' d) rules
        if all not bs
            then do
                updated reps Nothing
                return False
            else return True

  where
    apply' d (depth, rule)
              | d <= depth = apply rule reps
              | otherwise = return False

-- applys a set of rules on all classes
ruleEngine :: Int -> [(Int,Rule)] -> Opt ()
ruleEngine n rules | n < 0     = return ()
                   | otherwise = do
  classes <- getClasses
  res <- mapM (applyRules rules) classes
  when (any id res) $ ruleEngine (n-1) rules
