{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -F -pgmF she #-}
module Rule where

import Expr

import Opt hiding (EqRepr)
import Debug.Trace
import Data.Maybe
import Data.List (groupBy,sort, sortBy)
import Control.Monad
import Data.List (zipWith4)

type ID = Int

newtype Pattern = Pattern (Either (TExpr Pattern) ID)
    deriving Show

unPattern (Pattern x) = x

pattern PAny x = Pattern (Right x)


type Constraint = [(ID, EqRepr)] -> Opt Bool
data Rule = Rule Pattern Pattern

pid = Pattern . Right

(~>) = Rule 
forall3 f = f (PAny 1) (PAny 2) (PAny 3)
forall2 f = f (PAny 1) (PAny 2)
forall1 f = f (PAny 1)

rAnd x y  = Pattern $ Left (And x y)
rOr x y   = Pattern $ Left (Or x y)
rAdd x y  = Pattern $ Left (Add x y)
rMul x y  = Pattern $ Left (Mul x y)
rInt x    = Pattern $ Left (Lit $ LInteger x)
rBool x   = Pattern $ Left (Lit $ LBool x)
rTrue     = rBool True
rFalse    = rBool False
rVar x    = Pattern $ Left (Var x)
rEq x y   = Pattern $ Left (Eq x y)
rIf x y z = Pattern $ Left (If x y z)

rules :: [(Int,Rule)]
rules = map (\r -> (getRuleDepth r, r)) $
        [ assoc rAdd
        , assoc rMul
        , assoc rAnd
        , assoc rOr
        , commute rAdd
        , commute rMul
        , commute rAnd
        , commute rOr
        , commute rEq
        , identity rAdd  (rInt 0)
        , identity rMul  (rInt 1)
        , identity rAnd  (rTrue)
        , identity rOr   (rFalse)
        , forall3 $ \x y z -> rMul x (rAdd y z) ~> rAdd (rMul x y) (rMul x z) -- distr ....
        , forall3 $ \x y z -> rAdd (rMul x y) (rMul x z) ~> rMul x (rAdd y z)
        , forall1 $ \x -> x `rEq` x ~> rTrue
        , forall1 $ \x -> x `rMul` (rInt 0) ~> rInt 0
        , forall1 $ \x -> (x `rOr` rTrue) ~> rTrue
        , forall1 $ \x -> (x `rAnd` rFalse) ~> rFalse
        , forall2 $ \x y -> rIf (rTrue) x y ~> x
        , forall2 $ \x y -> rIf (rFalse) x y ~> y
        , forall2 $ \x y -> rIf y x x ~> x
        ] 

identity op v = forall1 $ \x -> (x `op` v) ~> x        
commute op    = forall2 $ \x y -> (x `op` y) ~> (y `op` x)
assoc op      = forall3 $ \x y z -> ((x `op` y) `op` z) ~> (x `op` (y `op` z))

getRuleDepth :: Rule -> Int
getRuleDepth (Rule r _) = getDepth r
  where
    getDepth :: Pattern -> Int
    getDepth r = case unPattern r of
        Left (Lit _) -> 0
        Left (Var _) -> 0
        Left (And p q) -> binDepth p q
        Left (Or p q)  -> binDepth p q
        Left (Mul p q) -> binDepth p q
        Left (Add p q) -> binDepth p q
        Left (Eq p q)  -> binDepth p q
        Left (If p q z) -> 1 + maximum [getDepth p, getDepth q, getDepth z]
        Right _        -> 0
     where
        binDepth p q = 1 + max (getDepth p) (getDepth q)

-- returns True when nothing matched
apply :: Rule -> EqRepr -> Opt Bool
apply (Rule p1 p2) cls = do
    ma <- applyPattern p1 cls
    -- TODO: check so if id maps to two different things in ma, that they are equal
    -- TODO: check if the code works :)
    --trace ("apply: " ++ show ma) $ return ()
    ma <- filterM (\l -> do 
        let same = map (map  snd) 
                     $ groupBy (\x y -> fst x == fst y) 
                     $ sortBy (\x y -> compare (fst x) (fst y)) $ l
        liftM and $ mapM eqRec same
        ) ma
    --liftM null $ mapM (buildPattern' cls p2) ma
    
    list <- mapM (buildPattern (Just cls) p2) $ ma
    --ls <- mapM (union cls) list
    return $ null list

--    mapM_ ls (markDirty

eqRec :: [EqRepr] -> Opt Bool
eqRec [] = return True
eqRec (x:[])   = return True
eqRec (x:y:xs) = liftM2 (&&) (equivalent x y) (eqRec (y:xs))

buildPattern :: Maybe EqRepr -> Pattern -> [(ID,EqRepr)] -> Opt EqRepr
buildPattern cls p ma = case p of
    Pattern (Left (Lit i)) -> addTermToClass (EqExpr $ Lit i) cls
    Pattern (Left (Var x)) -> addTermToClass (EqExpr $ Var x) cls
    Pattern (Left (Add q1 q2)) -> addBinTermToClass Add q1 q2
    Pattern (Left (Mul q1 q2)) -> addBinTermToClass Mul q1 q2
    Pattern (Left (And q1 q2)) -> addBinTermToClass And q1 q2
    Pattern (Left (Or q1 q2))  -> addBinTermToClass Or q1 q2
    Pattern (Left (Eq q1 q2))  -> addBinTermToClass Eq q1 q2
    Pattern (Left (If q1 q2 q3)) -> do
        p1 <- buildPattern Nothing q1 ma
        p2 <- buildPattern Nothing q2 ma
        p3 <- buildPattern Nothing q3 ma
        c <- addTermToClass (EqExpr $ If p1 p2 p3) cls
        c `dependOn` [p1,p2,p3]
        return c
    PAny i     -> do
        let c = fromJust $ lookup i ma
        maybe (return c) (union c) cls
  where
    addBinTermToClass op q1 q2 = do
        p1 <- buildPattern Nothing q1 ma
        p2 <- buildPattern Nothing q2 ma
        c <- addTermToClass  (EqExpr $ p1 `op` p2) cls
        c `dependOn` [p1,p2]
        return c

combineConst2 :: [[a]] -> [[a]] -> Maybe [a]
combineConst2 [] _  = Nothing
combineConst2 _ []  = Nothing
combineConst2 xs ys = Just . concat $ [x ++ y | x <- xs, y <- ys]

combineConst3 :: [[a]] -> [[a]] -> [[a]] -> Maybe [a]
combineConst3 [] _  _   = Nothing
combineConst3 _  [] _   = Nothing
combineConst3 _  _  []  = Nothing
combineConst3 xs ys zs = Just . concat $ [x ++ y ++ z | x <- xs, y <- ys, z <- zs]

applyPattern :: Pattern -> EqRepr -> Opt [[(ID, EqRepr)]]
applyPattern pattern cls = do 
    elems <- getElems cls
    case unPattern pattern of
        Left (Lit i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l) | i == l -> return  $ Just []
            _              -> return Nothing
        Left (Var x) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Var y) | x == y -> return  $ Just []
            _              -> return Nothing
        Left (Add q1 q2) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Add p1 p2) -> combine2 p1 p2 q1 q2 
            _ -> return Nothing
        Left (Mul q1 q2) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Mul p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        Left (And q1 q2) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (And p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        Left (Or q1 q2) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Or p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        Left (Eq q1 q2) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Eq p1 p2) -> combine2 p1 p2 q1 q2
            _ -> return Nothing
        Left (If q1 q2 q3) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (If p1 p2 p3) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                r3 <- applyPattern q3 p3
                return $ combineConst3 r1 r2 r3
            _ -> return Nothing
        Right i -> return [[(i,cls)]]
 where
    combine2 p1 p2 q1 q2 = do
       r1 <- applyPattern q1 p1 
       r2 <- applyPattern q2 p2
       return $ combineConst2 r1 r2    

applyRules :: [(Int, Rule)] -> EqRepr -> Opt ()
applyRules rules reps = do
    bs <- mapM apply' rules
    when (and bs) $ updated reps Nothing
  where
    apply' (depth, rule) = do
        dirty <- getDepth reps
        case dirty of
            Nothing -> return True
            Just d 
              | d <= depth -> apply rule reps
              | otherwise -> return True

-- applys a set of rules on all classes
ruleEngine :: [(Int,Rule)] -> Opt ()
ruleEngine rules = do
  classes <- getClasses
  mapM_ (applyRules rules) classes

