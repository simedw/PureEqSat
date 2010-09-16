{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeOperators #-}
module Rule where

import Expr

import Opt hiding (EqRepr)
import Debug.Trace
import Data.Maybe
import Data.List (groupBy,sort, sortBy)
import Control.Monad

type ID = Int

newtype Pattern = Pattern (Either (TExpr Pattern) ID)
    deriving Show

pattern PAny x = Pattern (Right x)

data Rule = Pattern :~> Pattern
  deriving Show

pid = Pattern . Right

(~>) = (:~>)
forall3 f = f (PAny 1) (PAny 2) (PAny 3)
forall2 f = f (PAny 1) (PAny 2)
forall1 f = f (PAny 1)

pand x y = Pattern $ Left (And x y)
por x y  = Pattern $ Left (Or x y)
add x y  = Pattern $ Left (Add x y)
mul x y  = Pattern $ Left (Mul x y)
pint x   = Pattern $ Left (Lit $ LInteger x)
pbool x  = Pattern $ Left (Lit $ LBool x)
pvar x   = Pattern $ Left (Var x)
peq x y  = Pattern $ Left (Eq x y)

rules :: [(Int,Rule)]
rules = [ (3, assoc add)
        , (3, assoc mul)
        , (3, assoc pand)
        , (3, assoc por)
        , (2, commute add)
        , (2, commute mul)
        , (2, commute por)
        , (3, identity add  (pint 0))
        , (3, identity mul  (pint 1))
        , (3, identity pand (pbool True))
        , (3, identity por  (pbool False))
        , (4, forall3 $ \x y z -> mul x (add y z) ~> add (mul x y) (mul x z)) -- distr ....
        , (4, forall3 $ \x y z -> add (mul x y) (mul x z) ~> mul x (add y z))
        , (2, forall1 $ \x -> x `peq` x ~> pbool True)
        , (2, forall1 $ \x -> x `mul` (pint 0) ~> pint 0)
        , (1, forall1 $ \x -> (x `por` pbool True) ~> pbool True)
        ] 

identity op v = forall1 $ \x -> (x `op` v) ~> x        
commute op    = forall2 $ \x y -> (x `op` y) ~> (y `op` x)
assoc op      = forall3 $ \x y z -> ((x `op` y) `op` z) ~> (x `op` (y `op` z))

test4 = forall1 $ \x -> add x x ~> mul x (pint 2)
test5 = forall1 $ \x -> mul x (pint 0) ~> pint 0
addIden = forall1 $ \x -> add x (pint 0) ~> x

-- returns True when nothing matched
apply :: Rule -> EqRepr -> Opt Bool
apply (p1 :~> p2) cls = do
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

fun :: Eq a => [[a]] -> [[a]] -> [[a]]
fun xs ys = [x ++ y | x <- xs, y <- ys] 

fum :: [[a]] -> [[a]] -> Maybe [a]
fum [] _  = Nothing
fum _ []  = Nothing
--fum (x:xs) (y:ys) = Just (x ++ y)
fum xs ys = Just . concat $ [x ++ y | x <- xs, y <- ys]

applyPattern :: Pattern -> EqRepr -> Opt [[(ID, EqRepr)]]
applyPattern pattern cls = do 
    elems <- getElems cls
    -- trace ("applyPattern: " ++ show pattern ++ " " ++ show cls ++ " " ++ show elems) $
    case pattern of
        Pattern (Left (Lit i)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Lit l) | i == l -> return  $ Just []
            _              -> return Nothing
        Pattern (Left (Var x)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Var y) | x == y -> return  $ Just []
            _              -> return Nothing
        Pattern (Left (Add q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Add p1 p2) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        Pattern (Left (Mul q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Mul p1 p2) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        Pattern (Left (And q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (And p1 p2) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        Pattern (Left (Or q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Or p1 p2) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        Pattern (Left (Eq q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Eq p1 p2) -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        PAny i -> return [[(i,cls)]]
        

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

