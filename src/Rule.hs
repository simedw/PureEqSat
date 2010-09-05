{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeOperators #-}
module Rule where

import Expr

import Opt hiding (Rule)
import Debug.Trace
import Data.Maybe
import Data.List (groupBy,sort)
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

add x y = Pattern $ Left (Add x y)
mul x y = Pattern $ Left (Mul x y)
plit x   = Pattern $ Left (Lit x)
pvar x   = Pattern $ Left (Var x)

rules = [com, assoc, test4, test5] -- vet inte om det är användbart :)

test2 = forall3 $ \x y z -> add (add x y) z
test3 = forall3 $ \x y z -> add (add x y) z ~> add x (add y z) 
com   = forall2 $ \x y -> add x y ~> add y x
assoc = forall3 $ \x y z -> add (add x y) z ~> add x (add y z) 

test4 = forall1 $ \x -> add x x ~> mul x (plit 2)
test5 = forall1 $ \x -> mul x (plit 0) ~> plit 0

apply :: Rule -> EqRepr -> Opt ()
apply (p1 :~> p2) cls = do
    ma <- applyPattern p1 cls
    -- TODO: check so if id maps to two different things in ma, that they are equal
    -- TODO: check if the code works :)
    --trace ("apply: " ++ show ma) $ return ()
    ma <- filterM (\l -> do 
        let same = map (map  snd) $ groupBy (\x y -> fst x == fst y) l
        liftM and $ mapM eqRec same
        ) ma
    list <- mapM (buildPattern p2) $ ma
    mapM_ (union cls) list

eqRec :: [EqRepr] -> Opt Bool
eqRec [] = return True
eqRec (x:[])   = return True
eqRec (x:y:xs) = liftM2 (&&) (equivalent x y) (eqRec (y:xs))

buildPattern :: Pattern -> [(ID,EqRepr)] -> Opt EqRepr
buildPattern p ma = case p of
    Pattern (Left (Lit i)) -> addTerm (Lit i)
    Pattern (Left (Var x)) -> addTerm (Var x)
    Pattern (Left (Add q1 q2)) -> do
        p1 <- buildPattern q1 ma
        p2 <- buildPattern q2 ma
        addTerm (Add p1 p2)
    Pattern (Left (Mul q1 q2)) -> do
        p1 <- buildPattern q1 ma
        p2 <- buildPattern q2 ma
        addTerm (Mul p1 p2)             
    PAny i     -> maybe (error $ "buildPattern: " ++ show i ++ " in " ++ show ma ++ ", pattern: " ++ show p) return $ lookup i ma

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
            Lit l | i == l -> return  $ Just []
            _              -> return Nothing
        Pattern (Left (Var x)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            Var y | x == y -> return  $ Just []
            _              -> return Nothing
        Pattern (Left (Add q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            Add p1 p2 -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        Pattern (Left (Mul q1 q2)) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            Mul p1 p2 -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                return $ fum r1 r2
            _ -> return Nothing
        PAny i -> return [[(i,cls)]]
        
        

applyRules :: [Rule] -> EqRepr -> Opt ()
applyRules rules reps = mapM_ (flip apply reps) rules

-- applys rules many times or something
ruleEngine :: [Rule] -> Opt ()
ruleEngine rules = do
  classes <- getClasses
  mapM_ (applyRules rules) classes
    -- skulle vara bra att ha en getClasses, vi gor en sadan!
