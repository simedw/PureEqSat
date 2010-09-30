module Translate where

import Expr 
import Opt hiding (EqRepr)

import Control.Monad

import qualified Data.Map as M
import Data.Map (Map)

import qualified Data.Set as S
import Data.Set (Set)

type Var = String


translate :: [(String, Expr)] -> Opt EqRepr
translate exprs = do
    let unk = S.unions (map (fv . snd) exprs) S.\\ S.fromList (map fst exprs)
        mexps = topoSort exprs unk
    case mexps of
        -- should be done more gracefully
        Nothing -> error "Recursive definition of vars"
        Just exprs' -> addExprs exprs' M.empty
            
addExprs :: [(Var, Expr)] -> Map Var EqRepr -> Opt EqRepr
addExprs [] gamma = case M.lookup "main" gamma of
    Nothing -> error "no main expression"
    Just ma -> return ma
addExprs ((v,e):es) gamma = do
    q <- addExpr e gamma
    addExprs es (M.insert v q gamma)

fv :: Expr -> Set Var
fv expr = case out expr of
    Atom (Var x) -> S.singleton x
    Atom _       -> S.empty
    Bin _ x y    -> x `fuv` y
    Tri _ x y z  -> x `fuv` y `S.union` fv z
  where
    x `fuv` y = fv x `S.union` fv y

topoSort :: [(Var,Expr)] -> Set Var -> Maybe [(Var, Expr)]
topoSort toSort unknown = topoSort' [ (S.size (depOn var) , var, e) | (var , e) <- toSort]
  where

    depMap :: Map Var (Set Var)
    depMap = M.fromList [(var , fv e S.\\ unknown) | (var, e) <- toSort]

    depOn :: Var -> Set Var
    depOn = maybe S.empty id . flip M.lookup depMap

    decr :: Var -> [ (Int, Var, Expr) ] -> [ (Int, Var, Expr)]
    decr v = map decr' 
      where
        decr' (num, var, expr) | v `S.member` depOn var = (num - 1, var,  expr)
                               | otherwise              = (num, var, expr)

    getZero :: [(Int, Var , Expr)] -> Maybe ((Var, Expr) , [(Int, Var, Expr)]) 
    getZero [] = Nothing 
    getZero ((0 , var, expr) : xs) = return ( (var, expr) , xs)
    getZero ( x : xs) = do
        (sol, xs') <- getZero xs
        return (sol , x : xs')
      where

    topoSort' :: [ (Int, Var,Expr) ] -> Maybe [(Var, Expr)]
    topoSort' [] = return []
    topoSort' xs = do
        ((var, e) , xs') <- getZero xs
        xs'' <- topoSort' (decr var xs')
        return $ (var, e) : xs'' 

addExpr :: Expr -> Map Var EqRepr -> Opt EqRepr
addExpr exp gamma = case out exp of
    Atom (Var x)    -> case M.lookup x gamma of
        Nothing -> addTerm (EqExpr . Atom $ Var x)
        Just q  -> return q
    Atom a    -> addTerm (EqExpr $ Atom a)
    Bin bin x y  -> do 
        x' <- addExpr x gamma
        y' <- addExpr y gamma
        c <- addTerm (EqExpr $ Bin bin x' y')
        c `dependOn` [x',y']
        return c
    Tri tri x y z -> do
        x' <- addExpr x gamma
        y' <- addExpr y gamma
        z' <- addExpr z gamma
        c <- addTerm (EqExpr $ Tri tri x' y' z')
        c `dependOn` [x',y', z']
        return c
