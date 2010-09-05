{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module TestExpr where

import Expr
import Rule
import ListSetA
import Opt

import qualified Data.Set as S

import "mtl" Control.Monad.State

import qualified Data.Map as M

testExpr2 :: Expr -> IO ()
testExpr2 expr = do
    let (a1, a2, q1, q2, t) = runOpt $ do
        rep <- addExpr expr
        cls <- liftM M.toList $ lift $ gets classes
        q1 <- get
        let a1 = [ (cid, rep) | (cid, Right xs) <- cls, rep <- S.toList xs]
        replicateM_ 100 $ ruleEngine rules
        q2 <- get
        cls <- liftM M.toList $ lift $ gets classes
        let a2 = [ (cid, rep) | (cid, Right xs) <- cls, rep <- S.toList xs]
        return (a1,a2, q1, q2, cls)
    mapM_ print a1
    putStrLn "optimized? : "
    mapM_ print a2
    putStrLn "testa q"
    print q1
    putStrLn "and nästa"
    print q2
    print t

test0' = lit 3 +. lit 1
test1' = lit 2
test2' = (lit 2 +. lit 3) +. (lit 3 +. lit 4)
test3' = (lit 2 +. lit 3) +. (lit 3 +. lit 2)
texpr0 = var "x" +. var "x"
texpr1 = var "y" +. var "x"
texpr2 = var "x" *. lit 0
texpr3 = var "a" +. var "b" +. var "c" +. var "d" +. lit 0 
