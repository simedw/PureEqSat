{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module TestExpr where

import Expr
import Rule
import IOSetA hiding (EqRepr)
import Opt hiding (EqRepr)

import Data.IOStableRef
import qualified Data.Set as S

import "mtl" Control.Monad.State

import qualified Data.Map as M


printClass :: EqRepr -> Opt ()
printClass rep = do
    (Root i _ s) <- liftIO $ readIOStableRef rep
    liftIO $ putStrLn $ "[#" ++ show i ++ " (" ++ show (S.size s) ++ ")]"
    forM_ (S.toList s) $ do \(EqExpr e) -> (showTerm e >>= \str -> liftIO $ putStrLn $ "  " ++ str)
    return ()
  where
    showTerm (Add p1 p2) = do
        q1 <- pointTo p1
        q2 <- pointTo p2 
        return $ "#" ++ show q1 ++ " + #" ++  show q2
    showTerm (Mul p1 p2) = do
        q1 <- pointTo p1
        q2 <- pointTo p2 
        return $ "#" ++ show q1 ++ " * #" ++  show q2
    showTerm (Lit i )    = return $ show i
    showTerm (Var x)     = return $ show x
    pointTo p = do
        (Root c _ _) <- lift $  rootIO p
        return c

testExpr :: Expr -> IO ()
testExpr expr = runOpt $ do
    rep <- addExpr expr
    cls <- lift $ gets classes
    liftIO $ print $ length cls
    mapM_ printClass $ reverse cls
    replicateM_ 10 $ ruleEngine rules
    cls <- lift $ gets classes
    liftIO $ print $ length cls
    mapM_ printClass $ reverse cls
       
 
{-
testExpr2 :: Expr -> IO ()
testExpr2 expr = do
    (a1, a2, q1, q2, t) <- runOpt $ do
        rep <- addExpr expr
        cls <- liftM M.toList $ lift $ gets classes
        q1 <- get
        let a1 = [ (cid, rep) | (cid, xs) <- cls, rep <- S.toList xs]
        replicateM_ 100 $ ruleEngine rules
        q2 <- get
        cls <- liftM M.toList $ lift $ gets classes
        let a2 = [ (cid, rep) | (cid, xs) <- cls, rep <- S.toList xs]
        return (a1,a2, q1, q2, cls)
    mapM_ print a1
    putStrLn "optimized? : "
    mapM_ print a2
    putStrLn "testa q"
    print q1
    putStrLn "and nästa"
    print q2
    print t
-}
test0' = lit 3 +. lit 1
test1' = lit 2
test2' = (lit 2 +. lit 3) +. (lit 3 +. lit 4)
test3' = (lit 2 +. lit 3) +. (lit 3 +. lit 2)
texpr0 = var "x" +. var "x"
texpr1 = var "y" +. var "x"
texpr2 = var "x" *. lit 0
texpr3 = var "a" +. var "b" +. var "c" +. var "d" +. lit 0 
