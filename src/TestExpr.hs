{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module TestExpr where

import Expr
import ListSetA
import Opt

import "mtl" Control.Monad.State

import qualified Data.Map as M

testExpr :: Expr -> IO ()
testExpr expr = do
    let (a1, a2, q1, q2) = runOpt $ do
        rep <- addExpr expr
        cls <- liftM M.toList $ lift $ gets classes
        q1 <- get
        let a1 = [ (cid, rep) | (cid, Right xs) <- cls, rep <- xs]
        replicateM_ 10 $ sequence_ [ runARule cid rep | (cid, Right xs) <- cls, rep <- xs]
        -- cls :: [(Int, Either Int [TExpr Int])
        q2 <- get
        cls <- liftM M.toList $ lift $ gets classes
        let a2 = [ (cid, rep) | (cid, Right xs) <- cls, rep <- xs]
        return (a1,a2, q1, q2)
    mapM_ print a1
    putStrLn "optimized? : "
    mapM_ print a2
    putStrLn "testa q"
    print q1
    putStrLn "and nästa"
    print q2
{-
testExpr :: Expr -> [(Int, TExpr EqRepr)]
testExpr expr = runOpt $ do
    rep <- addExpr expr
    cls <- liftM M.toList $ lift $ gets classes
    sequence_ [ runARule cid rep | (cid, Right xs) <- cls, rep <- xs]

    -- cls :: [(Int, Either Int [TExpr Int])
    cls <- liftM M.toList $ lift $ gets classes
    return $ [ (cid, rep) | (cid, Right xs) <- cls, rep <- xs]
-}



test1 = lit 3 +. lit 1
test2 = (lit 2 +. lit 3) +. (lit 3 +. lit 4)
test3 = (lit 2 +. lit 3) +. (lit 3 +. lit 2)
