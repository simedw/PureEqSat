{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module TestExpr where

import Expr
import Rule
import IOSetA hiding (EqRepr)
import Opt hiding (EqRepr)
import qualified Opt

import Data.List
import Data.IORef
import Data.IOStableRef
import qualified Data.Set as S

import "mtl" Control.Monad.State

import qualified Data.Map as M


printClass :: EqRepr -> Opt ()
printClass rep = do
    (Root i _ dat) <- lift $ rootIO rep 
    let s = eqSet dat
    liftIO $ putStrLn $ "[#" ++ show i ++ " (size: " ++ show (S.size s) ++ ")]"
    forM_ (S.toList s) $ do \(EqExpr e) -> (showTerm e >>= \str -> liftIO $ putStrLn $ "  " ++ str)
    return ()

pointTo p = do
        (Root c _ _) <- lift $ rootIO p
        return c

showTerm exp = case exp of
    Add p1 p2 -> showBin "+" p1 p2
    Mul p1 p2 -> showBin "*" p1 p2
    And p1 p2 -> showBin "`and`" p1 p2
    Or  p1 p2 -> showBin "`or`" p1 p2
    Eq  p1 p2 -> showBin "==" p1 p2
    Lit i -> return $ show i
    Var x -> return $ show x
  where
    showBin op p1 p2 = do
    q1 <- pointTo p1
    q2 <- pointTo p2 
    return $ "#" ++ show q1 ++ " " ++ op ++ " #" ++  show q2

testExpr :: Expr -> IO ()
testExpr expr = runOpt $ do
    rep <- addExpr expr
    p <- pointTo rep
    liftIO $  putStrLn $ "rep: #" ++ show p 
    cls <- Opt.getClasses
    mapM_ printClass $ reverse cls
    liftIO $ putStrLn $ "number of classes pointers: " ++ show (length cls)
    liftIO $ putStrLn "-----------------"
    replicateM_ 3 $ ruleEngine rules
    cls <- Opt.getClasses
    mapM_ printClass $ reverse cls
    liftIO $ putStrLn $ "number of classes pointers: " ++ show (length cls)
    m <- liftIO $ newIORef M.empty
    p <- pointTo rep
    res <- buildExpr m rep
    liftIO $ do
        putStrLn "from:"
        putStr $ show expr
        putStrLn $ " @ #" ++ show p
        putStrLn "to:"
        print res
    
test0' = int 3 +. int 1
test1' = int 2
test2' = (int 2 +. int 3) +. (int 3 +. int 4)
test3' = (int 2 +. int 3) +. (int 3 +. int 2)
texpr0 = var "x" +. var "x"
texpr1 = var "y" +. var "x"
texpr2 = var "x" *. int 0
texpr3 = var "a" +. var "b" +. var "c" +. var "d" +. int 0
texpr4 = int 3 +. int 0
texpr5 = bool True `tor` bool False
texpr7 = (bool True ==. bool False) `tor` (int 2 ==. (int 2 *. int 1))


-- eqexpr eller expr
-- tankte mig expr
buildExpr :: IORef (M.Map EqRepr (Maybe (Int,Expr))) -> EqRepr -> Opt (Int,Expr)
buildExpr m rep = do
    ltable <- liftIO $ readIORef m
    case M.lookup rep ltable of
        Just (Just t) -> return t
        -- if we try to build something that dependes on where what we are building x <| x
        -- we will try to make this an invalid choices
        Just Nothing  -> return (10000000,error "this is a loop")
        Nothing -> do
            liftIO $ writeIORef m (M.insert rep Nothing ltable) 
            terms <- Opt.getElems rep
            let pre_values = zip (map buildPre terms) terms
            Root p _ _ <- lift $ rootIO rep
            liftIO $ putStrLn $ "for class " ++ show p
            mapM_ (\(val , EqExpr e) -> (liftIO . putStrLn) =<< showTerm e) pre_values
            resl <- mapM (buildExpr' m) (best pre_values)
            let res = head $ sortBy (\(x,_) (y,_) -> x `compare` y) resl
            ltable <- liftIO $ readIORef m
            liftIO $ writeIORef m (M.insert rep (Just res) ltable) 
            return res
  where
    buildPre rep = case unEqExpr rep of
        Add _ _ -> 3
        Mul _ _ -> 3
        Or  _ _ -> 3
        And _ _ -> 3
        Eq _ _  -> 3
        Var _   -> 1
        Lit _   -> 1 

    buildExpr' :: IORef (M.Map EqRepr (Maybe (Int,Expr))) -> EqExpr -> Opt (Int, Expr)
    buildExpr' m rep = case unEqExpr rep of
        Add p1 p2 -> buildBin  Add 3 p1 p2
        Mul p1 p2 -> buildBin  Mul 3 p1 p2
        And p1 p2 -> buildBin  And 3 p1 p2
        Or  p1 p2 -> buildBin  Or  3 p1 p2
        Eq  p1 p2 -> buildBin  Eq  3 p1 p2
        Var v -> return (1,In $ Var v)
        Lit i -> return (1,In $ Lit i)
     where
        buildBin op cost p1 p2 = do
            (c1,q1) <- buildExpr m p1
            (c2,q2) <- buildExpr m p2
            return (c1+c2+3,In $ q1 `op` q2)

-- should be in prelude
best :: Ord a => [(a,b)] -> [b]
best xs = map snd $ best' (fst $ head sorted) sorted
  where 
    sorted = sortBy (\(x,_) (y,_) -> x `compare` y) xs
    best' v ((x,y):xs) | x <= v = (x,y) : best' v xs
    best' _ _ = []

