{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module TestExpr where

import Expr
import Rule
import IOSetA hiding (EqRepr)
import Opt hiding (EqRepr)
import qualified Opt

import Parser
import Translate (translate)

import Data.List
import Data.IORef
import Data.IOStableRef
import qualified Data.Set as S

import "mtl" Control.Monad.State

import qualified Data.Map as M

-- | Print all members of a class
printClass :: EqRepr -> Opt ()
printClass rep = do
    (Root i _ dat) <- rootIO rep 
    let s = eqSet dat
    mdeps <- forM (eqDependOnMe dat) $ \d -> do
        Root i _ _ <- rootIO d
        return i
    ideps <- forM (S.toList $ eqIDependOn dat) $ \d -> do
        Root i _ _ <- rootIO d
        return i
    liftIO $ putStrLn $ "[#" ++ show i ++ "(depth: " ++ show (depth dat) 
                         ++ "),(size: " ++ show (S.size s) 
                         ++ "),(mdeps: " ++ show (nub mdeps)
                         ++ "),(ideps: " ++ show (nub ideps)
                         ++ ")]"
    forM_ (S.toList s) $ \(EqExpr e) -> do
        str <- showTerm e
        liftIO $ putStrLn $ "  " ++ str
    return ()


rootID :: Opt.EqRepr s -> Opt.OptMonad s CompareType
rootID p = do
        (Root c _ _) <- rootIO p
        return c

showTerm :: TExpr (Opt.EqRepr (EqExpr)) -> Opt String
showTerm exp = case exp of
    Add p1 p2 -> showBin "+" p1 p2
    Mul p1 p2 -> showBin "*" p1 p2
    And p1 p2 -> showBin "`and`" p1 p2
    Or  p1 p2 -> showBin "`or`" p1 p2
    Eq  p1 p2 -> showBin "==" p1 p2
    Lit i -> return $ show i
    Var x -> return $ show x
    If p1 p2 p3 -> do
        q1 <- rootID p1
        q2 <- rootID p2 
        q3 <- rootID p3
        return $ "if #" ++ show q1 ++ " then  #" ++  show q2 ++ " else #" ++ show q3
  where
    showBin op p1 p2 = do
    q1 <- rootID p1
    q2 <- rootID p2 
    return $ "#" ++ show q1 ++ " " ++ op ++ " #" ++  show q2

-- | A simple tester, given a syntactic term it will be print status of how the
--   classes looks etc.
testExpr :: Expr -> IO ()
testExpr expr = runOpt $ do
    rep <- translate [("main", expr)]
    p <- rootID rep
    liftIO $  putStrLn $ "rep: #" ++ show p 
    cls <- Opt.getClasses
    mapM_ printClass $ reverse cls
    liftIO $ putStrLn $ "number of classes poeInters: " ++ show (length cls)
    liftIO $ putStrLn "-----------------"
    ruleEngine 10 rules
    cls <- Opt.getClasses
    mapM_ printClass $ reverse cls
    liftIO $ putStrLn $ "number of classes poeInters: " ++ show (length cls)
    m <- liftIO $ newIORef M.empty
    p <- rootID rep
    res <- buildExpr m rep
    liftIO $ do
        putStrLn "from:"
        putStr $ show expr
        putStrLn $ " @ #" ++ show p
        putStrLn "to:"
        print res

-- | Read a file and run the rule engine a specified number of times
testFileExpr :: FilePath -- ^ filename  
             -> Int      -- ^ maximum number of iterations of the rule engine
             -> Bool     -- ^ shoud we print all eq classes
             -> IO (Either String (Int, Expr))
testFileExpr fileName max_it show_cls = do
    file <- readFile fileName
    case parseExpr file of
        Left err -> return $ Left $ show err
        Right vs -> runOpt $ do
            eq <- translate vs
            ruleEngine max_it rules
            cls <- Opt.getClasses
            when show_cls $ mapM_ printClass $ reverse cls
            m <- liftIO $ newIORef M.empty
            res <- buildExpr m eq
            return $ Right res -- liftIO $ print res  
    

-- | Given an table for the value calculate the value (and term) of the
--   best term in a class. The table is usually empty when you call this.
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
            Root p _ _ <- rootIO rep
         --   liftIO $ putStrLn $ "for class " ++ show p
         --   mapM_ (\(val , EqExpr e) -> (liftIO . putStrLn) =<< showTerm e) pre_values
            resl <- mapM (buildExpr' m) (best pre_values)
            let res = head $ sortBy (\(x,_) (y,_) -> x `compare` y) resl
            ltable <- liftIO $ readIORef m
            liftIO $ writeIORef m (M.insert rep (Just res) ltable) 
            return res
  where
    -- Values are always as good as or better than operators
    buildPre rep = case unEqExpr rep of
        Var _    -> 1
        Lit _    -> 1
        _        -> 3

    buildExpr' :: IORef (M.Map EqRepr (Maybe (Int,Expr))) -> EqExpr -> Opt (Int, Expr)
    buildExpr' m rep = case unEqExpr rep of
        Add p1 p2 -> buildBin  Add 3 p1 p2
        Mul p1 p2 -> buildBin  Mul 3 p1 p2
        And p1 p2 -> buildBin  And 3 p1 p2
        Or  p1 p2 -> buildBin  Or  3 p1 p2
        Eq  p1 p2 -> buildBin  Eq  3 p1 p2
        Var v -> return (1,In $ Var v)
        Lit i -> return (1,In $ Lit i)
        If  p1 p2 p3 -> do
            (c1,q1) <- buildExpr m p1
            (c2,q2) <- buildExpr m p2
            (c3,q3) <- buildExpr m p3
            return (c1 + (max c2 c3) + 3,In $ If q1 q2 q3)
     where
        buildBin op cost p1 p2 = do
            (c1,q1) <- buildExpr m p1
            (c2,q2) <- buildExpr m p2
            return (c1+c2+3,In $ q1 `op` q2)


best :: Ord a => [(a,b)] -> [b]
best xs = map snd $ best' (fst $ head sorted) sorted
  where 
    sorted = sortBy (\(x,_) (y,_) -> x `compare` y) xs
    best' v ((x,y):xs) | x <= v = (x,y) : best' v xs
    best' _ _ = []


-- just a collection of examples --

test0' = eInt 3 +. eInt 1
test1' = eInt 2
test2' = (eInt 2 +. eInt 3) +. (eInt 3 +. eInt 4)
test3' = (eInt 2 +. eInt 3) +. (eInt 3 +. eInt 2)
texpr0 = eVar "x" +. eVar "x"
texpr1 = eVar "y" +. eVar "x"
texpr2 = eVar "x" *. eInt 0
texpr3 = eVar "a" +. eVar "b" +. eVar "c" +. eVar "d" +. eInt 0
texpr4 = eInt 3 +. eInt 0
texpr5 = eTrue `eOr` eFalse
texpr7 = (eTrue ==. eFalse) `eOr` (eInt 2 ==. (eInt 2 *. eInt 1))
texpr8 = eIf (texpr7) texpr4 texpr2
