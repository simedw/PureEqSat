{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
module Expr where

import Opt hiding (EqRepr)
import qualified Opt as Opt
import Debug.Trace
import Data.Maybe
import Data.List (groupBy,sort)
import Control.Monad


data Lit
    = LInteger Integer
    | LBool Bool
  deriving (Eq,Ord,Show)

data TExpr r 
    = Lit Lit
    | Var String
    | Add r r
    | Mul r r
    | And r r
    | Or  r r
    | Eq r r
    | If r r r
    deriving (Eq, Ord, Show)

-- smart operators
eAnd x y = In (And x y)
eOr  x y = In (Or x y)
eInt     = In . Lit . LInteger
eBool    = In . Lit . LBool
eTrue    = eBool True
eFalse   = eBool False

eVar     = In . Var
x +. y  = In (Add x y)
x *. y  = In (Mul x y)
x ==. y = In (Eq x y)

eIf p tru fls = In (If p tru fls)

newtype Expr = In { out :: TExpr Expr } deriving (Eq, Ord)

instance Show Expr where
    show v = case out v of
        Lit i -> show i
        Var s -> s
        Add p q -> paren $ show p ++ " + " ++ show q
        Mul p q -> paren $ show p ++ " * " ++ show q
        And p q -> paren $ show p ++ " `and` " ++ show q
        Or  p q -> paren $ show p ++ " `or` " ++ show q    
        Eq  p q -> paren $ show p ++ " == " ++ show q
        If p l r -> paren $ "if " ++ paren (show p) ++ " then " ++ show l ++ " else " ++ show r

paren :: String -> String
paren xs = '(':xs ++ ")"

newtype EqExpr = EqExpr {unEqExpr :: TExpr (Opt.EqRepr EqExpr)}

instance Ord EqExpr where
    compare (EqExpr x) (EqExpr y) = compare x y 

instance Eq EqExpr where
    (EqExpr x) == (EqExpr y) = x == y

type EqRepr = Opt.EqRepr EqExpr 

type Opt = OptMonad EqExpr

{-
addExpr :: Expr -> Opt EqRepr
addExpr exp = case out exp of
    Lit i    -> addTerm (EqExpr $ Lit i)
    Var x    -> addTerm (EqExpr $ Var x)
    Add x y  -> addBinTerm Add x y
    Mul x y  -> addBinTerm Mul x y
    And x y  -> addBinTerm And x y
    Or  x y  -> addBinTerm Or  x y
    Eq  x y  -> addBinTerm Eq  x y
    If x y z -> addTriTerm If x y z
  where
    addBinTerm op x y = do
        x' <- addExpr x
        y' <- addExpr y
        c <- addTerm (EqExpr $ op x' y')
        c `dependOn` [x',y']
        return c
    addTriTerm op x y z = do
        x' <- addExpr x
        y' <- addExpr y
        z' <- addExpr z
        c <- addTerm (EqExpr $ op x' y' z')
        c `dependOn` [x',y', z']
        return c
-}

addTerm :: EqExpr -> Opt EqRepr
{-addTerm t@(EqExpr (Add p1 p2)) = do
    r <- getClass t
    case r of
        Nothing -> do classes <- getClasses
                      eqs <- forM classes $ \c -> do
                        terms <- getElems c
                        liftM concat $ forM terms $ \term -> 
                            case term of
                                EqExpr (Add q1 q2) -> do 
                                    b <- liftM2 (&&) (equivalent p1 q1) (equivalent p2 q2)
                                    if b then return [c] else return []
                                _         -> return []
                      case concat eqs of
                        []    -> makeClass t
                        (x:xs) -> foldM union x xs--return x
        Just x -> return x
-}
addTerm t = do
    rs <- getClassOpt t
    case rs of
        []  -> makeClass t
        (c:cls)  -> foldM union c cls

getClassOpt :: EqExpr -> Opt [EqRepr]
getClassOpt term = do
    cls <- getClasses
    flip filterM cls $ \c -> do
        anyM (similar term) =<< getElems c

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM p []       = return False
anyM p (x : xs) = do
    b <- p x
    if b
        then return True
        else anyM p xs

similar :: EqExpr -> EqExpr -> Opt Bool
similar (EqExpr (Lit i)) (EqExpr (Lit i')) = return (i == i')
similar (EqExpr (Var v)) (EqExpr (Var v')) = return (v == v')
similar (EqExpr (Add x y)) (EqExpr (Add x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar (EqExpr (Mul x y)) (EqExpr (Mul x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar (EqExpr (Or x y)) (EqExpr (Or x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar (EqExpr (And x y)) (EqExpr (And x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar (EqExpr (Eq x y)) (EqExpr (Eq x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar (EqExpr (If x y z)) (EqExpr (If x' y' z')) 
    = and `fmap` zipWithM equivalent [x,y,z] [x',y',z']
similar _ _ = return False

myUnion :: (Bool, EqRepr) -> EqRepr -> Opt (Bool, EqRepr)
myUnion (b, x) y = do
    b' <- equivalent x y
    if b'
        then return (b, x)
        else do
            c <- union x y
            return (True, c)

addTermToClass :: EqExpr -> Maybe EqRepr -> Opt (Bool, EqRepr)
addTermToClass term Nothing    = do
    rs <- getClassOpt term
    c' <- case rs of
        []  -> makeClass term
        (c:cls)  -> foldM union c cls 
    return (False, c')
addTermToClass term (Just cls) = do -- addTerm term >>= union cls
    r <- getClassOpt term
    case r of
        [] -> addElem term cls >> return (True, cls)
        cl -> foldM myUnion (False, cls) cl
    {-terms <- getElems cls
    xs <- filterM (similar term) terms
    if null xs
        then do
            r <- getClassOpt term
            case r of
                [] -> addElem term cls >> return cls
                cl -> foldM union cls cl
        else return cls
    -}
{- old 
        then addElem term cls >> return cls
            -- union cls =<< addTerm term 
            -- since we already know the class we could just add it directly
        else return cls 
-}


