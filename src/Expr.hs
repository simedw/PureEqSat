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

data TExpr r 
    = Lit Integer
    | Var String
    | Add r r
    | Mul r r
    deriving (Eq, Ord, Show)

lit = In . Lit
var = In . Var
x +. y = In (Add x y)
x *. y = In (Mul x y)

-- Skall vi trixa med något som detta?
--newtype Fix f = In { out :: f (Fix f) } deriving (Eq, Ord)
newtype Expr = In { out :: TExpr Expr } deriving (Eq, Ord)

instance Show Expr where
    show v = case out v of
        Lit i -> show i
        Var s -> s
        Add p q -> paren $ show p ++ " + " ++ show q
        Mul p q -> paren $ show p ++ " * " ++ show q

paren :: String -> String
paren xs = '(':xs ++ ")"

newtype EqExpr = EqExpr {unEqExpr :: TExpr (Opt.EqRepr EqExpr)}

instance Ord EqExpr where
    compare (EqExpr x) (EqExpr y) = compare x y 

instance Eq EqExpr where
    (EqExpr x) == (EqExpr y) = x == y

type EqRepr = Opt.EqRepr EqExpr 

type Opt = OptMonad EqExpr

addExpr :: Expr -> Opt EqRepr
addExpr (In (Lit i)) = addTerm (EqExpr $ Lit i)
addExpr (In (Var x)) = addTerm (EqExpr $ Var x)
addExpr (In (Add x y)) = do
    x' <- addExpr x
    y' <- addExpr y
    c <- addTerm (EqExpr $ Add x' y')
    c `dependOn` [x',y']
    return c
addExpr (In (Mul x y)) = do
    x' <- addExpr x
    y' <- addExpr y
    c <- addTerm (EqExpr $ Mul x' y')
    c `dependOn` [x',y']
    return c

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
    r <- getClass t
    case r of
        Nothing  -> makeClass t
        Just rep -> return $ rep

similar :: EqExpr -> EqExpr -> Opt Bool
similar (EqExpr (Lit i)) (EqExpr (Lit i')) = return (i == i')
similar (EqExpr (Var v)) (EqExpr (Var v')) = return (v == v')
similar (EqExpr (Add x y)) (EqExpr (Add x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar (EqExpr (Mul x y)) (EqExpr (Mul x' y')) 
    = liftM2 (&&) (equivalent x x') (equivalent y y')
similar _ _ = return False

addTermToClass :: EqExpr -> Maybe EqRepr -> Opt EqRepr
addTermToClass term Nothing    = addTerm term
addTermToClass term (Just cls) = union cls =<< addTerm term
    {- -- union cls =<< addTerm term
    terms <- getElems cls
    xs <- filterM (similar term) terms
    if null xs
        then do
            r <- getClass term
            case r of
                Nothing -> addElem term cls >> return cls
                Just cl -> union cl cls
        else return cls
    -}
{- old 
        then addElem term cls >> return cls
            -- union cls =<< addTerm term 
            -- since we already know the class we could just add it directly
        else return cls 
-}

