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
newtype Fix f = In { out :: f (Fix f) }
type Expr = Fix TExpr

newtype EqExpr = EqExpr (TExpr (Opt.EqRepr EqExpr))

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
    return c
addExpr (In (Mul x y)) = do
    x' <- addExpr x
    y' <- addExpr y
    addTerm (EqExpr $ Mul x' y')

addTerm :: EqExpr -> Opt EqRepr
{-addTerm t@(Add p1 p2) = do
    r <- getClass t
    case r of
        Nothing -> do classes <- getClasses
                      eqs <- forM classes $ \c -> do
                        terms <- getElems c
                        liftM concat $ forM terms $ \term -> 
                            case term of
                                Add q1 q2 -> do b <- liftM2 (&&) (equivalent p1 q1) (equivalent p2 q2)
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

--addTermToClass :: TExpr EqRepr -> EqRepr -> Opt EqRepr
--addTermToClass term cls = union cls =<< addTerm term 

