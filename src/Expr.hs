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

data BinOp
    = Add'
    | Mul'
    | And'
    | Or'
    | Eq'
  deriving(Eq, Ord, Show)

data TriOp
    = If'
  deriving(Eq, Ord, Show)

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
{-
ordning vi parsar, alla är left recursive (dock borde kanske inte == vara det)
       [ [ "*" --> (*.)]
       , [ "+" --> (+.)]
       , [ "==" --> (==.)]
       , [ "&&" --> eAnd]
       , [ "||" --> eOr]
-}

instance Show Expr where
    showsPrec p e = case out e of
        Lit (LInteger i) -> shows i
        Lit (LBool b)    -> shows b
        Var x            -> showString x
        -- osäker på siffrorna :)
        Add e1 e2  -> showParen (p > 4) $
            showsPrec 4 e1 . showString " + " . showsPrec 5 e2
        Mul e1 e2  -> showParen (p > 5) $
            showsPrec 5 e1 . showString " * " . showsPrec 6 e2
        And e1 e2  -> showParen (p > 2) $
            showsPrec 2 e1 . showString " && " . showsPrec 3 e2
        Or e1 e2  -> showParen (p > 1) $
            showsPrec 1 e1 . showString " || " . showsPrec 2 e2
        Eq e1 e2  -> showParen (p > 3) $
            showsPrec 4 e1 . showString " == " . showsPrec 4 e2
        If e1 e2 e3  -> showParen (p > 0) $
            showString "if " . showsPrec 1 e1 
                             . showString " then " 
                             . showsPrec 1 e2
                             . showString " else "
                             . showsPrec 1 e3

paren :: String -> String
paren xs = '(':xs ++ ")"

newtype EqExpr = EqExpr {unEqExpr :: TExpr (Opt.EqRepr EqExpr)}

instance Ord EqExpr where
    compare (EqExpr x) (EqExpr y) = compare x y 

instance Eq EqExpr where
    (EqExpr x) == (EqExpr y) = x == y

type EqRepr = Opt.EqRepr EqExpr 

type Opt = OptMonad EqExpr

-- | add a new term, if the term already exists we will return that term.
addTerm :: EqExpr -> Opt EqRepr
addTerm t = do
    rs <- getClassOpt t
    case rs of
        []  -> makeClass t
        (c:cls)  -> foldM union c cls

getTermDep :: EqExpr -> Opt [EqRepr]
getTermDep term = case unEqExpr term of
    Lit _ -> getClasses
    Var _ -> getClasses
    Add x y  -> comb x y
    Mul x y  -> comb x y
    And x y  -> comb x y
    Or x y   -> comb x y
    Eq x y   -> comb x y
    If x y z -> do
        l <- getDependOnMe x
        c <- getDependOnMe y
        r <- getDependOnMe z
        nubClasses (l ++ c ++ r) 
  where
    comb x y = do
        l <- getDependOnMe x
        r <- getDependOnMe y
        nubClasses (l ++ r)

getClassOpt :: EqExpr -> Opt [EqRepr]
getClassOpt term = do
    cls <- getTermDep term
    flip filterM cls $ \c -> do
        anyM (similar term) =<< getElems c

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM p []       = return False
anyM p (x : xs) = do
    b <- p x
    if b
        then return True
        else anyM p xs

andM :: Monad m => (a -> m Bool) -> [a] -> m Bool
andM p []       = return True
andM p (x : xs) = do
    b <- p x
    if b
        then andM p xs
        else return False

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
addTermToClass term (Just cls) = do
    r <- getClassOpt term
    case r of
        [] -> addElem term cls >> return (True, cls)
        cl -> foldM myUnion (False, cls) cl
