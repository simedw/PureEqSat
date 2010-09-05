{-# OPTIONS_GHC -F -pgmF she #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
module Expr where

import Opt
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

-- pattern (EAdd x y) = Add (In x) (In y)

type Opt = OptMonad (TExpr EqRepr)

addExpr :: Expr -> Opt EqRepr
addExpr (In (Lit i)) = addTerm (Lit i)
addExpr (In (Var x)) = addTerm (Var x)
addExpr (In (Add x y)) = do
    x' <- addExpr x
    y' <- addExpr y
    c <- addTerm (Add x' y')
--    trace (show c) $ addRule c comm -- kanske ska ha den i flip i opt?
    return c
addExpr (In (Mul x y)) = do
    x' <- addExpr x
    y' <- addExpr y
    addTerm (Mul x' y')

addTerm :: TExpr EqRepr -> Opt EqRepr
addTerm x = do
    r <- getClass x
    case r of
        Nothing  -> makeClass x
        Just rep -> return rep

{-
assoc :: Rule (TExpr EqRepr)
assoc = Rule (Name "assoc") $ \ cls eqElem -> do
    case eqElem of
        Add x y -> do
            xs <- getClass x
            
            undefined
            -- hmm gå igenom och leta Add noder? bada hoger och vanster? tror vi får båda via commutative
            -- . Men om det inte finns i hoger och vi kolla till vanster... om ordningen ar fel pa reglerna
        _ -> return Failed
-}
comm :: Rule (TExpr EqRepr)
comm = Rule (Name "commutative") $ \cls eqElem -> trace "körs in" $ do
    case eqElem of
        Add x y -> do
            p <- addTerm (Add y x)
            bo <- equivalent p cls
            case not bo of
                True  -> trace "körs" $ union p cls >> return Applied
                False -> trace "already" $ return Failed

runARule :: EqRepr -> TExpr EqRepr -> Opt Result
runARule cls rep = trace "testa" $ do 
    rule <- getTopRule cls
    case rule of
        Just (Rule meta f)  -> trace "hitta regel" $ f cls rep
        Nothing -> trace "fail" $ return Failed 



    {-
    res <- forM elems $ \rep -> case (pattern,rep) of
        (Pattern (Left (Add q1 q2)), Add p1 p2) -> do
            r1 <- applyPattern q1 p1 
            r2 <- applyPattern q2 p2
            return $ fun r1 r2 
        (PAny i, _)             -> return [[(i,cls)]]
        _                       -> return []
    -}
    --return $ res

