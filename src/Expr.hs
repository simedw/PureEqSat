{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Expr where

import Opt
import Debug.Trace

data TExpr r 
    = Lit Integer
    | Var String
    | Add r r
    | Mul r r
    deriving (Eq, Show)

lit = In . Lit
var = In . Var
x +. y = In (Add x y)
x *. y = In (Mul x y)

-- Skall vi trixa med något som detta?
newtype Fix f = In { out :: f (Fix f) }
type Expr = Fix TExpr

-- pattern (EAdd x y) = Add (In x) (In y)

{- att skicka runt?
   Map EqRepr (Queue Rules)
-}

-- opt som i optimize? mm, så kan vi lägga på en StateT för bookkeeping, visst
-- dels vill jag göra det här och dels i en annan fil som exporterar DisjointSet fast med lift
{-
  BookKeep----Top
           /      \
     DisjointSetA   \        typ lägga till en ny top och ha att den slår ihop DisjointA med BookKeep
      /              \
   ListSet*         Expr
      \            /
          TestExpr
     
     hur vill du andra den? sa Expr importerar Top?
-}

type Opt = OptMonad (TExpr EqRepr)

addExpr :: Expr -> Opt EqRepr
addExpr (In (Lit i)) = addTerm (Lit i)
addExpr (In (Var x)) = addTerm (Var x)
addExpr (In (Add x y)) = do
    x' <- addExpr x
    y' <- addExpr y
    c <- addTerm (Add x' y')
    trace (show c) $ addRule c comm -- kanske ska ha den i flip i opt?
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
