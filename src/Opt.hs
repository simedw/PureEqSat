{-# LANGUAGE PackageImports #-}
module Opt 
    ( OptMonad
    , D.EqRepr
    , Rule(..)
    , MetaData(..)
    , Result(..)
    , makeClass
    , equivalent -- :: EqRepr       -> EqRepr m -> m Bool
    , union      -- :: EqRepr       -> EqRepr m -> m (EqRepr m)
    , getElems   -- :: EqRepr                   -> m [EqElem m]
    , getClass   -- :: Eq (EqElem m) => EqElem m -> m (Maybe (EqRepr m))
    , getClasses
    , runOpt -- :: m a -> a
    , addRule
    , addRules
    , getTopRule
    , getRules
    ) where

import Data.Foldable (toList)
import qualified DisjointSetA as D -- för att kunna ha samma namn fast lifted
import Control.Monad
import "mtl" Control.Monad.State.Strict
import qualified Data.Map as M
import qualified Data.Sequence as Q -- har O(1) cons och snoc, pa Seq

data Rule eqElem = Rule MetaData (D.EqRepr -> eqElem -> OptMonad eqElem Result)

instance Show (Rule e) where
    show (Rule meta _) = "RULE :" ++ show meta

data MetaData = None
              | Name String
              | Combine [MetaData]
              deriving Show
              
data Result = Applied | Retry | Failed -- ? vi kan testa det, blir nog bra :)
--Here'Be'Rules
-- Rule MetaData (EqRepr -> OptMonad EqRepr)
-- Rule MetaData (EqRepr -> OptMonad Bool) -- om den applicerades eller inte, eller om den ska laggas till igen?
-- Rule MetaData (
type Rules e = [Rule e]

type OptMonad eqElem = StateT (M.Map D.EqRepr (Q.Seq (Rule eqElem))) (D.EqMonad eqElem)

runOpt :: OptMonad s a -> a
runOpt o = D.runEqClass (evalStateT o M.empty)

makeClass x = lift (D.makeClass x)
equivalent x y = lift (D.equivalent x y)
union x y = lift (D.union x y)
getElems x = lift (D.getElems x) 
getClass x = lift (D.getClass x)
getClasses :: OptMonad eqElem [D.EqRepr]
getClasses = lift D.getClasses

addRule  :: D.EqRepr -> Rule s -> OptMonad s ()
addRule rep rule = do 
    ma <- get
    let mq = (M.lookup rep) ma
    flip (maybe (put $ M.insert rep (Q.empty Q.|> rule) ma)) mq $ \q -> do
        put $ M.insert rep (q Q.|> rule) ma

addRules :: D.EqRepr -> Rules s -> OptMonad s ()
addRules rep rules = mapM_ (addRule rep) rules

getTopRule  :: D.EqRepr -> OptMonad s (Maybe (Rule s)) -- tar en i taget, tar bort isf?
getTopRule rep = do
    ma <- get
    let mq = (M.lookup rep) ma
    flip (maybe (return Nothing)) mq $ \q ->
        case Q.viewl q of
            Q.EmptyL -> return Nothing
            x Q.:< rest -> do
                put $ M.insert rep rest ma
                return (Just x) -- mm :)

-- Skall den ta bort också?
getRules :: D.EqRepr -> OptMonad s (Rules s)
getRules rep = do
    ma <- get
    let mq = M.lookup rep ma
    return $ maybe [] toList mq