{-# LANGUAGE PackageImports #-}
module Opt 
    ( OptMonad
    , D.EqRepr
--    , Rule(..)
--    , MetaData(..)
--    , Result(..)
    , makeClass
    , equivalent -- :: EqRepr       -> EqRepr m -> m Bool
    , union      -- :: EqRepr       -> EqRepr m -> m (EqRepr m)
    , getElems   -- :: EqRepr                   -> m [EqElem m]
    , getClass   -- :: Eq (EqElem m) => EqElem m -> m (Maybe (EqRepr m))
    , getClasses
    , runOpt -- :: m a -> a
--    , markDirty
--   , isDirty
    , setShouldNotApply
    , resetClass
    , shouldApply
  --  , addRule
  --  , addRules
  --  , getTopRule
  --  , getRules
    ) where

import Data.Foldable (toList)
import qualified DisjointSetA as D -- för att kunna ha samma namn fast lifted
import Control.Monad
import "mtl" Control.Monad.State.Strict
import qualified Data.Map as M
import qualified Data.Sequence as Q -- har O(1) cons och snoc, pa Seq
import qualified Data.Set as S

-- data Rule eqElem = Rule MetaData (D.EqRepr -> eqElem -> OptMonad eqElem Result)
-- Map ID (Map Axiom Bool)
-- Map Axiom (Map ID Bool) <-- tror jag, för vi applicerar samma axiom över flera klasser
-- vilket ar bast? sure, vi later axiom vara typ en int vart i listan over relger det ar eller nagot sant...  fast vi har inte tillgang till Rules har
-- carp circulare import hade varit nice, är en post på cafe om det just nu, kanske de kan fixa det. hade varit skont.

type Axiom = Int
--type RuleBitMask = M.Map Axiom (M.Map D.EqRepr Bool)
--type RuleBitMask s = M.Map (D.EqRepr s) (S.Set Axiom)
type RuleBitMask s = [(D.EqRepr s, S.Set Axiom)]

type OptMonad eqElem = StateT (RuleBitMask eqElem) (D.EqMonad eqElem)

runOpt :: OptMonad s a -> IO a
runOpt o = D.runEqClass (evalStateT o [])

makeClass x = lift (D.makeClass x)
equivalent x y = lift (D.equivalent x y)
--union x y = lift (D.union x y) >>= \s -> resetClass s >> return s
getElems x = lift (D.getElems x) 
getClass x = lift (D.getClass x)
getClasses :: OptMonad eqElem [D.EqRepr eqElem]
getClasses = lift D.getClasses

union x y | x == y    = return x
          | otherwise = lift (D.union x y) >>= \s -> resetClass s >> return s



setShouldNotApply :: Axiom -> D.EqRepr s -> OptMonad s ()
setShouldNotApply ax rep = do 
    classes <- get
    let mq = lookup rep classes
    case mq of
        Nothing  -> put $ insert rep (S.singleton ax) classes
        Just cls -> put $ insert rep (S.insert ax cls) classes

insert key value list = (key,value) : list


resetClass :: D.EqRepr s -> OptMonad s ()
resetClass rep = do
    classes <- get
    put $ insert rep S.empty classes

shouldApply :: Axiom -> D.EqRepr s -> OptMonad s Bool
shouldApply ax rep = do
    classes <- get
    let axioms = lookup rep classes
    case axioms of
        Nothing -> return True
        Just m  -> return $ not $ S.member ax m
