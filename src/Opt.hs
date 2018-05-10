module Opt 
    ( OptMonad    -- :: * -> * -> *
    , D.EqRepr    -- :: * -> *
    , addElem       -- :: (Ord e) => e -> EqRepr e -> EqMonad e (EqRepr e)
    , dependOn      -- :: EqRepr e -> [EqRepr e] -> EqMonad e ()
    , equivalent    -- :: EqRepr e -> EqRepr e -> EqMonad e Bool
    , getClass      -- :: (Ord e) => e -> EqMonad e [EqRepr e]
    , getClasses    -- :: EqMonad e [EqRepr e]
    , getDependOnMe -- :: EqRepr e -> EqMonad e [EqRepr e]
    , getDepth      -- :: EqRepr s -> EqMonad s (Maybe Depth)
    , getElems      -- :: EqRepr e -> EqMonad e [e]
    , getPtr        -- :: EqRepr e -> EqMonad e Int
    , makeClass     -- :: eqElem -> IOSet eqElem (EqRepr eqElem)
    , nubClasses    -- :: [EqRepr e] -> EqMonad e [EqRepr e]
    , root          -- :: EqRepr s -> IOSet s (EqRepr s)
    , runOpt        -- :: OptMonad s a -> IO a
    , union         -- :: (Ord e) => EqRepr e -> EqRepr e -> IOSet e (EqRepr e)
    , updated       -- :: EqRepr e -> Maybe Depth -> EqMonad e ()
    ) where

import Data.Foldable (toList)
import qualified IOSetA as D -- för att kunna ha samma namn fast lifted
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.Map as M
import qualified Data.Set as S

type OptMonad eqElem = (D.EqMonad eqElem)

runOpt :: OptMonad s a -> IO a
runOpt o = D.runEqClass o

makeClass x     = D.makeClass x
equivalent x y  = D.equivalent x y
getElems x      = D.getElems x 
getClass x      = D.getClass x
-- getClasses :: OptMonad eqElem [D.EqRepr eqElem]
getClasses      = D.getClasses
updated x y     = D.updated x y
getDepth x      = D.getDepth x
nubClasses xs   = D.nubClasses xs
root x          = D.root x
dependOn x xs   = D.dependOn x xs
getDependOnMe x = D.getDependOnMe x

addElem x cls = do 
    D.addElem x cls
    deps <- getDependOnMe cls
    updateDepDepth (S.singleton cls) 1 deps    
    return cls

getPtr rep = do
    D.Root p _ _ <- D.rootIO rep
    return p

union x y 
  | x == y    = do
    return x
  | otherwise = do
    b <- equivalent x y
    if b 
        then return x
        else do
            c <- D.union x y 
            deps <- getDependOnMe c
            updateDepDepth (S.singleton c) 1 deps
            return c 
  
updateDepDepth :: S.Set (D.EqRepr s) -> Int -> [D.EqRepr s] -> OptMonad s ()
updateDepDepth set depth [] = return ()
updateDepDepth set depth (cls:classes) 
    | cls `S.member` set = updateDepDepth set depth classes
    | otherwise = do 
        updated cls (Just depth) 
        deps <- getDependOnMe cls
        updateDepDepth (S.insert cls set) (depth+1) deps
        updateDepDepth (S.insert cls set) depth classes
