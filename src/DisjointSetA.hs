module DisjointSetA
    ( EqMonad
    , EqRepr
    , makeClass  -- :: EqElem                   -> m (EqRepr m)
    , equivalent -- :: EqRepr       -> EqRepr m -> m Bool
    , union      -- :: EqRepr       -> EqRepr m -> m (EqRepr m)
    , getElems   -- :: EqRepr                   -> m [EqElem m]
    , getClass   -- :: Eq (EqElem m) => EqElem m -> m (Maybe (EqRepr m))
    , runEqClass -- :: m a -> a
    ) where

import ListSetA