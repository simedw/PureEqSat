{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module DisjointSet where

{-
  What we want:
  * create new equivalences classes
  * are two terms in the same classes
  * join to classes 
  * list all elements in a class
  * from a term get the class
-}

class Monad m => EqClass m where
    type EqElem m
    data EqRepr m
    
    makeClass  :: EqElem m                  -> m (EqRepr m) 
    equivalent :: EqRepr m      -> EqRepr m -> m Bool
    union      :: EqRepr m      -> EqRepr m -> m (EqRepr m)
    getElems   :: EqRepr m                  -> m [EqElem m]
    getClass   :: Eq (EqElem m) => EqElem m -> m (Maybe (EqRepr m))
    runEqClass :: m a -> a
	
