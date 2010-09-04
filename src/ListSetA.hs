{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module ListSetA where


import Control.Monad
import "mtl" Control.Monad.State

import qualified Data.Map as M
import Data.Map (Map)

import Data.Maybe

{-
 - Naive implementation of DisjointSets
 - Each class is represented by a integer
 - and there is map: Int -> [elements] 
 - 
 - Pros:
 - * equivalent is really fasy
 - * makeClass, union is as fast as append
 - Cons:
 - * getClass is slow 
 -}


newtype ListSet s a = LS { runLS :: State (LState s) a }
    deriving (MonadState (LState s), Monad)

data LState s = LState
    { classes :: Map Int (Either Int [s])
    , number  :: Int
    }

(.!) :: Map Int (Either Int [a]) -> Int -> [a]
map .! v = case map M.! v of
    Left v'  -> map .! v'
    Right xs -> xs

type EqMonad = ListSet

type EqRepr = Int

makeClass :: eqElem -> ListSet eqElem EqRepr
makeClass t = do
    n <- gets number
    c <- gets classes
    modify $ \s -> s { number  = n + 1
                     , classes = M.insert n (Right [t]) c 
                     }
    return n

equivalent :: EqRepr -> EqRepr -> ListSet eqElem Bool
equivalent x y = return (x == y)

union :: EqRepr -> EqRepr -> ListSet eqElem EqRepr
union x y = do
    cls <- gets classes
    let c1 = cls .! x
        c2 = cls .! y
        m  = max x y
    modify $ \s -> s { classes = M.insert (max x y) (Right $ c1 ++ c2) 
                                          (M.insert x (Left m) 
                                          (M.insert y (Left m) cls)) }
    return m

getElems :: EqRepr -> ListSet eqElem [eqElem]
getElems x = do
    c <- gets classes
    case M.lookup x c of
        Nothing -> return []
        Just (Left x') -> getElems x'
        Just (Right xs) -> return xs

getClass :: Eq eqElem => eqElem -> ListSet eqElem (Maybe EqRepr)
getClass z = do
    c <- gets classes
    let c' = map (\(x,y) -> case y of
         Left _    -> ([],x)
         Right xs  -> (xs,x)) $ M.toAscList c
    return $ listToMaybe $ map snd $ filter (\(xs, x) -> z `elem` xs) c' 

runEqClass m = evalState (runLS m) $ LState { classes = M.empty, number = 0 }
