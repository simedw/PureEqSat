{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeFamilies #-}
module ListSetA where


import Control.Monad
import "mtl" Control.Monad.State

import qualified Data.Map as M
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as S

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
    { classes :: Map Int (Either Int (Set s))
    , number  :: Int
    }

(.!) :: Map Int (Either Int a) -> Int -> a
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
                     , classes = M.insert n (Right (S.singleton t)) c 
                     }
    return n

equivalent :: EqRepr -> EqRepr -> ListSet eqElem Bool
equivalent x y | x == y    = return True
               | otherwise = do
    cls <- gets classes
    case M.lookup x cls of
        Nothing -> error ""
        Just (Left x') -> equivalent x' y
        Just (Right _) -> case M.lookup y cls of
            Nothing -> error ""
            Just (Left y') -> equivalent x y'
            Just (Right _) -> return (x == y)

{-
equivalent x y = {-return (x == y) -} do
    cls <- gets classes
    case M.lookup x cls of
        Nothing -> error ""
        Just (Left x') -> equivalent x' y
        Just (Right _) -> case M.lookup y cls of
            Nothing -> error ""
            Just (Left y') -> equivalent x y'
            Just (Right _) -> return (x == y)
-}
union :: Ord eqElem => EqRepr -> EqRepr -> ListSet eqElem EqRepr
union x y | x == y    = return x
          | otherwise = do
    cls <- gets classes
    let c1 = cls .! x
        c2 = cls .! y
        m  = max x y
    modify $ \s -> s { classes = M.insert m (Right $ c1 `S.union` c2) 
                                          (M.insert x (Left m) 
                                          (M.insert y (Left m) cls)) }
    return m

getElems :: EqRepr -> ListSet eqElem [eqElem]
getElems x = do
    c <- gets classes
    case M.lookup x c of
        Nothing -> return []
        Just (Left x') -> getElems x'
        Just (Right xs) -> return $ S.toList xs

getClass :: Ord eqElem => eqElem -> ListSet eqElem (Maybe EqRepr)
getClass z = do
    c <- liftM M.toList $ gets classes
    return $ listToMaybe [ cls | (cls, Right xs) <- c, z `S.member` xs]
--gets classes ger oss Mapen, borde bli battre om an fulare :(
--okej, getClasses ger ju bara intar till classes, och isf far vi ta getElems pa varje get class innan vi kan hitta vart element....

{-
getClass z = do
    c <- gets classes
    let c' = map (\(x,y) -> case y of
         Left _    -> ([],x)
         Right xs  -> (xs,x)) $ M.toAscList c
    return $ listToMaybe $ map snd $ filter (\(xs, x) -> z `elem` xs) c' 
-}

runEqClass m = evalState (runLS m) $ LState { classes = M.empty, number = 0 }


getClasses :: ListSet eqElem [EqRepr]
getClasses = liftM (map fst . M.toList)  $ gets classes
