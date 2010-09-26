{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}

module IOSetA where

import Control.Monad
import "mtl" Control.Monad.State.Strict

import Data.IOStableRef
import Data.Maybe (listToMaybe)
import qualified Data.Set as S
import Data.Set (Set)
import Test.QuickCheck

newtype IOSet s a = IS { runLS :: StateT (IState s) IO a }
    deriving (MonadState (IState s), Monad, MonadIO, Functor)

data IState s = IState
    { classes :: [EqRepr s] -- Only pointers to Root elems!
    , number  :: CompareType
    }

type EqMonad = IOSet

type EqRepr s = IOStableRef (MinEqRepr s)

type Depth = Int
type Rank  = Int
type CompareType = Int
data MinEqRepr s 
  = Root CompareType Rank (EqData s)
  | Node (EqRepr s)

data EqData s = EqData
    { eqSet  :: (Set s)              -- ^ terms
    , eqDependOnMe :: [EqRepr s]     -- ^ if we are x then list of y such as x <| y 
    , eqIDependOn  :: Set (EqRepr s) -- ^ if we are x then list of y such as y <| x
    , depth :: Maybe Depth  -- ^ if we are x then min n such that y <|^n x, where y has changed
    }

-- | Union for the EqData, will also set depth to zero
unionFunction :: Ord s => EqData s -> EqData s -> EqMonad s (EqData s)
unionFunction x y = do
    mdeps <- nubClasses (eqDependOnMe x ++ eqDependOnMe y)
    return EqData
            { eqSet        = eqSet x `S.union` eqSet y
            , eqDependOnMe = mdeps
            , eqIDependOn   = eqIDependOn x `S.union` eqIDependOn y
            , depth  = Just 0 
            }

makeData :: s -> EqData s
makeData s = EqData
    { eqSet = S.singleton s
    , eqDependOnMe = []
    , eqIDependOn  = S.empty
    , depth        = Just 0
    }

-- | Returns a pointer to a root node for a given class
root :: EqRepr s -> EqMonad s (EqRepr s)
root rep = do
    v <- liftIO $ readIOStableRef rep
    case v of
        r@(Root _ _ _) -> return rep
        Node parent    -> do
            r <- root parent
            liftIO $ writeIOStableRef rep (Node r)
            return r

-- | Returns a root node for a given class
rootIO :: EqRepr s -> EqMonad s (MinEqRepr s)
rootIO rep = do
    ioroot <- root rep
    liftIO $ readIOStableRef ioroot

-- | Creates a new class with one term in it.
makeClass :: eqElem -> EqMonad eqElem (EqRepr eqElem)
makeClass elem = do
    nr <- gets number
    v <- liftIO $ newIOStableRef (Root nr 0 (makeData elem))
    modify $ \ s -> s { classes = v : classes s
                      , number= nr + 1
                      }
    return v

-- | Checks if two classes are equivalent in other words pointing 
--   to the same root node
equivalent :: EqRepr e -> EqRepr e -> EqMonad e Bool
equivalent x y = do
    (Root cx _ _) <- rootIO x
    (Root cy _ _) <- rootIO y
    return (cx == cy)

-- | Combine two classes to create a new one, the old class pointers will
--   point forward the new class.
union :: Ord e => EqRepr e -> EqRepr e -> EqMonad e (EqRepr e)
union iox ioy = do
    (Root xc xrank xdata) <- rootIO iox
    (Root yc yrank ydata) <- rootIO ioy
    case (xrank > yrank, xrank < yrank, xc /= yc) of
        (True , _   , _   ) -> iox `setRootTo` ioy
        (False,True , _   ) -> ioy `setRootTo` iox
        (False,False, True) -> incRank =<< iox `setRootTo` ioy
        _                   -> return iox
  where
    -- make y the root of x
    setRootTo :: Ord e => EqRepr e -> EqRepr e -> EqMonad e (EqRepr e)
    setRootTo x y = do
        x <- root x
        y <- root y
        (Root cx xrank xdata) <- rootIO x
        (Root cy yrank ydata) <- rootIO y
        dat <- ydata `unionFunction` xdata
        liftIO $ writeIOStableRef y $ Root (min cx cy) yrank dat
        liftIO $ writeIOStableRef x $ Node y
        return y

    incRank :: EqRepr e -> IOSet e (EqRepr e)
    incRank x = do
        x <- root x
        Root c rank dat <- rootIO x
        liftIO $ writeIOStableRef x (Root c (rank + 1) dat)
        return x

-- | Adds a new term to a given class and updates the depth
addElem :: Ord e => e -> EqRepr e -> EqMonad e ()
addElem elem rep = do
    rep <- root rep
    Root c r dat <- rootIO rep
    liftIO $ writeIOStableRef rep (Root c r dat { eqSet = S.insert elem (eqSet dat) 
                                                , depth = Just 0})

-- | Get all terms from a given class.
getElems :: EqRepr e -> EqMonad e [e]
getElems x = do
    Root _ _ dat <- rootIO x
    return $ S.toList (eqSet dat)

-- | Given a term, check which classes it belongs to, notice that this function
--   is not really reliable and you should use other methods.
getClass :: Ord e => e -> EqMonad e [EqRepr e]
getClass elem = do
    cls <- getClasses
    liftM (concat) $ forM cls $ \c -> do
        Root _ _ dat <- rootIO c
        case elem `S.member` eqSet dat of
            True  -> return [c]
            False -> return []

-- | Get all classes that exists in this graph
getClasses :: EqMonad e [EqRepr e]
getClasses = do
    cls <- gets classes
    ls <- fun cls S.empty
    modify $ \s -> s { classes = ls}
    return ls
  where
    fun [] set = return []
    fun (cls : classes) set = do
        eq <- liftIO $ readIOStableRef cls
        case eq of
            Root c _ _ | c `S.member` set -> fun classes set
                       | otherwise        -> liftM (cls :) $  fun classes (S.insert c set)
            _ -> fun classes set

-- | Given a list of classes, update all pointers and make sure you only have one
--   pointer to each class.
nubClasses :: [EqRepr e] -> EqMonad e [EqRepr e]
nubClasses cls = fun cls S.empty
  where
    fun [] set = return []
    fun (cls : classes) set = do
        cls <- root cls
        eq <- liftIO $ readIOStableRef cls
        case eq of
            Root c _ _ | c `S.member` set -> fun classes set
                       | otherwise        -> liftM (cls :) $  fun classes (S.insert c set)

  
-- | For a class x gives all y such that x <| y
getDependOnMe :: EqRepr e -> EqMonad e [EqRepr e]
getDependOnMe rep = do
    rep <- root rep
    Root c r dat <- rootIO rep
    mdeps <- nubClasses (eqDependOnMe dat)
    liftIO $ writeIOStableRef rep $ Root c r dat { eqDependOnMe = mdeps }
    return mdeps

-- | Make a class depend on a bunch of other classes, setsup the <| relation in
--   both ways
dependOn :: EqRepr e -> [EqRepr e] -> EqMonad e ()
p `dependOn` ps = do
    p <- root p
    Root c r dat <- rootIO p
    liftIO $ writeIOStableRef p $ Root c r dat { eqIDependOn = eqIDependOn dat `S.union` S.fromList ps}
    forM_ ps $ \ dep -> do
        dep <- root dep
        Root cd rd dat <- rootIO dep
        liftIO $ writeIOStableRef dep $ Root cd rd dat { eqDependOnMe = p : eqDependOnMe dat }

-- | Set the depth, if the class doesn't have a depth currently set it unconditionally
--   otherwise set it to the smallest value (unless you set it to Nothing in which
--   case you mean that it has no more changes). 
updated :: EqRepr e -> Maybe Depth -> EqMonad e ()
updated cls deep = do
    cls <- root cls
    Root a b dat <- rootIO cls
    let dat' = case depth dat of
         Nothing -> dat { depth = deep }
         Just de -> dat { depth = liftM (min de) deep } -- :)
    liftIO $ writeIOStableRef cls $ Root a b dat'

-- | Given an class, tell how far you must go down depenencies for the class to
--   have been changed, Nothing says no changes.
getDepth :: EqRepr s -> EqMonad s (Maybe Depth)
getDepth reps = do
    Root _ _ dat <- rootIO reps
    return $ depth dat

-- | The run function for EqMonad
runEqClass :: EqMonad e a -> IO a
runEqClass m = evalStateT (runLS m) $ IState { classes = [], number = 0 }




-- Properties and tests
type P = IOSet Int Bool

prop_makeclass :: Int -> P
prop_makeclass x = do
    c1 <- makeClass x
    c2 <- makeClass (x+1)
    b  <- equivalent c1 c2
    return $ not b

prop_makeclassexist :: Int -> P
prop_makeclassexist x = do
    c1 <- makeClass x
    classes <- getClasses
    return $ c1 `elem` classes

prop_union :: Int -> Int -> P
prop_union x y = do
    x <- makeClass x
    y <- makeClass y
    z  <- union x y
    b1 <- equivalent x z
    b2 <- equivalent y z
    return $ b1 && b2

prop_getElem :: Int -> Int -> Int -> P
prop_getElem x y z = do
    c1 <- makeClass x
    c2 <- makeClass y
    c3 <- makeClass z
    r  <- union c3 =<< union c1 c2
    el <- getElems r
    return  $ x `elem` el 
           && y `elem` el 
           && z `elem` el

prop_equivalent_reflex :: Int -> P 
prop_equivalent_reflex x = makeClass x >>= \z -> equivalent z z

prop_equivalent_trans :: Int -> Int -> Int -> P
prop_equivalent_trans x y z = do
    c1 <- makeClass x
    c2 <- makeClass y
    c3 <- makeClass z
    a1 <- union c1 c2
    a2 <- union c2 c3
    xz <- equivalent c1 c3
    return xz



runTest = do
    quickCheck prop_makeclass
    quickCheck prop_makeclassexist
    quickCheck prop_equivalent_reflex
    quickCheck prop_equivalent_trans
    quickCheck prop_getElem
    quickCheck prop_union

instance Testable b => Testable (IOSet a b) where
   property b = property $ runEqClass b 
