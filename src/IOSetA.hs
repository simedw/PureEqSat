{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}

module IOSetA where

import Control.Monad
import "mtl" Control.Monad.State

import Data.IOStableRef
--import Data.IOStableRef
import Data.Maybe (listToMaybe)
import qualified Data.Set as S
import Data.Set (Set)
import Test.QuickCheck

newtype IOSet s a = IS { runLS :: StateT (IState s) IO a }
    deriving (MonadState (IState s), Monad, MonadIO)

data IState s = IState
    { classes :: [EqRepr s] -- Only pointer to Root elems!
    , number  :: CompareType
    }

type EqMonad = IOSet

type EqRepr s = IOStableRef (MinEqRepr s)

type Depth = Int
type Rank = Int
type CompareType = Int
data MinEqRepr s 
  = Root CompareType Rank (EqData s)
  | Node (EqRepr s)

data EqData s = EqData
    { eqSet  :: (Set s)
    , eqDependOnMe :: Set (EqRepr s)
    , eqIDependOn  :: Set (EqRepr s)
    , depth :: Maybe Depth
    }

unionFunction :: Ord s => EqData s -> EqData s -> EqData s
unionFunction x y = EqData
    { eqSet        = eqSet x `S.union` eqSet y
    , eqDependOnMe = eqDependOnMe x `S.union` eqDependOnMe y
    , eqIDependOn   = eqIDependOn x `S.union` eqIDependOn y
    , depth  = Just 0 
    }

makeData :: s -> EqData s
makeData s = EqData
    { eqSet = S.singleton s
    , eqDependOnMe = S.empty
    , eqIDependOn  = S.empty
    , depth        = Just 0
    }

root :: EqRepr s -> IOSet s (EqRepr s)
root rep = do
    v <- liftIO $ readIOStableRef rep
    case v of
        r@(Root _ _ _) -> return rep
        Node parent    -> do
            r <- root parent
            liftIO $ writeIOStableRef rep (Node r)
            return r

rootIO :: EqRepr s -> IOSet s (MinEqRepr s)
rootIO rep = do
    ioroot <- root rep
    liftIO $ readIOStableRef ioroot

makeClass :: eqElem -> IOSet eqElem (EqRepr eqElem)
makeClass elem = do
    nr <- gets number
    v <- liftIO $ newIOStableRef (Root nr 0 (makeData elem))
    modify $ \ s -> s { classes = v : classes s
                      , number= nr + 1
                      }
    return v

equivalent :: EqRepr e -> EqRepr e -> IOSet e Bool
equivalent x y = do
    (Root cx _ _) <- rootIO x
    (Root cy _ _) <- rootIO y
    return (cx == cy)


union :: Ord e => EqRepr e -> EqRepr e -> IOSet e (EqRepr e)
union iox ioy = do
    (Root xc xrank xdata) <- rootIO iox
    (Root yc yrank ydata) <- rootIO ioy
    --liftIO $ putStrLn $ "union #" ++ show xc ++ " #" ++ show yc ++ "(" ++ show xrank ++ "," ++ show yrank ++ ")"
    case (xrank > yrank, xrank < yrank, xc /= yc) of
        (True , _   , _   ) -> iox `setRootTo` ioy
        (False,True , _   ) -> ioy `setRootTo` iox
        (False,False, True) -> incRank =<< iox `setRootTo` ioy
        _                   -> return iox
  where
    -- make y the root of x
    setRootTo :: Ord e => EqRepr e -> EqRepr e -> IOSet e (EqRepr e)
    setRootTo x y = do
        x <- root x
        y <- root y
        (Root cx xrank xdata) <- rootIO x
        (Root cy yrank ydata) <- rootIO y
        liftIO $ writeIOStableRef y $ Root (min cx cy) yrank (ydata `unionFunction` xdata) 
        liftIO $ writeIOStableRef x $ Node y
        return y

    incRank :: EqRepr e -> IOSet e (EqRepr e)
    incRank x = do
        x <- root x
        Root c rank dat <- rootIO x
        liftIO $ writeIOStableRef x (Root c (rank + 1) dat)
        return x

addElem :: Ord e => e -> EqRepr e -> EqMonad e ()
addElem elem rep = do
    rep <- root rep
    Root c r dat <- rootIO rep
    liftIO $ writeIOStableRef rep (Root c r dat { eqSet = S.insert elem (eqSet dat) })

getElems :: EqRepr e -> EqMonad e [e]
getElems x = do
    Root _ _ dat <- rootIO x
    return $ S.toList (eqSet dat)

getClass :: Ord e => e -> EqMonad e (Maybe (EqRepr e))
getClass elem = do
    cls <- getClasses
    liftM (listToMaybe . concat) $ forM cls $ \c -> do
        Root _ _ dat <- rootIO c
        case elem `S.member` eqSet dat of
            True  -> return [c]
            False -> return []

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
   
   {-
getClasses = do
    cls <- gets classes
    ls <- flip filterM cls $ \c -> do
        eq <- liftIO $ readIOStableRef c
        case eq of
            Root _ _ _ -> return True
            _          -> return False
    modify $ \s -> s { classes = ls}
    return ls
-}


-- ps <| p
-- ska den har satta at bada hallen?
-- mm, funderar på om man ska ändra så att Root har speciell datatyp för all sin
-- data som den sparar. Så att man kan ha en withRoot :: (Data -> (Data,a)) -> EqRepr -> Opt a 
-- kanske blir skoj

getDependOnMe :: EqRepr e -> EqMonad e [EqRepr e]
getDependOnMe = liftM (\(Root _ _ dat) -> S.toList $ eqDependOnMe dat) . rootIO

dependOn :: EqRepr e -> [EqRepr e] -> EqMonad e ()
p `dependOn` ps = do
    p <- root p
    Root c r dat <- rootIO p
    liftIO $ writeIOStableRef p $ Root c r dat { eqIDependOn = eqIDependOn dat `S.union` S.fromList ps}
    forM_ ps $ \ dep -> do
        dep <- root dep
        Root cd rd dat <- rootIO dep
        liftIO $ writeIOStableRef dep $ Root cd rd dat { eqDependOnMe = S.insert p (eqDependOnMe dat) }


updated :: EqRepr e -> Maybe Depth -> EqMonad e ()
updated cls deep = do
    cls <- root cls
    Root a b dat <- rootIO cls
    -- om den i dat är Nothing ska vi sätta den högra annars sätta min såvida inte depth är nothing
    let dat' = case depth dat of
         Nothing -> dat { depth = deep }
         Just de -> dat { depth = liftM (min de) deep } -- :)
    liftIO $ writeIOStableRef cls $ Root a b dat'

getDepth :: EqRepr s -> EqMonad s (Maybe Depth)
getDepth reps = do
    Root _ _ dat <- rootIO reps
    return $ depth dat

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


{-
interface
    ( EqMonad
    , EqRepr
    , makeClass  -- :: EqElem                   -> m (EqRepr m)
    , equivalent -- :: EqRepr       -> EqRepr m -> m Bool
    , union      -- :: EqRepr       -> EqRepr m -> m (EqRepr m)
    , getElems   -- :: EqRepr                   -> m [EqElem m]
    , getClass   -- :: Eq (EqElem m) => EqElem m -> m (Maybe (EqRepr m))
    , getClasses -- :: m [EqRepr]
    , runEqClass -- :: m a -> a
-}
{-
-- fast det är inte samma s detta s är TExpr ,, medan i STRef så är det en phantom type
-- vi kan fortfarande ha den till Int och ha att mappen är till IOStableRef (Set s)

-- det viktigaste ar att EqRepr som lamnar IOSetA aldrig kan peka pa nagot an en direkt klass. annars blir det jobbig bookkeeping tror jag

-- mm vi vill ha en unionfind slags grej, dar har vi en pekare till en specific term. och med hjalp av den kan vi hitta klassrep termen
-- problemet är att vi inte har alla termer i klassen då, samt att vi kanske inte 
-- kan ha EqRepr utan en parameter

-- vi kanske kan overleva att EqRepr har en param
-- jo men vi bör nog tänka på det innan vi ändrar, dock kommer ListSet fortfarande fungera
-- I think iaf, så vi har kanske inte för mycket att förlora
-- isf för att få alla element i UF så kanske de kan sparas i motsvarigheten till Point (i den modulen)
-- vilket jag tror är vad vår EqRepr är..
-- vad menas med en point nu? med Point menar jag datatypen Point i UF.hs
-- Point Value Rank Parent, ranken används när man slår ihop union
-- for att fa log aktig complex ... hade glomt det.
jepp gillar att vi skriver i kommentarer för att det ska vara gilitig syntax :p
:)

fragan ar om den har typen av trad ar en bra modell att arbeta i i haskell.
exakt vad menar du med modell, interface eller faktum att vi gör union-find grejen?
well vårat interface är ganska imperativt redan och jag tycker inte den skriker c
algoritmen är fin så kan inte vara c :) 
det finns persistent varianter av uf som är pure och samma komplexitet

unionfind, den skriker ju c . Men du tror du kan fa ut alla element i en klass givet en pekare till en av termerna?

ja varje term innehåller alla sina barns termer. sa en dubble lankad lista typ..
hmm blir det det? om bara rotelement har barnen, eller det fungerar inte..

Vi har tre sorters EqRepr ::= Root | Element som pekar på rot | element som pekar på annat

kanske man kan se som tva?


tänkte att element som pekar på rot skulle haft möjlighet att ge rot elementet sina
barn medan de andra elementen inte haft den chansen. Så rot elementen måste förutom
Set av termer också ha under EqRepr som ännu inte gett barn som den får gå igenom.
Does that make sense? en optimering?

hmm ja kanske :) vi har två val

eller jag kanske blandar ihop properties, 
   y
 /   \
x     x'  vi kan nog ha invarianten att barn till y (x samt x') har lämnat sina termer
|
z

till y, men de behöver inte ha gjort pathreduction, alltså z har gett till x som
gett till y. Men z behöver inte peka på y (än) vilket gör det enklare i think.

vi kommer bara ta union av rot elemen (hittar rötter först) så om det bara är de
som har termerna så kommer det elementet som är rot att kunna ärva den andras termer
och den andra blir en vanlig medlem :p
type CompareType = Int -- unqiue ? japp  ... okej för varje makeClass

data EqRepr s= Root CompareType Rank (Set s) | Node (STRef (EqRepr s))
Int är för att jämföra == mellan klasser, rank får komma in någonstanns också

men om jag forstar din algorithm korrekt sa kommer alla barn till Rooten pusha upp sig sjalva  till rootens set? mm makeClass kommer skapa rot element, och enda sättet att slå ihop är via
union, och då, borde faktiskt fungera bra :) men da behover vi en gora nagot speciellt for noder som pekar pa root i skillnad mot noder som pekar pa allmana noder. 
Tror inte vi behöver det, vad tänker du på? rad 54
ahh nu har jag slagit ihop element som pekar på stuff till en, bra, lattare att fatta.
för alla element som pekar på något annat har redan lämnat sina termer så behöver
inte göra den skillnaden längre

"I don't remember you looking any better, but then again I don't remember you"
grymt bra låt :p Who says med John Mayer har inte hort

den är inte så bra, mer att jag tyckte det lät roligt för jag tror inte man ska ta det
som skämt :p

Egentligen har vi samma sak som innan med Left fast nu kan vi uppdatera det vardet och gora path reduction utanfor IOSetA.hs.

mm det är nog samma sak ja fast bättre ;) mest att jag trode det skulle bli mer annorlunda :p 
hehe

men i var state har vi en lista pa Root element.
ahh visst det glömde jag bort och tänka på men ja det borde fungera :)
maste bara tanka pa att bort saker som inte langre ar rotter.
mm vi kan någon slags collection där och sedan filtrerar man bort alla som inte är
rot och sparar innan man retunerar

om man kollar pa data typen for EqRepr som du gjorde innan, med den kan vi inte gora path reduction sa langt som direct till Rooten, maste alltid vara Node (Root)

hmm du vill ha något i stil med EqRepr = IOStableRef MinEqRepr, där Min är det jag definera på 81
tror du inte det hade varit battre?
Jo jag ser en poäng med det

Just nu kanns det som vi slagit ut de flesta bucklorna :P sa kanske dags att se om det fungerar :D
du menar i praktiken? ;)
iaf i en simulering
Jag tycker verkligen vi borde ha quickcheck egenskaper pa allt!


equivalent (Root c1 _ _) (Root c2 _ _) = return (c1 == c2)
equivalent (Node s     ) x             = getRoot.... precis

 function Union(x, y)
     xRoot := Find(x)
     yRoot := Find(y)
     if xRoot.rank > yRoot.rank  
         yRoot.parent := xRoot// lägg till de EqRepr som pekar till y till x, lägg till barn av y till x
                              , lägg inte till y som pekare till x
     else if xRoot.rank < yRoot.rank
         xRoot.parent := yRoot
     else if xRoot != yRoot // Unless x and y are already in same set, merge them
         yRoot.parent := xRoot
         xRoot.rank := xRoot.rank + 1



union x y
    x' <- root x
    y' <- root y
    child = S.union (child x') (child y')
    uf stuff ..
    setChild x' Nothing


-}


