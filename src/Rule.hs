{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PackageImports #-}
module Rule where

import Expr

import Opt hiding (EqRepr)
import Debug.Trace
import Data.Maybe
import Data.List (groupBy,sort, sortBy)
import Control.Monad
import "mtl" Control.Monad.Trans
import Data.List (zipWith4)
import Data.Either
import Data.Function
import qualified Data.Set as S
import Data.Set (Set)

import qualified Data.Map as M
import Data.Map(Map)

type ID = Int

data Pattern = PExpr (TExpr Pattern)
             | PAny ID
             | PLit Atom Pattern
             | PFun (Atom -> Atom -> Atom) Pattern Pattern

instance Show Pattern where
  show p = case p of
    PExpr t -> "ex: " ++ show t
    PAny i  -> "any " ++ show i

type Constraint = (ID, Either Atom EqRepr)
data Rule = Rule Pattern Pattern


(~>) = Rule
infix 0 ~>
forall3 f = f (PAny 1) (PAny 2) (PAny 3)
forall2 f = f (PAny 1) (PAny 2)
forall1 f = f (PAny 1)

rAnd x y  = PExpr (Bin And x y)
rOr x y   = PExpr (Bin Or x y)
rAdd x y  = PExpr (Bin Add x y)
rMul x y  = PExpr (Bin Mul x y)
rInt x    = PExpr (Atom $ LInteger x)
rBool x   = PExpr (Atom $ LBool x)
rTrue     = rBool True
rFalse    = rBool False
rVar x    = PExpr (Atom $ Var x)
rEq x y   = PExpr (Bin Eq x y)
rIf x y z = PExpr (Tri If x y z)
pInt x    = PLit (LInteger (error "don't peek here")) x
pBool x   = PLit (LBool (error "don't peek here")) x

plus = PFun $ \(LInteger i) (LInteger j) ->  (LInteger $ i + j)
mul  = PFun $ \(LInteger i) (LInteger j) ->  (LInteger $ i * j)
eqI  = PFun $ \(LInteger i) (LInteger j) ->  (LBool $ i == j)
eqB  = PFun $ \(LBool x)    (LBool y)    ->  (LBool $ x == y)

rules :: [(Int,Rule)]
rules = map (\r -> (getRuleDepth r, r)) $
        [ identity rAdd  (rInt 0)
        , identity rMul  (rInt 1)
        , identity rAnd  (rTrue)
        , identity rOr   (rFalse)
        , assoc rAdd
        , assoc rMul
        , assoc rAnd
        , assoc rOr
        , commute rAdd
        , commute rMul
        , commute rAnd
        , commute rOr
        , commute rEq
        , zero rMul (rInt 0)
        , zero rAnd (rFalse)
        , zero rOr  (rTrue)

        , eval (rAdd `on` pInt)  plus pInt
        , eval (rMul `on` pInt)  mul pInt
        , eval (rEq  `on` pInt)  eqI pBool
        , eval (rEq  `on` pBool) eqB pBool

        , distr  rMul rAdd
        , distr' rMul rAdd
        , distr  rAnd rOr
        , distr' rAnd rOr
        , distr  rOr  rAnd
        , distr' rOr  rAnd
        , forall1 $ \x -> x `rEq` x ~> rTrue
        , forall3 $ \x y z -> ((x `rAdd` z) `rEq` (y `rAdd` z)) ~> (x `rEq` y)
        , forall2 $ \x y -> rIf (rTrue) x y ~> x
        , forall2 $ \x y -> rIf (rFalse) x y ~> y
        , forall2 $ \x y -> rIf y x x ~> x
        ] 

distr op1 op2 = forall3 $ \x y z -> x `op1` (y `op2` z) ~> (x `op1` y) `op2` (x `op1` z)
distr' op1 op2 = forall3 $ \x y z -> (x `op1` y) `op2` (x `op1` z) ~> x `op1` (y `op2` z) 
zero op v     = forall1 $ \x -> (x `op` v) ~> v
identity op v = forall1 $ \x -> (x `op` v) ~> x        
commute op    = forall2 $ \x y -> (x `op` y) ~> (y `op` x)
assoc op      = forall3 $ \x y z -> ((x `op` y) `op` z) ~> (x `op` (y `op` z))
eval op sop res = forall2 $ \x y -> (x `op` y) ~> res (x `sop` y)

getRuleDepth :: Rule -> Int
getRuleDepth (Rule r _) = getPDepth r
  where
        getPDepth :: Pattern -> Int
        getPDepth r = case r of
            PExpr (Atom _) -> 0
            PExpr (Bin _ p q)   -> 1 + max (getPDepth p) (getPDepth q)
            PExpr (Tri _ p q z) -> 1 + maximum (map getPDepth [p, q, z])
            PAny _          -> 0
            PLit _ _        -> 0


eqRec :: [EqRepr] -> Opt Bool
eqRec [] = return True
eqRec (x:[])   = return True
eqRec (x:y:xs) = liftM2 (&&) (equivalent x y) (eqRec (y:xs))

-- Returns True if it has changed the class
buildPattern :: Maybe EqRepr -> Pattern -> [Constraint] -> Opt (Bool, EqRepr)
buildPattern cls p ma = case p of
    PExpr (Atom i) -> addTermToClass (EqExpr $ Atom i) cls
    PExpr (Bin bin q1 q2) -> do -- addBinTermToClass Add q1 q2
        p1 <- rec q1
        p2 <- rec q2
        c <- addTermToClass  (EqExpr $ Bin bin p1 p2) cls
        snd c `dependOn` [p1,p2]
        return c
    PExpr (Tri tri q1 q2 q3) -> do
        p1 <- rec q1
        p2 <- rec q2
        p3 <- rec q3
        c <- addTermToClass (EqExpr $ Tri tri p1 p2 p3) cls
        snd c `dependOn` [p1,p2,p3]
        return c
    PAny i     -> do
        let Right c = fromJust $ lookup i $ ma
        maybe (return (False, c)) (myUnion (False, c)) cls
    PLit _ v -> do
        r <- literal v
        c <- addTermToClass (EqExpr $ Atom r) cls
        return c
        
  where
    rec q = snd `fmap` buildPattern Nothing q ma
    literal :: Pattern -> Opt Atom
    literal p = case p of
       PFun f p1 p2 -> do
         q1 <- literal p1
         q2 <- literal p2
         return $ f q1 q2
       PLit _ v -> literal v
       PAny i -> do  
         let Left c = fromJust $ lookup i ma
         return c 

{-
combineConst2 :: [[a]] -> [[a]] -> Maybe [[a]]
combineConst2 [] _  = Nothing
combineConst2 _ []  = Nothing
combineConst2 xs ys = Just [x ++ y | x <- xs, y <- ys]

combineConst3 :: [[a]] -> [[a]] -> [[a]] -> Maybe [[a]]
combineConst3 [] _  _   = Nothing
combineConst3 _  [] _   = Nothing
combineConst3 _  _  []  = Nothing
combineConst3 xs ys zs = Just [x ++ y ++ z | x <- xs, y <- ys, z <- zs]

applyPattern :: Pattern -> EqRepr -> Opt [[Constraint]] -- [[Either (ID, Lit) (ID,EqRepr)]]
applyPattern pattern cls = do 
    elems <- getElems cls
    case pattern of
        PExpr (Atom i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Atom l) | i == l -> return  $ Just []
            _              -> return Nothing
        PExpr (Bin bin q1 q2) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Bin bin' p1 p2) | bin == bin' -> do
                b <- equivalent p1 cls
                b' <- equivalent p2 cls
                if b || b'
                     then return Nothing
                     else do
                       r1 <- applyPattern q1 p1 
                       r2 <- applyPattern q2 p2
                       return $ combineConst2 r1 r2    
            _ -> return Nothing
        PExpr (Tri tri q1 q2 q3) -> liftM (concat . catMaybes) $ forM elems $ \rep -> case rep of
            EqExpr (Tri tri' p1 p2 p3) | tri == tri' -> do
                r1 <- applyPattern q1 p1 
                r2 <- applyPattern q2 p2
                r3 <- applyPattern q3 p3
                return $ combineConst3 r1 r2 r3
            _ -> return Nothing
        PAny i -> return [[(i,Right cls)]]
        PLit (LInteger _) (PAny i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Atom l@(LInteger _)) -> return  $  Just [(i, Left l)]
            _              -> return Nothing
        PLit (LBool _) (PAny i) -> liftM catMaybes $ forM elems $ \rep -> case rep of
            EqExpr (Atom l@(LBool _)) -> return  $  Just [(i, Left l)]
            _              -> return Nothing

-- returns True when it matched
apply :: Rule -> EqRepr -> Opt Bool
apply (Rule p1 p2) cls = do
    ma <- applyPattern p1 cls 
    -- ma :: [ [ Either (Id, Lit) (id, eqrepr) ]] nagonting med nubclassesRight
    ma <- filterM (\l -> do 
        let same :: [ [EqRepr] ]
            same = map (map  snd) 
                     $ groupBy (\x y -> fst x == fst y) 
                     $ sortBy (\x y -> compare (fst x) (fst y)) 
                     $ [ (x, y) | (x, Right y) <- l ]

        liftM and $ mapM eqRec same
        ) ma
    list <- mapM (buildPattern (Just cls) p2) ma

    -- we should return True something has changed
    return $ any fst list
  where
    fun [] _ = return []
    fun (x:xs) set = do
        x' <- mapM translateConstraint (sortBy (compare `on` fst) x)
        if S.member x' set
            then fun xs set
            else liftM (x:) (fun xs (S.insert x' set))

translateConstraint :: Constraint -> Opt (ID, Either Atom Int)
translateConstraint (id, e) = liftM ((,) id) $ case e of
    Left v -> return $ Left v
    Right cls -> do
        cls' <- getPtr cls
        return $  Right  cls'
-- Return True if any rule applied
applyRules :: [(Int, Rule)] -> EqRepr -> Opt Bool
applyRules rules reps = do
    dirty <- getDepth reps
    case dirty of
       Nothing -> return False
       Just d  -> do 
        bs <- mapM (apply' d) rules
        if all not bs
            then do
                updated reps Nothing
                return False
            else return True

  where
    apply' d (depth, rule)
              | d <= depth = apply rule reps
              | otherwise = return False
-}

type Done  = (Int, EqRepr, [Constraint])
type Check = (Pattern, [(EqRepr, Pattern)], (Int, EqRepr), [Constraint])

type Dones = [Done]
type Checks = [Check]

type ToCheck = [(EqRepr, Checks)]

insertDone :: Done -> Dones -> Opt Dones
insertDone done dones = return (done : dones)

mergeDones :: Dones -> Dones -> Opt Dones
mergeDones d1 d2 = return (d1 ++ d2)

mergeChecks :: ToCheck -> ToCheck -> Opt ToCheck
mergeChecks t1 t2 = return (t1 ++ t2)

getToCheck :: ToCheck -> Opt (Maybe (EqRepr, Checks, ToCheck))
getToCheck [] = return Nothing
getToCheck ((e,c):tc) = return $ Just (e,c,tc)

apply :: EqRepr -> ID -> [Constraint] -> Opt (Maybe [Constraint])
apply cls id [] = return . Just $ [ (id, Right cls) ]
apply cls id con@(id'@(cid,cls') : con') 
    | id < cid = return . Just $ (id, Right cls) : con
    | id == cid = do
        b <- case cls' of
            Left _ -> return False
            Right cls' -> equivalent cls cls'
        if b then return $ Just con else return Nothing
    | otherwise = do
        m <- apply cls id con'
        return $ (id':) `fmap` m

getDone :: EqRepr -> Checks -> Opt (Dones, ToCheck, Checks)
getDone cls chks = foldM step ([], [], []) chks
  where
    step :: (Dones, ToCheck, Checks) -> Check -> Opt (Dones, ToCheck, Checks)
    step (done, tc, chs) (PAny id, m, (rule, req), constraints) = do
        mcon <- apply cls id constraints
        case mcon of
            Nothing -> return (done, tc, chs)
            Just con -> case m of
                [] -> do
                    don <- insertDone (rule, req, con) done
                    return (don, tc, chs)
                (e,p):es -> return (done, (e,[(p, es, (rule,req), con)]) : tc, chs)
    step (done, tc, chs) chk = return (done, tc, chk: chs)

isEmpty :: Checks -> Bool
isEmpty = null

empty :: Opt Checks
empty = return []

emptyTC :: ToCheck
emptyTC = []

applyRules :: [(Int, Rule)] -> [EqRepr] -> Opt ()
applyRules rules classes = do
    let rules' = [ (nr, depth, pat) 
                 | (nr, (depth, Rule pat _)) <- zip [0..] rules] 
    tc <- forM classes $ \cls -> do
        depth <- getDepth cls
        case depth of
            Nothing -> return (cls, [(p, [], (nr, cls), []) 
                                    | (nr, _, p) <- rules'])
            Just d  -> return (cls, [(p, [], (nr, cls), []) 
                                    | (nr, d', p) <- rules'
                                    , d <= d'])
    liftIO $ print $ length tc
    done <- loop tc []
    liftIO $ print $ length done
    mapM_ (\(rule, cls, con) -> buildPattern (Just cls) (getRule rule) con) done 
  where
    
    ruleMap :: Map Int Pattern
    ruleMap = M.fromList [ (id, rule) | (id, (_, Rule _ rule)) <- zip [0..] rules]

    getRule :: Int -> Pattern
    getRule i = ruleMap M.! i    

    loop :: ToCheck -> Dones -> Opt Dones
    loop tc done = do
        ma <- getToCheck tc
        case ma of
            Nothing -> return done
            Just (e,checks, eq) -> do
                (done', eq') <- step e checks
                d <- mergeDones done done'
                e <- mergeChecks eq  eq'
                loop e d

    step :: EqRepr -> Checks -> Opt (Dones, ToCheck) 
    step cls chks = do
        (done, toc, undone) <- getDone cls chks
        case isEmpty undone of
            True -> return $ (,) done toc
            False -> do
                elems <- getElems cls
                (ds, tc) <- liftM (unzip . concat) . forM elems $ \term -> do
                    case unEqExpr term of
                        Atom atom        -> checkAtom atom undone
                        Bin bin e1 e2    -> checkBin bin e1 e2 undone
                        Tri tri e1 e2 e3 -> checkTri tri e1 e2 e3 undone
                (,) `fmap` foldM mergeDones done ds `ap` foldM mergeChecks toc tc

    checkAtom :: Atom -> Checks -> Opt [(Dones, ToCheck)]
    checkAtom atom chs = liftM concat . forM chs $ \check -> do
        case check of
            (PExpr (Atom atom'), m, rule@(rid, req), const) | atom == atom' -> do
                case m of
                    [] -> return [([(rid, req, const)] , [])]
                    ((e,p):ps) -> return [([], [(e, [(p, ps, rule, const)])])]
            _ -> return []

    checkBin :: BinOp -> EqRepr -> EqRepr -> Checks -> Opt [(Dones, ToCheck)]
    checkBin bin e1 e2 chs = liftM concat . forM chs $ \check -> do
        e1 <- root e1
        e2 <- root e2
        case check of
            (PExpr (Bin bin' p1 p2), m, rule, const) | bin == bin' -> do
                return [ ([], [ (e1, [ (p1, (e2,p2):m, rule, const) ]) ]) ]
            _ -> return []

    checkTri :: TriOp -> EqRepr -> EqRepr -> EqRepr -> Checks -> Opt [(Dones, ToCheck)]
    checkTri tri e1 e2 e3 chs = liftM concat . forM chs $ \check -> do
        e1 <- root e1
        e2 <- root e2
        e3 <- root e3
        case check of
            (PExpr (Tri tri' p1 p2 p3), m, rule, const) | tri == tri' -> do
                return [ ([], [ (e1, [ (p1, (e2,p2):(e3,p3):m, rule, const) ]) ]) ]
            _ -> return []
            

ruleEngine :: Int -> [(Int, Rule)] -> Opt ()
ruleEngine 0 rules = return ()
ruleEngine n rules = do
    classes <- getClasses
    applyRules rules classes
    ruleEngine (n-1) rules

{-
-- applys a set of rules on all classes
ruleEngine :: Int -> [(Int,Rule)] -> Opt ()
ruleEngine n rules | n < 0     = return ()
                   | otherwise = do
  classes <- getClasses
  res <- mapM (applyRules rules) classes
  when (any id res) $ ruleEngine (n-1) rules
-}
