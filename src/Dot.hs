module Dot 
    ( toGraphviz
    )where

import Control.Monad
import Data.Function
import Data.List


import Data.GraphViz

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree

import Opt hiding (EqRepr)
import Expr

getDeps :: EqExpr -> [EqRepr]
getDeps e = case unEqExpr e of
    Atom _ -> []
    Bin _ a b -> [a,b]
    Tri _ a b c -> [a,b,c]

toGraphviz :: Opt String
toGraphviz = do
    classes <- getClasses
    (nodes, edges) <- liftM unzip . forM classes $ \cls -> do
        node <- getPtr cls
        deps <- getDependOnMe cls
        elems <- getElems cls
        edges' <- liftM nub . forM elems $ \elem -> do
            deps <- mapM getPtr $ getDeps elem
            return [(node, dep, ()) | dep <- deps]
        return ((node,length deps), nub $ concat edges')
    let nodes' = [ (node, ()) | (node , _) <- sortBy (compare `on` snd) nodes]
        edges' = concat edges
        g :: Gr () ()
        g = mkGraph nodes' edges'
        def :: GraphvizParams nl el Int nl
        def = defaultParams
    return $ printDotGraph 
           $ graphToDot def g 
