module WLP.Invariant (
    findInvariantStmt,
    findInvariant,
    findInvariantTimeout,
    removeLoops,
    removeLoopsTimeout,
) where

import GCL.GCLParser.GCLDatatype
import WLP.Simplify (simplifyExpr)
import Z3.Z3ModelChecker (verifyExpr)
import Z3.Monad (Z3, evalZ3With)
import Z3.Opts (opt)
import System.Timeout (timeout)
import Control.Monad (join)

findInvariantStmt :: Int -> Expr -> Stmt -> Stmt
findInvariantStmt 0 g _    = Assume $ OpNeg g
findInvariantStmt k g body = IfThenElse g (Seq body $ findInvariantStmt (k-1) g body) Skip

-- | Tries to find the invariant by doing fixed point iterations
findInvariant :: [(String, Type)] -> (Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr -> Z3 (Maybe Expr)
findInvariant _ _ 0 _ _ _ _ = return Nothing
findInvariant tenv wlp k g body q expr = do
    let newExpr = simplifyExpr $ wlp body (opAnd g expr `opOr` opAnd (OpNeg g) q)
    let check = simplifyExpr (expr `opImplication` newExpr)
    same <- verifyExpr tenv check
    if same then return $ Just newExpr else findInvariant tenv wlp (k-1) g body q newExpr

findInvariantTimeout :: [(String, Type)] -> (Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr -> Int -> IO (Maybe Expr)
findInvariantTimeout tenv wlp k g body q expr time = do
    let options = opt "timeout" time
    r <- timeout (time * 1000) $ do evalZ3With Nothing options $ findInvariant tenv wlp k g body q expr
    return $ join r

removeLoops :: [(String, Type)] -> (Int -> Stmt -> Expr -> Expr) -> Int -> Stmt -> Z3 (Stmt, Expr, Bool)
removeLoops tenv wlp k p = removeLoopsR tenv wlp k p (LitB True) True

removeLoopsR :: [(String, Type)] -> (Int -> Stmt -> Expr -> Expr) -> Int -> Stmt -> Expr -> Bool -> Z3 (Stmt, Expr, Bool)
removeLoopsR tenv wlp k (Seq (Assert as) (While g body)) q True = removeLoopInvariant tenv wlp k g body q as
removeLoopsR tenv wlp k (Seq (Assert as) a@(Seq (While g body) b)) q c = do
    (bs, be, bt) <- removeLoopsR tenv wlp k b q c
    (ast, ae, at) <- if bt then removeLoopInvariant tenv wlp k g body be as else removeLoopsR tenv wlp k a be bt
    return (Seq ast bs, ae, at)
removeLoopsR tenv wlp k (Seq a b) q c = do 
    (bs, be, bt) <- removeLoopsR tenv wlp k b q c
    (as, ae, at) <- removeLoopsR tenv wlp k a be bt
    return (Seq as bs, ae, at)
removeLoopsR tenv wlp k (Block _ s) q c = removeLoopsR tenv wlp k s q c
removeLoopsR tenv wlp k (While g body) q True = removeLoopInvariant tenv wlp k g body q (LitB True)
removeLoopsR _ wlp k w@(While {}) e False = return (w, wlp k w e, False)
removeLoopsR _ wlp k a e c = return (a, wlp k a e, c)

removeLoopInvariant :: [(String, Type)] -> (Int -> Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr -> Z3 (Stmt, Expr, Bool)
removeLoopInvariant tenv wlp k g body q asinv = do
    (newBody, _, complete) <- removeLoopsR tenv wlp k body (LitB True) True
    if complete then do
        invariant <- findInvariant tenv (wlp k) k g newBody q asinv
        case invariant of
            Just inv -> return (Seq (Assert inv) (Assume $ OpNeg g), inv, True)
            Nothing -> if asinv == LitB True
                then return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
                else do
                    invariant2 <- findInvariant tenv (wlp k) k g newBody q (LitB True)
                    case invariant2 of
                        Nothing -> return (Seq (Assert asinv) $ While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
                        Just inv2 -> return (Seq (Assert inv2) (Assume $ OpNeg g), inv2, True)
    else do
        return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)

removeLoopsTimeout :: [(String, Type)] -> (Int -> Stmt -> Expr -> Expr) -> Int -> Stmt -> Int -> IO (Stmt, Expr, Bool)
removeLoopsTimeout tenv wlp k p = removeLoopsRTimeout tenv wlp k p (LitB True) True

removeLoopsRTimeout :: [(String, Type)] -> (Int -> Stmt -> Expr -> Expr) -> Int -> Stmt -> Expr -> Bool -> Int -> IO (Stmt, Expr, Bool)
removeLoopsRTimeout tenv wlp k (Seq (Assert as) (While g body)) q True time = removeLoopInvariantTimeout tenv wlp k g body q as time
removeLoopsRTimeout tenv wlp k (Seq (Assert as) a@(Seq (While g body) b)) q c time = do
    (bs, be, bt) <- removeLoopsRTimeout tenv wlp k b q c time
    (ast, ae, at) <- if bt then removeLoopInvariantTimeout tenv wlp k g body be as time else removeLoopsRTimeout tenv wlp k a be bt time
    return (Seq ast bs, ae, at)
removeLoopsRTimeout tenv wlp k (Seq a b) q c time = do 
    (bs, be, bt) <- removeLoopsRTimeout tenv wlp k b q c time
    (as, ae, at) <- removeLoopsRTimeout tenv wlp k a be bt time
    return (Seq as bs, ae, at)
removeLoopsRTimeout tenv wlp k (Block _ s) q c time = removeLoopsRTimeout tenv wlp k s q c time
removeLoopsRTimeout tenv wlp k (While g body) q True time = removeLoopInvariantTimeout tenv wlp k g body q (LitB True) time
removeLoopsRTimeout _ wlp k w@(While {}) e False _ = return (w, wlp k w e, False)
removeLoopsRTimeout _ wlp k a e c _ = return (a, wlp k a e, c)

removeLoopInvariantTimeout :: [(String, Type)] -> (Int -> Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr -> Int -> IO (Stmt, Expr, Bool)
removeLoopInvariantTimeout tenv wlp k g body q asinv time = do
    (newBody, _, complete) <- removeLoopsRTimeout tenv wlp k body (LitB True) True time
    if complete then do
        invariant <- findInvariantTimeout tenv (wlp k) k g newBody q asinv time
        case invariant of
            Just inv -> return (Seq (Assert inv) (Assume $ OpNeg g), inv, True)
            Nothing -> if asinv == LitB True
                then return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
                else do
                    invariant2 <- findInvariantTimeout tenv (wlp k) k g newBody q (LitB True) time
                    case invariant2 of
                        Nothing -> return (Seq (Assert asinv) $ While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
                        Just inv2 -> return (Seq (Assert inv2) (Assume $ OpNeg g), inv2, True)
    else do
        return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
