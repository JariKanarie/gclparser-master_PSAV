module WLP.Invariant (
    findInvariantStmt,
    findInvariant,
    removeLoops,
) where

import GCL.GCLParser.GCLDatatype
import WLP.Simplify (simplifyExpr)
import Z3.Z3ModelChecker (verifyExpr)
import Z3.Monad (Z3)

findInvariantStmt :: Int -> Expr -> Stmt -> Stmt
findInvariantStmt 0 g _    = Assume $ OpNeg g
findInvariantStmt k g body = IfThenElse g (Seq body $ findInvariantStmt (k-1) g body) Skip

-- | Tries to find the invariant by doing fixed point iterations
findInvariant :: [(String, Type)] -> (Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr -> Z3 (Maybe Expr)
findInvariant _ _ 0 _ _ _ _ = return Nothing
findInvariant tenv wlp k g body q expr = do
    let newExpr = simplifyExpr $ wlp body (opAnd g expr `opOr` opAnd (OpNeg g) q)
    let check = simplifyExpr (expr `opImplication` newExpr)
    if check == LitB True then return $ Just newExpr else do
        same <- verifyExpr tenv check
        if same then return $ Just newExpr else findInvariant tenv wlp (k-1) g body q newExpr

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
            Nothing -> return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
            Just inv -> if asinv == LitB True 
                then return (Seq (Assert inv) (Assume $ OpNeg g), inv, True)
                else do
                    invariant2 <- findInvariant tenv (wlp k) k g newBody q (LitB True)
                    case invariant2 of
                        Nothing -> return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)
                        Just inv2 -> return (Seq (Assert inv2) (Assume $ OpNeg g), inv2, True)
    else do
        return (While g newBody, wlp k (findInvariantStmt k g newBody) q, False)

