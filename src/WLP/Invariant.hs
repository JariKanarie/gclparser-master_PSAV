module WLP.Invariant (
    findInvariantStmt,
    findInvariant,
) where

import GCL.GCLParser.GCLDatatype
import WLP.Simplify (simplifyExpr)
import WLP.Z3ModelChecker (verifyExpr)
import Z3.Monad (Z3)

findInvariantStmt :: Int -> Expr -> Stmt -> Stmt
findInvariantStmt 0 g _    = Assume $ OpNeg g
findInvariantStmt k g body = IfThenElse g (Seq body $ findInvariantStmt (k-1) g body) Skip

-- | Tries to find the invariant by doing fixed point iterations
findInvariant :: (Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr -> Z3 (Maybe Expr)
findInvariant _ 0 _ _ _ _ = return Nothing
findInvariant wlp k g body q expr = do
    let newExpr = simplifyExpr $ wlp body (opAnd g expr `opOr` opAnd (OpNeg g) q)
    let check = simplifyExpr (newExpr `opImplication` expr)
    if check == LitB True then return $ Just newExpr else do
        same <- verifyExpr check
        if same then return $ Just newExpr else findInvariant wlp (k-1) g body q newExpr
