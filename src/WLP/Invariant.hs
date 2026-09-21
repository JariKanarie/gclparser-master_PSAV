module WLP.Invariant (
    findInvariantStmt,
    findInvariantWlp,
) where

import GCL.GCLParser.GCLDatatype

findInvariantStmt :: Int -> Expr -> Stmt -> Stmt
findInvariantStmt 0 g _    = Assume $ OpNeg g
findInvariantStmt k g body = IfThenElse g (Seq body $ findInvariantStmt (k-1) g body) Skip

findInvariantWlp :: (Stmt -> Expr -> Expr) -> Int -> Expr -> Stmt -> Expr -> Expr
findInvariantWlp wlp 0 g _    q = wlp (Assume $ OpNeg g) q
findInvariantWlp wlp k g body q = opAnd g prev `opOr` opAnd (OpNeg g) q
    where
        prev = findInvariantWlp wlp (k-1) g body q
