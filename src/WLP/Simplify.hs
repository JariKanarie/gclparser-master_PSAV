module WLP.Simplify where
import GCL.GCLParser.GCLDatatype
import Data.Bifunctor (first)
import Data.List (partition)

simplifyExpr :: Expr -> Expr
simplifyExpr expr = case expr of
    (ArrayElem a b) -> ArrayElem (simplifyExpr a) (simplifyExpr b)

    OpNeg (LitB b) -> simplifyExpr $ LitB (not b)
    OpNeg (OpNeg b) -> simplifyExpr b
    OpNeg (BinopExpr LessThan a b) -> simplifyExpr $ BinopExpr GreaterThanEqual a b
    OpNeg (BinopExpr GreaterThan a b) -> simplifyExpr $ BinopExpr LessThanEqual a b
    OpNeg (BinopExpr LessThanEqual a b) -> simplifyExpr $ BinopExpr GreaterThan a b
    OpNeg (BinopExpr GreaterThanEqual a b) -> simplifyExpr $ BinopExpr LessThan a b
    OpNeg b -> simplifyExpr b

    BinopExpr op a b -> simplifyBinopExpr op a b

    a -> a

simplifyBinopExpr :: BinOp -> Expr -> Expr -> Expr
simplifyBinopExpr op a b
    | op == And = retree op (LitB True) . collapseOn (LitB False) . filter (/= LitB True) $ combineSame op a b
    | op == Or = retree op (LitB False) . collapseOn (LitB True) . filter (/= LitB False) $ combineSame op a b
    | op == Plus = retree op (LitI 0) . sumLitI $ combineSame op a b
    | op == Minus = retreeMin . sumNegLitI $ combineWithDir op a b
    | otherwise = BinopExpr op simpleA simpleB
    where
        simpleA = simplifyExpr a
        simpleB = simplifyExpr b
        -- symmetric and associative
        combinable = [Plus, Multiply, And, Or, Equal]

combineSame :: BinOp -> Expr -> Expr -> [Expr]
combineSame op aexpr bexpr = expand aexpr ++ expand bexpr
    where
        expand expr@(BinopExpr aop c d) = if op == aop then combineSame op c d else [expr]
        expand expr = [expr]

combineWithDir :: BinOp -> Expr -> Expr -> [(Bool, Expr)]
combineWithDir op aexpr bexpr = expand False aexpr ++ expand True bexpr
    where
        expand dir expr@(BinopExpr aop c d) = if op == aop then map (first (/= dir)) $ combineWithDir op c d else [(dir, expr)]
        expand dir expr = [(dir, expr)]

retree :: BinOp -> Expr -> [Expr] -> Expr
retree _  i []     = i
retree _  _ [x]    = simplifyExpr x
retree op i (x:xs) = BinopExpr op (simplifyExpr x) $ retree op i xs

retreeMin :: [(Bool, Expr)] -> Expr
retreeMin l
    | null l = i
    | null plus = BinopExpr Minus (LitI 0) negsum
    | null neg = plussum
    | otherwise = BinopExpr Minus plussum negsum
    where
        i = LitI 0
        (neg, plus) = partition fst l
        plussum = retree Plus i $ map snd plus
        negsum = retree Plus i $ map snd neg

collapseOn :: Expr -> [Expr] -> [Expr]
collapseOn evil exprs = if evil `elem` exprs then [evil] else exprs

sumLitI :: [Expr] -> [Expr]
sumLitI exprs = (\(s, o) -> LitI s : o) $ foldr f (0, []) exprs
    where
        f :: Expr -> (Int, [Expr]) -> (Int, [Expr])
        f (LitI i) (s, r) = (s + i, r)
        f other (s, r) = (s, other:r)

sumNegLitI :: [(Bool, Expr)] -> [(Bool, Expr)]
sumNegLitI exprs = (\(s, o) -> (False, LitI s) : o) $ foldr f (0, []) exprs
    where
        f :: (Bool, Expr) -> (Int, [(Bool, Expr)]) -> (Int, [(Bool, Expr)])
        f (right, LitI i) (s, r) = (if right then s - i else s + i, r)
        f other (s, r) = (s, other:r)