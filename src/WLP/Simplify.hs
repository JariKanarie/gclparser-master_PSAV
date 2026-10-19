module WLP.Simplify where
import GCL.GCLParser.GCLDatatype
import Data.Bifunctor (first, second)
import Data.List (partition)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

simplifyExpr :: Expr -> Expr
simplifyExpr expr = case expr of
    (ArrayElem a b) -> ArrayElem (simplifyExpr a) (simplifyExpr b)

    OpNeg (LitB b) -> simplifyExpr $ LitB (not b)
    OpNeg (OpNeg b) -> simplifyExpr b
    OpNeg (BinopExpr LessThan a b) -> simplifyExpr $ BinopExpr GreaterThanEqual a b
    OpNeg (BinopExpr GreaterThan a b) -> simplifyExpr $ BinopExpr LessThanEqual a b
    OpNeg (BinopExpr LessThanEqual a b) -> simplifyExpr $ BinopExpr GreaterThan a b
    OpNeg (BinopExpr GreaterThanEqual a b) -> simplifyExpr $ BinopExpr LessThan a b
    OpNeg (BinopExpr And a b) -> simplifyExpr $ BinopExpr Or (OpNeg a) (OpNeg b)
    OpNeg (BinopExpr Or a b) -> simplifyExpr $ BinopExpr And (OpNeg a) (OpNeg b)
    OpNeg b -> OpNeg $ simplifyExpr b

    BinopExpr op a b -> simplifyBinopExpr op a b

    Forall name e -> Forall name $ simplifyExpr e
    Exists name e -> Exists name $ simplifyExpr e
    a -> a

simplifyBinopExpr :: BinOp -> Expr -> Expr -> Expr
simplifyBinopExpr op a b
    | op == And = retree op (LitB True) . collapseOn (LitB False) . filter (/= LitB True) . map simplifyExpr $ combineSame op a b
    | op == Or = retree op (LitB False) . collapseOn (LitB True) . filter (/= LitB False) . combineRangesOr . map simplifyExpr $ combineSame op a b
    | op == Plus = retree op (LitI 0) . sumLitI . map simplifyExpr $ combineSame op a b
    | op == Minus = retreeMin . sumNegLitI . map (second simplifyExpr) $ combineWithDir op a b
    | op `elem` comparisons = simplifyComparison op a b
    | op == Implication = simplifyExpr $ BinopExpr Or (OpNeg simpleA) simpleB
    | otherwise = BinopExpr op simpleA simpleB
    where
        simpleA = simplifyExpr a
        simpleB = simplifyExpr b

comparisons :: [BinOp]
comparisons = [GreaterThan, GreaterThanEqual, LessThan, LessThanEqual, Equal]

-- always puts the variable on the left if possible
simplifyComparison :: BinOp -> Expr -> Expr -> Expr
simplifyComparison comp a b | simplifyExpr a == simplifyExpr b = LitB $ comp `elem` [GreaterThanEqual, LessThanEqual, Equal]
simplifyComparison comp (LitI a) (LitI b) = case comp of
    Equal -> LitB $ a == b
    GreaterThan -> LitB $ a > b
    GreaterThanEqual -> LitB $ a >= b
    LessThan -> LitB $ a < b
    LessThanEqual -> LitB $ a <= b
    _ -> error "invalid comparison"
simplifyComparison comp (BinopExpr Plus (Var x) e) f = BinopExpr comp (Var x) . simplifyExpr $ BinopExpr Minus (simplifyExpr f) (simplifyExpr e)
simplifyComparison comp (BinopExpr Plus e (Var x)) f = BinopExpr comp (Var x) . simplifyExpr $ BinopExpr Minus (simplifyExpr f) (simplifyExpr e)
simplifyComparison comp (BinopExpr Minus (Var x) e) f = BinopExpr comp (Var x) . simplifyExpr $ BinopExpr Plus (simplifyExpr f) (simplifyExpr e)
simplifyComparison comp (BinopExpr Minus e (Var x)) f = BinopExpr (flipComp comp) (Var x) . simplifyExpr $ BinopExpr Minus (simplifyExpr e) (simplifyExpr f)
simplifyComparison comp f (BinopExpr Plus (Var x) e) = BinopExpr comp (Var x) . simplifyExpr $ BinopExpr Minus (simplifyExpr f) (simplifyExpr e)
simplifyComparison comp f (BinopExpr Plus e (Var x)) = BinopExpr comp (Var x) . simplifyExpr $ BinopExpr Minus (simplifyExpr f) (simplifyExpr e)
simplifyComparison comp f (BinopExpr Minus (Var x) e) = BinopExpr comp (Var x) . simplifyExpr $ BinopExpr Plus (simplifyExpr f) (simplifyExpr e)
simplifyComparison comp f (BinopExpr Minus e (Var x)) = BinopExpr (flipComp comp) (Var x) . simplifyExpr $ BinopExpr Minus (simplifyExpr e) (simplifyExpr f)
simplifyComparison comp a (Var x) = BinopExpr (flipComp comp) (Var x) (simplifyExpr a)
simplifyComparison comp a b = BinopExpr comp (simplifyExpr a) (simplifyExpr b)

flipComp :: BinOp -> BinOp
flipComp GreaterThan = LessThan
flipComp GreaterThanEqual = LessThanEqual
flipComp LessThan = GreaterThan
flipComp LessThanEqual = GreaterThanEqual
flipComp comp = comp

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
retree _  _ [x]    = x
retree op i (x:xs) = BinopExpr op x $ retree op i xs

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

combineRanges :: ([Expr] -> [Expr]) -> [Expr] -> [Expr]
combineRanges f list = f ranges ++ rest
    where
        (ranges, rest) = partition isComp list
        isComp (BinopExpr op (Var _) (LitI _)) = op `elem` comparisons
        isComp _ = False

combineRangesAnd :: [Expr] -> [Expr]
combineRangesAnd = combineRanges $ combineRangesAndR Map.empty

-- uses de morgans rule to use the simpler 'And' case
combineRangesOr :: [Expr] -> [Expr]
combineRangesOr = combineRanges (return . simplifyExpr . OpNeg . retree And (LitB True) . combineRangesAndR Map.empty) . map (simplifyExpr . OpNeg)

data RangeEnd = NegInf | Nb Int | Inf
    deriving (Eq, Ord, Show)
type Range = (RangeEnd, RangeEnd)

combineRangesAndR :: Map.Map String [Range] -> [Expr] -> [Expr]
combineRangesAndR m [] = concatMap (\(x, ranges) -> rangeToExprAnd x $ intersectRanges ranges) $ Map.toList m
combineRangesAndR m ((BinopExpr op (Var x) (LitI i)):xs) = combineRangesAndR (Map.alter (\v -> Just $ compAndIntToRange op i:fromMaybe [] v) x m) xs
combineRangesAndR _ _ = error "invalid range"

compAndIntToRange :: BinOp -> Int -> Range
compAndIntToRange GreaterThanEqual i = (Nb i, Inf)
compAndIntToRange GreaterThan i = (Nb (i + 1), Inf)
compAndIntToRange LessThanEqual i = (NegInf, Nb i)
compAndIntToRange LessThan i = (NegInf, Nb (i - 1))
compAndIntToRange Equal i = (Nb i, Nb i)
compAndIntToRange op _ = error $ "invalid comparison" ++ show op

rangeToExprAnd :: String -> Range -> [Expr]
rangeToExprAnd _ (NegInf, Inf) = []
rangeToExprAnd x (NegInf, Nb i) = [BinopExpr LessThanEqual (Var x) (LitI i)]
rangeToExprAnd x (Nb i, Inf) = [BinopExpr GreaterThanEqual (Var x) (LitI i)]
rangeToExprAnd x (Nb i, Nb j)
    | i == j = [BinopExpr Equal (Var x) (LitI i)]
    | i < j = [BinopExpr GreaterThanEqual (Var x) (LitI i), BinopExpr LessThanEqual (Var x) (LitI j)]
rangeToExprAnd _ _ = [LitB False]

intersectRanges :: [Range] -> Range
intersectRanges = foldr f (NegInf, Inf)
    where
        f :: Range -> Range -> Range
        f (a, b) (c, d) = (max a c, min b d)
