module WLP.Simplify where
import GCL.GCLParser.GCLDatatype

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

    BinopExpr And (LitB True) b -> simplifyExpr b
    BinopExpr And b (LitB True) -> simplifyExpr b
    BinopExpr And (LitB False) _ -> LitB False
    BinopExpr And _ (LitB False) -> LitB False
    BinopExpr Or (LitB True) _ -> LitB True
    BinopExpr Or _ (LitB True) -> LitB True
    BinopExpr Or (LitB False) b -> simplifyExpr b
    BinopExpr Or b (LitB False) -> simplifyExpr b
    BinopExpr Minus (BinopExpr Minus a (LitI b)) (LitI c) -> simplifyExpr $ BinopExpr Minus a (LitI (b+c))
    BinopExpr Plus (BinopExpr Plus a (LitI b)) (LitI c) -> simplifyExpr $ BinopExpr Plus a (LitI (b+c))
    BinopExpr op a b -> BinopExpr op (simplifyExpr a) (simplifyExpr b)

    a -> a
