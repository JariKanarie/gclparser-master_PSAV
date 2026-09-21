module Z3ModelChecker where

import GCL.GCLParser.GCLDatatype

import Z3.Monad

-- TODO: these are for the test, might need to be removed 21/09/2026
import WLPTest as Test
import WLP.Wlp

-- Environment mapping GCL variable names to their Z3 AST node
type Env = Map.Map String AST

-- | Recursively translates ANY GCL Expr into a Z3 AST formula. Based on the exp data type from GCLDatatypes.hs
exprToZ3 :: Env -> Expr -> Z3 AST
exprToZ3 env expr = case expr of
  -- Literals
  LitI n -> mkIntNum n
  LitB True  -> mkTrue
  LitB False -> mkFalse

  -- Variables (Lookup from environment)
  Var name -> case Map.lookup name env of
    Just ast -> return ast
    Nothing  -> error $ "Variable not bound in environment: " ++ name

  -- Binary Arithmetic & Logic Operators
  BinopExpr OpPlus  e1 e2 -> binaryOp (\x y -> mkAdd [x, y]) e1 e2
  BinopExpr OpMinus e1 e2 -> binaryOp (\x y -> mkSub [x, y]) e1 e2
  BinopExpr OpMul   e1 e2 -> binaryOp (\x y -> mkMul [x, y]) e1 e2
  BinopExpr OpDiv   e1 e2 -> binaryOp mkDiv e1 e2
  BinopExpr OpAnd   e1 e2 -> binaryOp (\x y -> mkAnd [x, y]) e1 e2
  BinopExpr OpOr    e1 e2 -> binaryOp (\x y -> mkOr [x, y]) e1 e2
  BinopExpr OpEq    e1 e2 -> binaryOp mkEq e1 e2
  BinopExpr OpNEq   e1 e2 -> binaryOp (\x y -> mkNot =<< mkEq x y) e1 e2
  BinopExpr OpLt    e1 e2 -> binaryOp mkLt e1 e2
  BinopExpr OpLte   e1 e2 -> binaryOp mkLe e1 e2
  BinopExpr OpGt    e1 e2 -> binaryOp mkGt e1 e2
  BinopExpr OpGte   e1 e2 -> binaryOp mkGe e1 e2
  BinopExpr OpImpl  e1 e2 -> binaryOp mkImplies e1 e2

  -- Unary Operators
  OpNeg e -> do
    ast <- exprToZ3 env e
    mkNot ast

  -- Array Read: a[i] -> Z3 select(a, i)
  ArrayElem arrExpr idxExpr -> do
    arrAst <- exprToZ3 env arrExpr
    idxAst <- exprToZ3 env idxExpr
    mkSelect arrAst idxAst

  -- Array Store Mutation: RepBy a idx val -> Z3 store(a, idx, val)
  RepBy arrExpr idxExpr valExpr -> do
    arrAst <- exprToZ3 env arrExpr
    idxAst <- exprToZ3 env idxExpr
    valAst <- exprToZ3 env valExpr
    mkStore arrAst idxAst valAst

  -- Parentheses
  Parens e -> exprToZ3 env e

  -- If-Then-Else / Conditionals: Cond g t f -> Z3 ite(g, t, f)
  Cond g t f -> do
    gAst <- exprToZ3 env g
    tAst <- exprToZ3 env t
    fAst <- exprToZ3 env f
    mkIte gAst tAst fAst

  other -> error $ "Type hasn't been programmed yet " ++ show other

  where
    binaryOp op e1 e2 = do
      a1 <- exprToZ3 env e1
      a2 <- exprToZ3 env e2
      op a1 a2

-- | Verify an Expr formula with Z3 on Example 3, not dynamic yet.
verifyFormula :: Expr -> IO ()
verifyFormula gclExpr = do

  result <- evalZ3 $ do

    -- 1. Create sorts
    intSort <- mkIntSort
    arraySort <- mkArraySort intSort intSort

    -- 2. Declare variables
    iVar <- mkFreshConst "i" intSort
    aVar <- mkFreshConst "a" arraySort

    -- 3. Build the Z3 AST representation
    --
    -- The formula we are checking is:
    --
    --     (i = 1) ==> (a2[i - 1] = 0)
    --
    -- where:
    --
    --     a1 = a[(i - 1) := 0]
    --     a2 = a1[((i - 1) + 1) := 1]

    zero <- mkIntNum 0
    one  <- mkIntNum 1

    -- i - 1
    iMinus1 <- mkSub [iVar, one]

    -- a[(i - 1) := 0]
    a1 <- mkStore aVar iMinus1 zero

    -- (i - 1) + 1
    idx2 <- mkAdd [iMinus1, one]

    -- a1[((i - 1) + 1) := 1]
    a2 <- mkStore a1 idx2 one

    -- a2[i - 1]
    readVal <- mkSelect a2 iMinus1

    -- a2[i - 1] = 0
    eq0 <- mkEq readVal zero

    -- i = 1
    condI <- mkEq iVar one

    -- (i = 1) ==> (a2[i - 1] = 0)
    wlpAst <- mkImplies condI eq0

    -- 4. Negate the WLP.
    --
    -- We ask Z3 whether:
    --
    --     NOT WLP
    --
    -- is satisfiable.
    --
    -- UNSAT => WLP is valid.
    -- SAT   => counterexample exists.
    notWlp <- mkNot wlpAst
    assert notWlp

    -- 5. Check satisfiability
    check

  case result of

    Unsat ->
      putStrLn
        "VERDICT: ACCEPT (Formula is valid for all inputs)"

    Sat -> do
      putStrLn
        "VERDICT: REJECT (Counterexample found)"

      putStrLn
        "Z3 found a satisfying assignment for the negated WLP."

    Undef ->
      putStrLn
        "VERDICT: UNKNOWN (Solver timed out or was inconclusive)"


main :: IO ()
main = do
  let path = Test.path1
  let wlpFormula = wlp path (LitB True)
  verifyFormula wlpFormula