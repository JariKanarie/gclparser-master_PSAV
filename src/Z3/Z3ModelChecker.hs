module Z3.Z3ModelChecker where

import GCL.GCLParser.GCLDatatype
import qualified Data.Map as Map
import qualified Data.Set as Set
import Z3.Monad
import Control.Monad.IO.Class (liftIO)
import WLP.Helper (wlpPath, freeVars, exprSize)
import WLP.ProgramTypes (baseName)
import WLP.Simplify (simplifyExpr)

-- Environment mapping GCL variable names to their Z3 AST node
type Env = Map.Map String AST

-- | The Z3 sort for a GCL type.
gclSort :: Type -> Z3 Sort
gclSort (PType PTInt)  = mkIntSort
gclSort (PType PTBool) = mkBoolSort
gclSort (AType p)      = do intS <- mkIntSort
                            rangeS <- gclSort (PType p)
                            mkArraySort intS rangeS
gclSort RefType        = error "Z3ModelChecker: ref type -- pointer extension (4.2) not supported"

-- | Recursively translate supported GCL expressions into Z3 ASTs.
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

  -- Binary Arithmetic & Logic Operators // type do not correspond with datatype
  BinopExpr op e1 e2 -> case op of
    -- Arithmetic (Returns Int)
    Plus     -> binaryIntOp (\x y -> mkAdd [x, y]) e1 e2
    Minus    -> binaryIntOp (\x y -> mkSub [x, y]) e1 e2
    Multiply -> binaryIntOp (\x y -> mkMul [x, y]) e1 e2
    Divide   -> binaryIntOp mkDiv e1 e2

    -- Relational (Returns Bool)
    Equal            -> binaryOp mkEq e1 e2
    LessThan         -> binaryOp mkLt e1 e2
    LessThanEqual    -> binaryOp mkLe e1 e2
    GreaterThan      -> binaryOp mkGt e1 e2
    GreaterThanEqual -> binaryOp mkGe e1 e2
    Alias            -> error "Z3ModelChecker: ref equality (==) -- pointer extension (4.2) not supported"

    -- Logical (Returns Bool)
    And         -> binaryBoolOp (\x y -> mkAnd [x, y]) e1 e2
    Or          -> binaryBoolOp (\x y -> mkOr [x, y]) e1 e2
    Implication -> binaryBoolOp mkImplies e1 e2

  -- Unary Operators
  OpNeg e -> do
    ast <- exprToZ3 env e
    sort <- getSort ast
    kind <- getSortKind sort
    if kind == Z3_INT_SORT
      then mkUnaryMinus ast
      else mkNot ast

  -- Array Read: a[i] -> Z3 select(a, i)
  ArrayElem arrExpr idxExpr -> do
    arrAst <- exprToZ3 env arrExpr
    idxAst <- ensureInt env idxExpr
    mkSelect arrAst idxAst

  -- -- Handle of #a example: (0 < i < #a)
  -- SizeOf (Var name) -> case Map.lookup ("#" ++ name) env of
  --   Just ast -> return ast
  --   Nothing  -> error $ "var not in environment: #" ++ name -- should't happen if wlp is correctly implemented

  -- Array Store Mutation: RepBy a idx val -> Z3 store(a, idx, val)
  RepBy arrExpr idxExpr valExpr -> do
    arrAst <- exprToZ3 env arrExpr
    idxAst <- ensureInt env idxExpr
    valAst <- exprToZ3 env valExpr
    mkStore arrAst idxAst valAst

  -- If-Then-Else / Conditionals: Cond g t f -> Z3 ite(g, t, f)
  Cond g t f -> do
    gAst <- ensureBool env g
    tAst <- exprToZ3 env t
    fAst <- exprToZ3 env f
    mkIte gAst tAst fAst

  SizeOf e -> case Map.lookup (sizeKey e) env of
    Just ast -> return ast
    Nothing  -> error $ "Z3ModelChecker: no size symbol " ++ sizeKey e ++ " for array expression " ++ show e

  Forall x e -> do
    (v, extra) <- freshQuantified x
    v' <- toApp v
    body <- exprToZ3 (foldr (uncurry Map.insert) env extra) e
    mkForallConst [] [v'] body
    
  Exists x e -> do
    (v, extra) <- freshQuantified x
    v' <- toApp v
    body <- exprToZ3 (foldr (uncurry Map.insert) env extra) e
    mkExistsConst [] [v'] body

  other -> error $ "Type hasn't been programmed yet " ++ show other

  where
    binaryOp op e1 e2 = do
      a1 <- exprToZ3 env e1
      a2 <- exprToZ3 env e2
      op a1 a2

    binaryIntOp op e1 e2 = do
      a1 <- ensureInt env e1
      a2 <- ensureInt env e2
      op a1 a2

    binaryBoolOp op e1 e2 = do
      a1 <- ensureBool env e1
      a2 <- ensureBool env e2
      op a1 a2

    sizeKey (Var a)       = "#" ++ a
    sizeKey (RepBy a _ _) = sizeKey a
    sizeKey e             = error ("Z3ModelChecker: can't determine array size for " ++ show e)

    freshQuantified :: String -> Z3 (AST, [(String, AST)])
    freshQuantified x = case Map.lookup (baseName x) env of
      Just existing -> do
        sortHere <- getSort existing
        v <- mkFreshConst x sortHere
        kind <- getSortKind sortHere
        if kind == Z3_ARRAY_SORT
          then do
            sz <- mkFreshIntVar ("#" ++ x)
            pure (v, [(x, v), ("#" ++ x, sz)])
          else pure (v, [(x, v)])
      Nothing -> do
        v <- mkFreshIntVar x
        pure (v, [(x, v)])
        
ensureInt :: Env -> Expr -> Z3 AST
ensureInt env expr = do
  ast <- exprToZ3 env expr
  sort <- getSort ast
  kind <- getSortKind sort
  if kind == Z3_BOOL_SORT
    then do
      one  <- mkIntNum (1 :: Integer)
      zero <- mkIntNum (0 :: Integer)
      mkIte ast one zero
    else return ast

-- | Helper to force an AST expression to be of sort Bool
ensureBool :: Env -> Expr -> Z3 AST
ensureBool env expr = do
  ast <- exprToZ3 env expr
  sort <- getSort ast
  kind <- getSortKind sort
  if kind == Z3_INT_SORT
    then do
      zero <- mkIntNum (0 :: Integer)
      mkNot =<< mkEq ast zero
    else return ast

-- | Takes an Expr (WLP result) and produces a Z3 AST
buildZ3Formula :: [(String, Type)] -> Expr -> Z3 AST
buildZ3Formula tenv wlpFormula = do
  let vars = freeVars wlpFormula
  intSort <- mkIntSort
  envList <- concat <$> mapM (\v -> do
    let t = case lookup (baseName v) tenv of
              Just t' -> t'
              Nothing -> error ("buildZ3Formula: no declared type for " ++ v ++ " -- is tenv built from the right Program?")
    sortHere <- gclSort t
    case t of
      AType _ -> do
        z3Arr  <- mkFreshConst v sortHere
        z3Size <- mkFreshConst ("#" ++ v) intSort
        pure [(v, z3Arr), ("#" ++ v, z3Size)]
      _ -> do
        z3Var <- mkFreshConst v sortHere
        pure [(v, z3Var)]
    ) (Set.toList vars)
  
  let env = Map.fromList envList   
  ensureBool env wlpFormula

checkSatisfiable :: [(String, Type)] -> Expr -> IO Bool
checkSatisfiable tenv e = evalZ3 $ do
  ast <- buildZ3Formula tenv e
  assert ast
  (result, _) <- solverCheckAndGetModel
  pure (result /= Unsat)

checkFormulaSatisfiability :: AST -> Z3 Bool
checkFormulaSatisfiability wlpAst = do
  notWlp <- mkNot wlpAst
  assert notWlp
  (result, mModel) <- solverCheckAndGetModel
  case result of
    Unsat -> do
      liftIO $ putStrLn "UNSAT: (Formula is valid for all inputs)"
      pure True
    Sat   -> do
      case mModel of
        Just model -> do
          str <- modelToString model
          liftIO $ do
            putStrLn "SAT: (Counterexample found)"
            putStrLn "Counterexample Model:"
            putStrLn str
        Nothing -> liftIO $ putStrLn "SAT: (Counterexample found, but no model available)"
      pure False
    Undef -> do
      liftIO $ putStrLn "UNKNOWN/UNDEF: (Solver timed out or was inconclusive)"
      pure False  -- treated as "not confirmed valid" -- see the module docstring

-- | A data type to represent the result of verifying a path's WLP.
data PathVerdict = PathVerdict { verdictValid :: Bool, verdictSize :: Int } deriving Show

-- | Verifies the WLP of a given path against its postcondition using Z3. Returns True if the WLP is valid (unsatisfiable negation), False otherwise.
verifyWLP :: [(String, Type)] -> Expr -> IO Bool
verifyWLP tenv wlpExpr = evalZ3 $ do
  wlpAst <- buildZ3Formula tenv wlpExpr
  
  -- FOR TESTING
  astStr <- astToString wlpAst
  liftIO $ do
    putStrLn "\n=== 3. Translated Z3 SMT-LIB Formula ==="
    putStrLn astStr

  -- KEEP
  checkFormulaSatisfiability wlpAst

verifyExpr :: Expr -> Z3 Bool 
verifyExpr expr = do
  wlpAst <- buildZ3Formula [] expr
  notWlp <- mkNot wlpAst
  assert notWlp
  
  result <- solverCheck 
  case result of
    Unsat -> return True
    Sat   -> return False
    Undef -> return False

-- | Stage 3 + Stage 4 together for one path: compute its WLP (Stage 3, WLP.Wlp.wlpPath) then verify it (Stage 4, above).
verifyPath :: (Stmt -> Expr -> Expr) -> [(String, Type)] -> [Stmt] -> Expr -> IO PathVerdict
verifyPath wlp tenv path postCond = do
  let wlpFormula = simplifyExpr $ wlpPath wlp path postCond
  
  -- FOR TESTING
  putStrLn "=== 1. Raw GCL WLP Expression ==="
  print wlpFormula
  putStrLn "=================================\n"

  -- KEEP
  valid <- verifyWLP tenv wlpFormula
  pure (PathVerdict valid (exprSize wlpFormula))