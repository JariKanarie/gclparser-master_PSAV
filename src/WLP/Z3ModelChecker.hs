module WLP.Z3ModelChecker where

import GCL.GCLParser.GCLDatatype
import qualified Data.Map as Map
import qualified Data.Set as Set

import Z3.Monad
import Control.Monad.IO.Class (liftIO)

-- TODO: these are for the test, might need to be removed 21/09/2026
import WLPTest as Test
import WLP.Wlp
import GCL.GCLParser.Parser ( parseGCLfile )
import Data.Typeable (typeOf)

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
    Alias            -> binaryOp mkEq e1 e2 -- Not sure but just to be sure

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

  -- Handle of #a example: (0 < i < #a)
  SizeOf (Var name) -> case Map.lookup ("#" ++ name) env of
    Just ast -> return ast
    Nothing  -> error $ "var not in environment: #" ++ name -- should't happen if wlp is correctly implemented

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

  -- Universal quantifer (for all: ∀)
  Forall varName bodyExpr -> do
    intSort <- mkIntSort
    boundVarAst <- mkFreshConst varName intSort
    boundVarApp <- toApp boundVarAst
    let localEnv = Map.insert varName boundVarAst env
    bodyAst <- ensureBool localEnv bodyExpr
    mkForallConst [] [boundVarApp] bodyAst

  -- Existential quantifier (there exits: ∃)
  Exists varName bodyExpr -> do
    intSort <- mkIntSort
    boundVarAst <- mkFreshConst varName intSort
    boundVarApp <- toApp boundVarAst
    let localEnv = Map.insert varName boundVarAst env
    bodyAst <- ensureBool localEnv bodyExpr
    mkExistsConst [] [boundVarApp] bodyAst

  other -> error $ "Type hasn't been programmed yet: " ++ show other ++ " of type: " ++ show (typeOf other)

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

ensureInt :: Env -> Expr -> Z3 AST
ensureInt env expr = do
  ast <- exprToZ3 env expr
  sort <- getSort ast
  kind <- getSortKind sort
  if kind == Z3_BOOL_SORT
    then do
      one  <- mkIntNum 1
      zero <- mkIntNum 0
      mkIte ast one zero
    else return ast

-- | Function to force an AST expression to be of sort Bool
ensureBool :: Env -> Expr -> Z3 AST
ensureBool env expr = do
  ast <- exprToZ3 env expr
  sort <- getSort ast
  kind <- getSortKind sort
  if kind == Z3_INT_SORT
    then do
      zero <- mkIntNum 0
      mkNot =<< mkEq ast zero
    else return ast

-- | Takes an Expr (WLP result) and produces a Z3 AST
buildZ3Formula :: Expr -> Z3 AST
buildZ3Formula wlpFormula = do
  let vars = freeVars wlpFormula

  intSort <- mkIntSort
  arrSort <- mkArraySort intSort intSort

  envList <- concat <$> mapM (\v -> do
    if v `elem` ["a", "b"]
      then do
        z3Arr  <- mkFreshConst v arrSort
        z3Size <- mkFreshConst ("#" ++ v) intSort -- SMT variable named "#a"
        return [ (v, z3Arr)
               , ("#" ++ v, z3Size)
               ]
      else do
        z3Var <- mkFreshConst v intSort
        return [(v, z3Var)]
    ) (Set.toList vars)
  
  let env = Map.fromList envList   
  ensureBool env wlpFormula

checkFormulaSatisfiability :: AST -> Z3 ()
checkFormulaSatisfiability wlpAst = do
--Negate formula and check with Z3
--Negation is required because normally it checks for 1 variable as counterexample, now it asks to check if there are any variables
  notWlp <- mkNot wlpAst 
  assert notWlp
  
  (result, mModel) <- solverCheckAndGetModel 
  case result of
    Unsat -> liftIO $ putStrLn "SAT: (Formula is valid for all inputs)"
    Sat   -> case mModel of
      Just model -> do
        str <- modelToString model
        liftIO $ do               
          putStrLn "UNSAT: (Counterexample found)"
          putStrLn "Counterexample Model:"
          putStrLn str
      Nothing -> liftIO $ putStrLn "SAT: (Counterexample found, but no model available)"
    Undef -> liftIO $ putStrLn "UNKNOWN/UNDEF: (Solver timed out or was inconclusive)"

verifyWLP :: Expr -> IO ()
verifyWLP wlpExpr = evalZ3 $ do
  wlpAst <- buildZ3Formula wlpExpr
  
  -- FOR TESTING
  astStr <- astToString wlpAst
  liftIO $ do
    putStrLn "\n=== 3. Translated Z3 SMT-LIB Formula ==="
    putStrLn astStr

  -- KEEP
  checkFormulaSatisfiability wlpAst

-- verifyPath :: [Stmt] -> Expr -> IO ()
-- verifyPath path postCond = verifyWLP (wlpPath path postCond)

verifyPath :: [Stmt] -> Expr -> IO ()
verifyPath path postCond = do

  -- FOR TESTING
  let wlpFormula = wlpPath path postCond -- wlpPath should be done somewhere else and the formula should just be given as a paramater
  putStrLn "=== 1. Raw GCL WLP Expression ==="
  print wlpFormula
  putStrLn "=================================\n"

  -- KEEP 
  verifyWLP wlpFormula

main :: IO ()
main = do
  gcl <- parseGCLfile "examples/GCL/benchmark/memberOf.gcl" -- simpletest only one that works without while and if-then-else statement from .gcl files
  let (Right prg) = gcl
  verifyPath [stmt prg] (LitB True)
  
  -- verifyPath [Test.ePath] (LitB True)  -- path is wrong, is still hardcoded, but requires a call from different file 
                                            -- and still uses a path, while it should use the result of the WLP.
                                            -- In buildZ3Formula the wlp function is used!!! needs to removed