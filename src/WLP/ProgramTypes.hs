module WLP.ProgramTypes
  ( typeEnv
  , typeOf
  , baseName
  , freeParams
  , bindParams
  ) where

import Data.List (nub, sort)
import GCL.GCLParser.GCLDatatype
import GCL.ExamplesOfSemanticFunction (freeVariables)
import WLP.Helper (subst)

-- | A type environment for a program, mapping variable names to their types.
typeEnv :: Program -> [(String, Type)]
typeEnv prog = [(n, t) | VarDeclaration n t <- declarations prog] ++ [(n, PType PTInt) | n <- freeParams prog]

-- | Parameters and every Block-local declaration anywhere in the body.
declarations :: Program -> [VarDeclaration]
declarations prog = input prog ++ output prog ++ collectDecls (stmt prog)
  where
    collectDecls (Seq s1 s2)          = collectDecls s1 ++ collectDecls s2
    collectDecls (IfThenElse _ s1 s2) = collectDecls s1 ++ collectDecls s2
    collectDecls (While _ s)          = collectDecls s
    collectDecls (Block ds s)         = ds ++ collectDecls s
    collectDecls (TryCatch _ s1 s2)   = collectDecls s1 ++ collectDecls s2
    collectDecls _                    = []

baseName :: String -> String
baseName = takeWhile (/= '$')

typeOf :: [(String, Type)] -> String -> Type
typeOf env x = case lookup (baseName x) env of
  Just t  -> t
  Nothing -> error ("ProgramTypes: no declared type for " ++ x ++ " -- is this typeEnv built from the right Program?")

freeParams :: Program -> [String]
freeParams prog =
  sort (nub [n | n <- read2, n `notElem` declared, n `notElem` writes, n `notElem` xs])
  where
    (read2, writes, xs)  = uses (stmt prog)
    declared             = [n | VarDeclaration n _ <- declarations prog]

-- | (names read, names assigned, names used as an array) in a statement. A try/catch variable is local to its try/catch, so it is not reported.
uses :: Stmt -> ([String], [String], [String])
uses s = case s of
  Skip               -> mempty
  Assert e           -> exprUses e
  Assume e           -> exprUses e
  Assign x e         -> ([], [x], []) <> exprUses e
  AAssign a i e      -> ([], [a], [a]) <> exprUses i <> exprUses e
  DrefAssign u e     -> ([], [u], []) <> exprUses e
  Seq s1 s2          -> uses s1 <> uses s2
  IfThenElse g s1 s2 -> exprUses g <> uses s1 <> uses s2
  While g b          -> exprUses g <> uses b
  Block _ b          -> uses b
  TryCatch x s1 s2   -> let (r, w, a) = uses s1 <> uses s2
                            local     = filter (/= x)
                        in (local r, local w, local a)
  where
    -- 'freeVariables' already leaves out quantifier-bound names.
    exprUses e = (freeVariables e, [], arrayNames e)

-- | Names used in array position: a[i] or #a.
arrayNames :: Expr -> [String]
arrayNames e = [a | ArrayElem (Var a) _ <- subExprs e] ++ [a | SizeOf (Var a) <- subExprs e]

-- | An expression together with all of its sub-expressions.
subExprs :: Expr -> [Expr]
subExprs e = e : concatMap subExprs (children e)
  where
    -- children (Parens a)        = [a]
    children (ArrayElem a i)   = [a, i]
    children (OpNeg a)         = [a]
    children (BinopExpr _ a b) = [a, b]
    children (Forall _ a)      = [a]
    children (Exists _ a)      = [a]
    children (SizeOf a)        = [a]
    children (RepBy a i v)     = [a, i, v]
    children (Cond g t f)      = [g, t, f]
    children (NewStore a)      = [a]
    children _                 = []

bindParams :: [(String, Int)] -> Program -> Program
bindParams []   prog = prog
bindParams bnds prog = prog {stmt = go (stmt prog)}
  where
    e x = foldr (\(n, v) acc -> subst n (LitI v) acc) x bnds
    go Skip                 = Skip
    go (Assert p)           = Assert (e p)
    go (Assume p)           = Assume (e p)
    go (Assign x rhs)       = Assign x (e rhs)
    go (AAssign a i rhs)    = AAssign a (e i) (e rhs)
    go (DrefAssign u rhs)   = DrefAssign u (e rhs)
    go (Seq s1 s2)          = Seq (go s1) (go s2)
    go (IfThenElse g s1 s2) = IfThenElse (e g) (go s1) (go s2)
    go (While g s)          = While (e g) (go s)
    go (Block ds s)         = Block ds (go s)
    go (TryCatch x s1 s2)   = TryCatch x (go s1) (go s2)
