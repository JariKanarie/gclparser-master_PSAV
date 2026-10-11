module WLP.Helper where
import qualified Data.Set as Set
import GCL.GCLParser.GCLDatatype
import GCL.ExamplesOfSemanticFunction (freeVariables)

-- | get a set of free variables in expression e.
freeVars :: Expr -> Set.Set String
freeVars = Set.fromList . freeVariables

-- | Convenience for a path represented as an ordered list of statements rather than a pre-built Seq-chain.
wlpPath :: (Stmt -> Expr -> Expr) -> [Stmt] -> Expr -> Expr
wlpPath wlp stmts q = wlp (foldr Seq Skip stmts) q
