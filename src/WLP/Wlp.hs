module WLP.Wlp
  ( wlp
  , feasibilityCond
  , feasibilityCondPath
  , wlpZ3
  ) where

import GCL.GCLParser.GCLDatatype
import WLP.Invariant (findInvariantStmt, findInvariant)
import WLP.Helper (subst)
import Z3.Monad (Z3)
import Control.Monad.IO.Class (liftIO)

-- | @wlp s q@: the wlp of linear path @s@ with respect to postcondition @q@ (pass @LitB True@ at the top level 
-- the path's own asserts already carry whatever postcondition it's checking).
wlp :: Stmt -> Expr -> Expr
wlp Skip             q = q
wlp (Assert e)       q = e `opAnd` q
wlp (Assume e)       q = BinopExpr Implication e q
wlp (Assign x e)     q = subst x e q
wlp (AAssign a i e)  q = subst a (RepBy (Var a) i e) q
wlp (Seq s1 s2)      q = wlp s1 (wlp s2 q)
-- Compound statements must have been expanded by PathGen. This fallback also
-- makes unsupported pointer/exception statements fail explicitly.
wlp s _ = error ("wlp: expected a linearized path statement, got " ++ show s)

wlpZ3 :: Int -> Stmt -> Expr -> Z3 Expr
wlpZ3 k (Seq s1 s2) q = wlpZ3 k s1 =<< wlpZ3 k s2 q
wlpZ3 k (Block _ s) q = wlpZ3 k s q
wlpZ3 k (While g body) q = do
  invariant <- findInvariant wlp k g body q (LitB True)
  liftIO $ do print invariant
  case invariant of
    Just expr -> return (expr `opImplication` q)
    Nothing -> return $ wlp (While g body) q
wlpZ3 k x q = return $ wlp x q

-- | @feasibilityCond s q@ is the condition that must hold at the start of statement @s@ in order for the path to be feasible, given that @q@ holds at the end of @s@.
feasibilityCond :: Stmt -> Expr -> Expr
feasibilityCond Skip            q = q
feasibilityCond (Assert _)      q = q
feasibilityCond (Assume e)      q = e `opAnd` q
feasibilityCond (Assign x e)    q = subst x e q
feasibilityCond (AAssign a i e) q = subst a (RepBy (Var a) i e) q
feasibilityCond (Seq s1 s2)     q = feasibilityCond s1 (feasibilityCond s2 q)
feasibilityCond (Block _ s)     q = feasibilityCond s q
feasibilityCond s               _ = error ("feasibilityCond: unexpected " ++ show s)

-- | 'feasibilityCond' for a path given as a statement list, similar to 'wlpPath'.
feasibilityCondPath :: [Stmt] -> Expr
feasibilityCondPath stmts = feasibilityCond (foldr Seq Skip stmts) (LitB True)
