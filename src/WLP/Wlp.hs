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
wlp :: Int -> Stmt -> Expr -> Expr
wlp _ Skip             q = q
wlp _ (Assert e)       q = e `opAnd` q
wlp _ (Assume e)       q = e `opImplication` q
wlp _ (Assign x e)     q = subst x e q
wlp _ (AAssign a i e)  q = subst a (RepBy (Var a) i e) q
wlp k (Seq s1 s2)      q = wlp k s1 (wlp k s2 q)
wlp k (Block _ s)      q = wlp k s q -- Local declarations should already be uniquely named
wlp _ s@(DrefAssign {}) _ = error ("wlp: " ++ show s)
wlp _ s@(TryCatch {})   _ = error ("wlp: " ++ show s)
wlp k (IfThenElse g t e) q = opAnd g (wlp k t q) `opOr` opAnd (OpNeg g) (wlp k e q)
wlp k (While g body)    q = wlp k (findInvariantStmt k g body) q

wlpZ3 :: [(String, Type)] -> Int -> Stmt -> Expr -> Z3 Expr
wlpZ3 tenv k (Seq s1 s2) q = wlpZ3 tenv k s1 =<< wlpZ3 tenv k s2 q
wlpZ3 tenv k (Block _ s) q = wlpZ3 tenv k s q
wlpZ3 tenv k (While g body) q = do
  invariant <- findInvariant tenv (wlp k) k g body q (LitB True)
  liftIO $ do print invariant
  case invariant of
    Just expr -> return (expr `opImplication` q)
    Nothing -> return $ wlp k (While g body) q
wlpZ3 _ k x q = return $ wlp k x q

-- | @feasibilityCond s q@ is the condition that must hold at the start of statement @s@ in order for the path to be feasible, given that @q@ holds at the end of @s@.
feasibilityCond :: Stmt -> Expr -> Expr
feasibilityCond Skip            q = q
feasibilityCond (Assert _)      q = q
feasibilityCond (Assume e)      q = e `opAnd` q
feasibilityCond (Assign x e)    q = subst x e q
feasibilityCond (AAssign a i e) q = subst a (RepBy (Var a) i e) q
feasibilityCond (Seq s1 s2)     q = feasibilityCond s1 (feasibilityCond s2 q)
feasibilityCond s               _ = error ("feasibilityCond: unexpected " ++ show s)

-- | 'feasibilityCond' for a path given as a statement list, similar to 'wlpPath'.
feasibilityCondPath :: [Stmt] -> Expr
feasibilityCondPath stmts = feasibilityCond (foldr Seq Skip stmts) (LitB True)
