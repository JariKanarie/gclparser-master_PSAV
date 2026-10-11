module WLP.Wlp
  ( wlp
  , wlpPath
  , feasibilityCond
  , feasibilityCondPath
  , subst
  , freeVars
  , exprSize
  ) where

import GCL.GCLParser.GCLDatatype
import GCL.ExamplesOfSemanticFunction (freeVariables)
import Data.Set hiding (foldr, map, filter)

-- | get a set of free variables in expression e.
freeVars :: Expr -> Set String
freeVars = fromList . freeVariables

-- | A name derived from 'base' that isn't in 'used'.
newVar :: String -> Set String -> String
newVar base used = head (filter (`notMember` used) vars)
  where vars = [base ++ "$" ++ show n | n <- [(0 :: Int) ..]]

-- | @subst x e f@ is @f[e\x]@: replace every free occurrence of variable @x@ in @f@ with @e@.
-- Capture-avoiding: a quantifier whose bound name would otherwise capture a variable free in @e@ gets alpha-renamed first.
subst :: String -> Expr -> Expr -> Expr
subst x e1 = go
  where
    go :: Expr -> Expr
    go v@(Var y)
      | y == x    = e1
      | otherwise = v
    go v@(LitI _)         = v
    go v@(LitB _)         = v
    go LitNull            = LitNull
    go (ArrayElem a i)    = ArrayElem (go a) (go i)
    go (OpNeg e2)         = OpNeg (go e2)
    go (BinopExpr op a b) = BinopExpr op (go a) (go b)
    go (SizeOf e2)        = SizeOf (go e2)
    go (RepBy a i v)      = RepBy (go a) (go i) (go v)
    go (Cond g t f)       = Cond (go g) (go t) (go f)
    go (NewStore e2)      = NewStore (go e2)
    go d@(Dereference _)  = d 
    go (Forall y e2)    = bindVar Forall y e2
    go (Exists y e2)    = bindVar Exists y e2

    -- | @bindVar f y e2@ is a capture-avoiding version of @f y e2@, where @y@ is a bound variable and @e2@ is its scope.
    bindVar :: (String -> Expr -> Expr) -> String -> Expr -> Expr
    bindVar f y e2
      | y == x = f y e2                                -- x is shadowed
      | y `notMember` freeVars e2 = f y (go e2)        -- no capture possible
      | otherwise =
          let avoid = freeVars e2 `union` freeVars e2 `union` singleton x
              y'    = newVar y avoid
          in f y' (go (subst y (Var y') e2))           -- alpha-rename, then recurse

-- | @wlp s q@: the wlp of linear path @s@ with respect to postcondition @q@ (pass @LitB True@ at the top level 
-- the path's own asserts already carry whatever postcondition it's checking).
wlp :: Stmt -> Expr -> Expr
wlp Skip             q = q
wlp (Assert e)       q = e `opAnd` q
wlp (Assume e)       q = e `opImplication` q
wlp (Assign x e)     q = subst x e q
wlp (AAssign a i e)  q = subst a (RepBy (Var a) i e) q
wlp (Seq s1 s2)      q = wlp s1 (wlp s2 q)
wlp (Block _ s)      q = wlp s q -- Local declarations should already be uniquely named
-- [TODO] The following cases are not handled (yet) by wlp, since they are either optional (TryCatch) or not part of a linear path (IfThenElse, While, DrefAssign).
wlp s@(DrefAssign {}) _ = error ("wlp: " ++ show s)
wlp s@(TryCatch {})   _ = error ("wlp: " ++ show s)
wlp s@(IfThenElse {}) _ = error ("wlp: got a branch (" ++ show s ++ ")")
wlp s@(While {})      _ = error ("wlp: got a loop (" ++ show s ++ ")")

-- | Convenience for a path represented as an ordered list of statements rather than a pre-built Seq-chain.
wlpPath :: [Stmt] -> Expr -> Expr
wlpPath stmts q = wlp (foldr Seq Skip stmts) q

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

exprSize :: Expr -> Int
exprSize (Var _)             = 1
exprSize (LitI _)            = 1
exprSize (LitB _)            = 1
exprSize LitNull              = 1
exprSize (ArrayElem a i)     = exprSize a + exprSize i
exprSize (OpNeg e)           = exprSize e
exprSize (BinopExpr _ e1 e2) = exprSize e1 + exprSize e2
exprSize (Forall _ e)        = exprSize e
exprSize (Exists _ e)        = exprSize e
exprSize (SizeOf e)          = exprSize e
exprSize (RepBy a i v)       = exprSize a + exprSize i + exprSize v
exprSize (Cond g t f)        = exprSize g + exprSize t + exprSize f
exprSize (NewStore e)        = exprSize e
exprSize (Dereference _)     = 1