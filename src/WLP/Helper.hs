module WLP.Helper where
import qualified Data.Set as Set
import GCL.GCLParser.GCLDatatype
import GCL.ExamplesOfSemanticFunction (freeVariables)

-- | get a set of free variables in expression e.
freeVars :: Expr -> Set.Set String
freeVars = Set.fromList . freeVariables

-- | Convenience for a path represented as an ordered list of statements rather than a pre-built Seq-chain.
wlpPath :: (Stmt -> Expr -> Expr) -> [Stmt] -> Expr -> Expr
wlpPath wlp stmts = wlp (foldr Seq Skip stmts)

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


-- | A name derived from 'base' that isn't in 'used'.
newVar :: String -> Set.Set String -> String
newVar base used = head (filter (`Set.notMember` used) vars)
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
      | y `Set.notMember` freeVars e2 = f y (go e2)        -- no capture possible
      | otherwise =
          let avoid = freeVars e2 `Set.union` freeVars e2 `Set.union` Set.singleton x
              y'    = newVar y avoid
          in f y' (go (subst y (Var y') e2))           -- alpha-rename, then recurse