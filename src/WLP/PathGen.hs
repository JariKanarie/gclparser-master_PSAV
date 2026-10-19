module WLP.PathGen
  ( generatePaths
  , GenStats(..)
  ) where

import GCL.GCLParser.GCLDatatype
import WLP.Wlp (feasibilityCondPath)
import WLP.Helper (subst)

-- | A data type to keep track of the number of paths inspected and pruned during path generation.
data GenStats = GenStats { pathsInspected :: !Int, pathsPruned :: !Int } deriving Show

instance Semigroup GenStats where
  GenStats a b <> GenStats a' b' = GenStats (a + a') (b + b')

instance Monoid GenStats where
  mempty = GenStats 0 0

-- | Every full path of a program up to depth k, and the pruning stats collected along the way.
generatePaths :: (Expr -> IO Bool) -> Int -> Program -> IO (GenStats, [[Stmt]])
generatePaths sat k prog = explore k [] 0 (stmt prog) []
  where
    explore :: Int -> [Stmt] -> Int -> Stmt -> [Stmt] -> IO (GenStats, [[Stmt]])
    explore b acc n cur cont = case cur of
      Seq s1 s2           -> explore b acc n s1 (s2 : cont)
      IfThenElse g s1 s2  -> branch (g, Just s1) (OpNeg g, Just s2) b acc n cont
      While g body        -> branch (g, Just (Seq body (While g body))) (OpNeg g, Nothing) b acc n cont
      Block decls s       -> let (s', n') = freshBlock n decls s in explore b acc n' s' cont
      TryCatch {}         -> error "TryCatch not implemented yet" -- exceptions extension (4.1), not implemented
      DrefAssign {}       -> error "DrefAssign not implemented yet" -- pointer extension (4.2), not implemented
      basic               -> step basic b acc n cont

    -- | A single step in the path exploration. If the budget is exhausted, we discard the path and count it as an inspected leaf. Otherwise, we either continue with the next statement in the continuation or record a full path if there are no more statements to explore.
    step :: Stmt -> Int -> [Stmt] -> Int -> [Stmt] -> IO (GenStats, [[Stmt]])
    step s b acc n cont
      | b <= 0      = pure (GenStats 1 0, [])   -- would be the (K+1)th statement: not a full path, discard
      | otherwise   = case cont of
        []          -> pure (GenStats 1 0, [acc ++ [s]])
        (c : rest)  -> explore (b - 1) (acc ++ [s]) n c rest

    -- | A branch's own condition costs one unit of b too (it becomes an Assume in the path, and the assignment counts those explicitly).
    branch :: (Expr, Maybe Stmt) -> (Expr, Maybe Stmt) -> Int -> [Stmt] -> Int -> [Stmt] -> IO (GenStats, [[Stmt]])
    branch (gA, msA) (gB, msB) b acc n cont
      | b <= 0 = pure (GenStats 1 0, [])
      | otherwise = do
          let accA  = acc ++ [Assume gA]
              accB  = acc ++ [Assume gB]
              b'    = b - 1
              onto sideAcc Nothing = case cont of
                []          -> pure (GenStats 1 0, [sideAcc])
                (c:rest)    -> explore b' sideAcc n c rest
              onto sideAcc (Just s) = explore b' sideAcc n s cont
          okA <- sat (feasibilityCondPath accA)
          (statsA, pathsA)  <- if okA then onto accA msA else pure (GenStats 1 1, [])
          okB <- sat (feasibilityCondPath accB)
          (statsB, pathsB)  <- if okB then onto accB msB else pure (GenStats 1 1, [])
          pure (statsA <> statsB, pathsA ++ pathsB)

    -- | Freshen the names of the local variables in a block to ensure they are unique.
    freshBlock :: Int -> [VarDeclaration] -> Stmt -> (Stmt, Int)
    freshBlock n0 decls body = foldl step' (body, n0) decls
      where
        step' (s, n) (VarDeclaration x _) = let x' = x ++ "$" ++ show n in (renameStmt x x' s, n + 1)

    -- | Rename a variable in a statement, ensuring that the new name is used consistently throughout the statement.
    renameStmt :: String -> String -> Stmt -> Stmt
    renameStmt old new = go
      where
        e = subst old (Var new)
        go Skip                 = Skip
        go (Assert p)           = Assert (e p)
        go (Assume p)           = Assume (e p)
        go (Assign x rhs)       = Assign (if x == old then new else x) (e rhs)
        go (AAssign a i rhs)    = AAssign (if a == old then new else a) (e i) (e rhs)
        go (DrefAssign u rhs)   = DrefAssign (if u == old then new else u) (e rhs)
        go (Seq s1 s2)          = Seq (go s1) (go s2)
        go (IfThenElse g s1 s2) = IfThenElse (e g) (go s1) (go s2)
        go (While g s)          = While (e g) (go s)
        go (Block ds s)
          | old `elem` [ v | VarDeclaration v _ <- ds ] = Block ds s
          | otherwise                                   = Block ds (go s)
        go (TryCatch x s1 s2)
          | x == old            = TryCatch x s1 s2
          | otherwise           = TryCatch x (go s1) (go s2)