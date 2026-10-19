module InvariantTest where

import WLP.Invariant
import GCL.GCLParser.Parser (parseGCLfile)
import WLP.Wlp
import GCL.GCLParser.GCLDatatype (Program(stmt), Expr (LitB))
import WLP.Simplify (simplifyExpr)
import Z3.Monad (evalZ3)
import WLP.ProgramTypes (typeEnv)

main :: IO ()
main = do
    gcl <- parseGCLfile "examples/GCL/E.gcl"
    let (Right prg) = gcl
    let tenv = typeEnv prg

    -- print (stmt prg)
    (prg2, _, _) <- evalZ3 $ removeLoops tenv wlp 5 (stmt prg)
    print prg2
    a <- evalZ3 $ wlpZ3 tenv 5 prg2 (LitB True)
    print a
    putStrLn "====="
    print $ simplifyExpr a
    
    return ()