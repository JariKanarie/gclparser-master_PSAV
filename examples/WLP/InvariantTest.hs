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
    gcl <- parseGCLfile "examples/GCL/benchmark/bsort.gcl"
    let (Right prg) = gcl
    let tenv = typeEnv prg

    print (stmt prg)
    (prg2, _, _) <- removeLoopsTimeout tenv wlp 50 (stmt prg) 1000
    putStrLn "====="
    print prg2
    let a = wlp 5 prg2 (LitB True)
    -- print a
    putStrLn "====="
    print $ simplifyExpr a
    
    return ()