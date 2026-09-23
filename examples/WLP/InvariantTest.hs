module InvariantTest where

import WLP.Invariant
import GCL.GCLParser.Parser (parseGCLfile)
import WLP.Wlp (wlp)
import GCL.GCLParser.GCLDatatype (Program(stmt), Expr (LitB))
import WLP.Simplify (simplifyExpr)

main :: IO ()
main = do
    gcl <- parseGCLfile "examples/GCL/E.gcl"
    let (Right prg) = gcl

    let a = wlp (stmt prg) (LitB True)
    print a
    putStrLn "====="
    print $ simplifyExpr a
    
    return ()