module WLPTest where

import GCL.GCLParser.GCLDatatype
import WLP.Wlp

minus1, plus1 :: Expr -> Expr
minus1 e = opMinus e (LitI 1)
plus1  e = opPlus  e (LitI 1)

main :: IO ()
main = do
  putStrLn "=== Array-assignment example (project doc, eq. 3) ==="
  let path1 =
        Seq (Assume (opEqual (Var "i") (LitI 1)))
        (Seq (Assign "i" (minus1 (Var "i")))
        (Seq (AAssign "a" (Var "i") (LitI 0))
        (Seq (AAssign "a" (plus1 (Var "i")) (LitI 1))
             (Assert (opEqual (ArrayElem (Var "a") (Var "i")) (LitI 0))))))
  putStrLn ("path: " ++ show path1)
  putStrLn ("wlp:  " ++ show (wlp path1 (LitB True)))
  putStrLn ""

  putStrLn "=== E, loop unrolled twice (project doc, eq. 2) ==="
  let ePath =
        Seq (Assume (opLessThan (LitI 1) (Var "x")))
        (Seq (Assume (opLessThan (LitI 0) (Var "x")))
        (Seq (Assign "x" (minus1 (Var "x")))
        (Seq (Assume (opLessThan (LitI 0) (Var "x")))
        (Seq (Assign "x" (minus1 (Var "x")))
        (Seq (Assume (OpNeg (opLessThan (LitI 0) (Var "x"))))
        (Seq (Assign "y" (Var "x"))
             (Assert (opEqual (Var "y") (LitI 1)))))))))
  putStrLn ("path: " ++ show ePath)
  putStrLn ("wlp:  " ++ show (wlp ePath (LitB True)))
  putStrLn ""

  putStrLn "=== Same path, feasibility of the branch prefixes (B0, B1) ==="
  let prefixB0 =
        Seq (Assume (opLessThan (LitI 1) (Var "x")))
            (Assume (opLessThan (LitI 0) (Var "x")))
      prefixB1 =
        Seq (Assume (opLessThan (LitI 1) (Var "x")))
        (Seq (Assume (opLessThan (LitI 0) (Var "x")))
        (Seq (Assign "x" (minus1 (Var "x")))
             (Assume (opLessThan (LitI 0) (Var "x")))))
  putStrLn ("B0: " ++ show (feasibilityCond prefixB0 (LitB True)))
  putStrLn ("B1: " ++ show (feasibilityCond prefixB1 (LitB True)))
  putStrLn ""

  putStrLn "=== Capture-avoidance check ==="
  putStrLn "substituting x -> (k + 1) into (forall k :: k < x):"
  let captureCase = subst "x" (plus1 (Var "k")) (Forall "k" (opLessThan (Var "k") (Var "x")))
  putStrLn ("  naive (wrong) would give: forall k :: k < (k + 1)   -- always true, x is gone")
  putStrLn ("  actual result:            " ++ show captureCase)
