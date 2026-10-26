module Benchmark where

import Data.List (intercalate, isPrefixOf)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import System.Exit (exitFailure)
import System.FilePath (takeBaseName)
import Text.Read (readMaybe)
import GCL.GCLParser.GCLDatatype
import GCL.GCLParser.Parser (parseGCLfile)
import WLP.Invariant (removeLoopsTimeout)
import WLP.PathGen (generatePaths, GenStats(..))
import WLP.ProgramTypes (typeEnv, bindParams)
import WLP.Wlp (wlp)
import Z3.Z3ModelChecker (checkSatisfiable, verifyPathStatus, VerificationStatus(..))

runBenchmarkArgs :: [String] -> IO ()
runBenchmarkArgs args = case parseOptions args of
  Left err -> benchmarkError err
  Right opts -> case (lookup "--file" opts, lookup "--k" opts, lookup "--n" opts, lookup "--heuristics" opts, lookup "--invariant-timeout-ms" opts) of
    (Just file, Just kText, Just nText, Just mode, Just timeoutText) ->
      case (readMaybe kText :: Maybe Int, readMaybe nText :: Maybe Int, readMaybe timeoutText :: Maybe Int) of
        (Just k, Just n, Just timeoutMs)
          | k < 0 -> benchmarkError "K must be >= 0"
          | timeoutMs < 1 -> benchmarkError "invariant timeout must be positive"
          | mode `notElem` ["none", "prune", "simplify", "invariants", "prune+simplify", "prune+invariants", "all"] -> benchmarkError ("unknown heuristic mode: " ++ mode)
          | otherwise -> runBenchmark file k n mode timeoutMs
        _ -> benchmarkError "K, N, and invariant timeout must be integers"
    _ -> benchmarkError "missing required option; expected --file, --k, --n, --heuristics, and --invariant-timeout-ms"
  where
    benchmarkError err = do
      putStrLn ("BENCHMARK_ERROR\t" ++ cleanField err)
      exitFailure

parseOptions :: [String] -> Either String [(String, String)]
parseOptions [] = Right []
parseOptions (key : value : rest)
  | "--" `isPrefixOf` key = ((key, value) :) <$> parseOptions rest
  | otherwise = Left ("expected an option, got: " ++ key)
parseOptions [key] = Left ("missing value for option: " ++ key)

cleanField :: String -> String
cleanField = map (\c -> if c == '\t' || c == '\n' || c == '\r' then ' ' else c)

runBenchmark :: FilePath -> Int -> Int -> String -> Int -> IO ()
runBenchmark file k n mode invariantTimeoutMs = do
  start <- getCurrentTime
  parsed <- parseGCLfile file
  case parsed of
    Left err -> do
      putStrLn ("BENCHMARK_ERROR\tparse error: " ++ cleanField err)
      exitFailure
    Right prog0 -> do
      let prog = bindParams [("N", n)] prog0
          tenv = typeEnv prog
      case unsupportedFeature (stmt prog) of
        Just reason -> do
          end <- getCurrentTime
          let seconds = realToFrac (diffUTCTime end start) :: Double
          emitBenchmarkResult file k n mode "UNSUPPORTED" seconds 0 0 0 0 0 Nothing
            ("unsupported: " ++ reason)
        Nothing -> do
          let usePruning = mode `elem` ["prune", "prune+simplify", "prune+invariants", "all"]
              useSimplifier = mode `elem` ["simplify", "prune+simplify", "all"]
              useInvariants = mode `elem` ["invariants", "prune+invariants", "all"]
          (stmts, invariantStatus) <-
            if useInvariants
              then do
                (abstractedStmt, _, complete) <- removeLoopsTimeout tenv wlp k (stmt prog) (invariantTimeoutMs * 1000)
                pure ( abstractedStmt, if complete then "complete" else "partial" )
              else pure (stmt prog, "disabled")
          let satCheck formula = if usePruning then checkSatisfiable tenv formula else pure True
          (stats, paths) <- generatePaths satCheck k (prog { stmt = stmts })
          (verdict, sizeSum, pathsVerified, failedPath) <-
            verifyBenchmarkPaths useSimplifier (wlp k) tenv paths
          end <- getCurrentTime
          let seconds = realToFrac (diffUTCTime end start) :: Double
          emitBenchmarkResult file k n mode verdict seconds
            (pathsInspected stats) (pathsPruned stats) (length paths) pathsVerified sizeSum (maxDepth stats) invariantStatus
          case failedPath of
            Just badPath -> putStrLn ("BENCHMARK_FAIL_PATH\t" ++ cleanField (show badPath))
            Nothing -> pure ()

emitBenchmarkResult :: FilePath -> Int -> Int -> String -> String -> Double -> Int -> Int -> Int -> Int -> Int -> Maybe Int -> String -> IO ()
emitBenchmarkResult file k n mode verdict seconds inspected pruned fullPaths verified wlpSize depth invariantStatus  = do
  let depthFmt = maybe "k" show depth
  let fields = [ takeBaseName file, file, show n, show k, mode, verdict, show seconds, show inspected, show pruned, show fullPaths, show verified, show wlpSize, depthFmt, invariantStatus ]
  putStrLn ("BENCHMARK_RESULT\t" ++ intercalate "\t" (map cleanField fields))

unsupportedFeature :: Stmt -> Maybe String
unsupportedFeature statement = case statement of
  TryCatch {} -> Just "try/catch exception handling is optional extension 4.1 and is not implemented"
  DrefAssign {} -> Just "pointer/dereference assignment is optional extension 4.2 and is not implemented"
  Seq a b -> firstUnsupported (unsupportedFeature a) (unsupportedFeature b)
  IfThenElse _ a b -> firstUnsupported (unsupportedFeature a) (unsupportedFeature b)
  While _ body -> unsupportedFeature body
  Block _ body -> unsupportedFeature body
  _ -> Nothing
  where
    firstUnsupported (Just reason) _ = Just reason
    firstUnsupported Nothing other = other

verifyBenchmarkPaths :: Bool -> (Stmt -> Expr -> Expr) -> [(String, Type)] -> [[Stmt]] -> IO (String, Int, Int, Maybe [Stmt])
verifyBenchmarkPaths useSimplifier wlpFn tenv = go 0 0 False
  where
    go sizeSum count sawUnknown []
      | sawUnknown = pure ("UNKNOWN", sizeSum, count, Nothing)
      | otherwise = pure ("ACCEPT", sizeSum, count, Nothing)
    go sizeSum count sawUnknown (path : rest) = do
      (status, size) <- verifyPathStatus useSimplifier wlpFn tenv path (LitB True)
      let sizeSum' = sizeSum + size
          count' = count + 1
      case status of
        WLPVerified -> go sizeSum' count' sawUnknown rest
        WLPCounterexample -> pure ("REJECT", sizeSum', count', Just path)
        WLPUnknown -> go sizeSum' count' True rest