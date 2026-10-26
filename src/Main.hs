module Main where

import Control.Exception (catch, SomeException)
import Control.Monad (forM_, when)
import Data.List (intercalate, isSuffixOf, sort)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import System.Directory (listDirectory, doesFileExist, doesDirectoryExist)
import System.IO (hFlush, stdout)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)
import GCL.GCLParser.GCLDatatype
import GCL.GCLParser.Parser (parseGCLfile)
import WLP.PathGen (generatePaths, GenStats(..))
import WLP.ProgramTypes (typeEnv, freeParams, bindParams)
import Z3.Z3ModelChecker (checkSatisfiable, verifyPath, PathVerdict(..))
import System.FilePath ((</>))
import WLP.Wlp (wlp)
import WLP.Invariant (removeLoopsTimeout)
import Benchmark (runBenchmarkArgs, unsupportedFeature)
import Data.Maybe (isJust)

examplesDirs :: [FilePath]
examplesDirs = ["examples/GCL"]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> loop
    ("--benchmark" : rest) -> runBenchmarkArgs rest
    _ -> do
      putStrLn "Usage: Main [--benchmark --file FILE --k K --n N --heuristics MODE --invariant-timeout-ms MS]"
      exitFailure

loop :: IO ()
loop = do
  files <- gclFiles examplesDirs
  path  <- pickFile files
  case path of
    Nothing -> putStrLn "bye"
    Just p  -> do
      k <- askK
      runOne p k
      again <- askYesNo "\ncheck another file? (y/n): "
      if again then loop else putStrLn "bye"

-- ========================================= Menu ========================================= --

gclFiles :: [FilePath] -> IO [FilePath]
gclFiles dirs = do
  files <- mapM listRecursively dirs
  pure (sort (concat files))
  where
    listRecursively dir = (do
        names <- listDirectory dir
        nested <- mapM visit [dir </> name | name <- names]
        pure (concat nested)
      ) `catch` \(_ :: SomeException) -> pure []

    visit path = do
      isDirectory <- doesDirectoryExist path
      if isDirectory
        then listRecursively path
        else pure [path | ".gcl" `isSuffixOf` path]

pickFile :: [FilePath] -> IO (Maybe FilePath)
pickFile files = do
  putStrLn ""
  if null files
    then putStrLn ("(no .gcl files found in: " ++ show examplesDirs ++ ")")
    else do
      putStrLn "found GCL files:"
      forM_ (zip [1 :: Int ..] files) $ \(i, f) -> putStrLn ("  " ++ show i ++ ") " ++ f)
  putStrLn "  o) open a file by path"
  putStrLn "  q) quit"
  prompt "pick one: " >>= choose
  where
    choose "q" = pure Nothing
    choose "o" = do
      p <- prompt "path to .gcl file: "
      exists <- doesFileExist p
      if exists
        then pure (Just p)
        else do
          putStrLn ("no such file: " ++ p)
          pickFile files
    choose s = case readMaybe s of
      Just i | i >= 1, i <= length files -> pure (Just (files !! (i - 1)))
      _ -> do
        putStrLn "not a valid choice"
        pickFile files

ask :: String -> Int -> IO Int
ask prmt def = do
  s <- prompt $ prmt ++ " [default: " ++ show def ++ "]: "
  case s of
    "" -> pure def
    _  -> case readMaybe s of
      Just k  -> pure k
      Nothing -> do putStrLn "not a number"; ask prmt def

askK :: IO Int
askK = ask "K, max path length" 20

askYesNo :: String -> IO Bool
askYesNo msg = do
  s <- prompt msg
  case s of
    ('y':_) -> pure True
    ('n':_) -> pure False
    _       -> askYesNo msg

prompt :: String -> IO String
prompt msg = do
  putStr msg
  hFlush stdout
  getLine

askFreeParams :: [String] -> IO [(String, Int)]
askFreeParams []    = pure []
askFreeParams names = do
  putStrLn ("\nfree integer parameter(s): " ++ intercalate ", " names ++ " (enter a value to bind it; leave blank to keep it symbolic)")
  concat <$> mapM askOne names
  where
    askOne n = do
      s <- prompt ("  value for " ++ n ++ " [blank = symbolic]: ")
      case s of
        "" -> pure []
        _  -> case readMaybe s of
          Just v  -> pure [(n, v)]
          Nothing -> do putStrLn "  not an integer"
                        askOne n

runOne :: FilePath -> Int -> IO ()
runOne path k = do
  parsed <- parseGCLfile path
  case parsed of
    Left err -> putStrLn ("parse error: " ++ err)
    Right prog0 -> case unsupportedFeature (stmt prog0) of
      Just reason -> putStrLn ("Cannot verify this program: " ++ reason ++ ".")
      Nothing -> do
        binds <- askFreeParams (freeParams prog0)
        let prog = bindParams binds prog0
            tenv = typeEnv prog
        logging <- askYesNo "enable debug logging? (y/n): "
        start <- getCurrentTime

        putStrLn "\n=== Stage 1: removing loops ==="
        let invariantTimeoutMicros = 1000 * 1000
        (abstractedStmt, _, loopAbstractionComplete) <- removeLoopsTimeout tenv wlp k (stmt prog) invariantTimeoutMicros
        let stmts = if loopAbstractionComplete then abstractedStmt else stmt prog
        putStrLn $ if loopAbstractionComplete
          then "Loop abstraction: all loops handled using proved invariants."
          else "Loop abstraction incomplete: discarded partial rewrite; using original program for bounded path exploration."
        when logging (print stmts)

        putStrLn ("\n=== Stage 2: generating paths up to K=" ++ show k ++ " ===")
        (stats, paths) <- generatePaths (checkSatisfiable tenv) k (prog { stmt = stmts })
        putStrLn (show (length paths) ++ " feasible full path(s) found")

        (verdict, sizeSum) <- verifyAll tenv paths 1 0 k logging
        end <- getCurrentTime
        putStrLn ""
        putStrLn ("verdict: " ++ verdict)
        putStrLn "stats:"
        putStrLn ("  (1) paths inspected: " ++ show (pathsInspected stats) ++ "   of which unfeasible (pruned): " ++ show (pathsPruned stats))
        putStrLn ("  (2) time:            " ++ show (diffUTCTime end start))
        putStrLn ("  (3) total wlp size:  " ++ show sizeSum)
        putStrLn ("  (4) complete:        " ++ show (isJust $ maxDepth stats))

verifyAll :: [(String, Type)] -> [[Stmt]] -> Int -> Int -> Int -> Bool -> IO (String, Int)
verifyAll _ [] _ sizeSum _ _ = pure ("ACCEPT -- no invalid path found among those generated", sizeSum)
verifyAll tenv (path : rest) index sizeSum k logging = do
  putStrLn ("\n--- checking path " ++ show index ++ " ---")
  PathVerdict valid size <- verifyPath (wlp k) tenv path (LitB True) logging
  let newSizeSum = sizeSum + size
  if valid
    then verifyAll tenv rest (index + 1) newSizeSum k logging
    else do
      putStrLn ("Invalid path: " ++ show path)
      pure ("REJECT -- path " ++ show index ++ " is invalid (see the counterexample above)", newSizeSum)
