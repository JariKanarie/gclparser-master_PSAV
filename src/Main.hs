module Main where

import Control.Exception (catch, SomeException)
import Control.Monad (forM_)
import Data.List (intercalate, isSuffixOf, sort)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import System.Directory (listDirectory, doesFileExist)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)
import GCL.GCLParser.GCLDatatype
import GCL.GCLParser.Parser (parseGCLfile)
import WLP.PathGen (generatePaths, GenStats(..))
import WLP.ProgramTypes (typeEnv, freeParams, bindParams)
import Z3.Z3ModelChecker (checkSatisfiable, verifyPath, PathVerdict(..))
import System.FilePath ((</>))
import WLP.Wlp (wlp)
import WLP.Invariant (removeLoops, removeLoopsTimeout)
import Z3.Monad (evalZ3)

examplesDirs :: [FilePath]
examplesDirs =
  [ "examples/GCL"
  , "examples/GCL/benchmark"
  ]

main :: IO ()
main = loop

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
  files <- mapM listInDir dirs
  pure (sort (concat files))
  where
    listInDir dir = (do
        names <- listDirectory dir
        let files = filter (".gcl" `isSuffixOf`) names
        pure [dir </> f | f <- files]
      ) `catch` \(_ :: SomeException) -> pure []

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
    Left err    -> putStrLn ("parse error: " ++ err)
    Right prog0 -> do
      binds <- askFreeParams (freeParams prog0)
      let prog = bindParams binds prog0
          tenv = typeEnv prog
      start <- getCurrentTime

      putStrLn "\n=== Stage 1: removing loops ==="
      let secondMicros = 1 * 1000 * 1000
      (stmts, _, _) <- removeLoopsTimeout tenv wlp k (stmt prog) secondMicros
      print stmts

      -- Stage 2
      putStrLn ("\n=== Stage 2: generating paths up to K=" ++ show k ++ " ===")
      (stats, p) <- generatePaths (checkSatisfiable tenv) k (prog { stmt = stmts })
      putStrLn (show (length p) ++ " feasible full path(s) found")

      -- Stage 2 + 3, stopping at the first invalid path
      (verdict, sizeSum) <- verifyAll tenv p 1 0 k

      end <- getCurrentTime
      putStrLn ""
      putStrLn ("verdict: " ++ verdict)
      putStrLn "stats:"
      putStrLn ("  (1) paths inspected: " ++ show (pathsInspected stats) ++ "   of which unfeasible (pruned): " ++ show (pathsPruned stats))
      putStrLn ("  (2) time:            " ++ show (diffUTCTime end start))
      putStrLn ("  (3) total wlp size:  " ++ show sizeSum)

verifyAll :: [(String, Type)] -> [[Stmt]] -> Int -> Int -> Int -> IO (String, Int)
verifyAll _ [] _ sizeSum _          = pure ("ACCEPT -- no invalid path found among those generated", sizeSum)
verifyAll tenv (p : ps) i sizeSum k = do
  putStrLn ("\n--- checking path " ++ show i ++ " ---")
  PathVerdict ok sz <- verifyPath (wlp k) tenv p (LitB True)
  let sizeSum' = sizeSum + sz
  if ok
    then verifyAll tenv ps (i + 1) sizeSum' k
    else pure ("REJECT -- path " ++ show i ++ " is invalid (see the counterexample above)", sizeSum')