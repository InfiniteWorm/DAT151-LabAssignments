import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (dropExtension, takeFileName)

import CPP.Lex
import CPP.Par
import CPP.ErrM

import TypeChecker
import Compiler

-- | Parse, type check, and compile a program given by the @String@.

check :: FilePath -> String -> IO ()
check file s = do
  case pProgram (myLexer s) of
    Bad err  -> do
      putStrLn "SYNTAX ERROR"
      putStrLn err
      exitFailure
    Ok  tree -> do
      case typecheck tree of
        Bad err -> do
          putStrLn "TYPE ERROR"
          putStrLn err
          exitFailure
        Ok _ -> compile file tree

-- | Main: read file passed by only command line argument and call 'check'.

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> check (dropExtension $ takeFileName file) =<< readFile file
    _      -> do
      putStrLn "Usage: lab3 <SourceFile>"
      exitFailure
