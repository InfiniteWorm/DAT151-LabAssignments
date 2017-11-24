module Interpreter where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

interpret :: Program -> IO ()

interpret p = putStrLn "Type checker has no errors. No interpreter yet"
