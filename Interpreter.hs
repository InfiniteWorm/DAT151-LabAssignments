{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase, EmptyCase #-}


module Interpreter where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Eval = ReaderT Sig (StateT Env IO)

type Sig = Map Id SigEntry
data SigEntry
    = FunSig
    { args :: [Arg]
    , body :: [Stm]
    }

type Env = [Block]
type Block = Map Id Val

data Val
    = VVoid
    | VInt Integer
    | VBool Bool
    | VDouble Double
  deriving (Eq, Ord, Show, Read)

  -- När man går igenom ett program och typecheckar kommer man ihåg variablernas typer, 
ltVal :: Val -> Val -> Val
ltVal (VInt x) (VInt y) = VBool (x < y)
ltVal (VDouble x) (VDouble y) = VBool (x < y)

-- | Result
data Res
  = RRet Val
  | RCont

interpret :: Program -> IO ()
interpret (PDefs ds) = do
  -- Build signature
  let sig = Map.fromList $ map sigEntry ds
      sigEntry (DFun _t f args ss) = (f, FunSig args ss)
  -- Invoke main
  runMain sig

runMain :: Sig -> IO ()
runMain sig = do
  case Map.lookup (Id "main") sig of
    Just (FunSig [] ss) -> do
      _res <- evalStateT (runReaderT (evalStms ss) sig) [Map.empty]
      return ()

instance Monoid (Eval Res) where
  mempty       = return RCont
  mappend m m' = m >>= \case
    RCont  -> m'
    RRet v -> return (RRet v)

evalStms :: [Stm] -> Eval Res
evalStms = foldMap evalStm

evalStm :: Stm -> Eval Res
evalStm stm = case stm of
  SExp exp -> do
    _v <- evalExp exp
    return RCont
  SDecls t ids -> do
    fail $ "uninitialized variable " ++ show ids
  SInit t id exp -> do
    v <- evalExp exp
    --newVar env id v
    return RCont
  s -> fail $ "Not yet implemented: evalStm for " ++ show s



ltEqVal :: Val -> Val -> Val
ltEqVal (VInt x) (VInt y) = VBool (x <= y)
ltEqVal (VDouble x) (VDouble y) = VBool (x <= y)

gtVal :: Val -> Val -> Val
gtVal (VInt x) (VInt y) = VBool (x > y)
gtVal (VDouble x) (VDouble y) = VBool (x > y)

gtEqVal :: Val -> Val -> Val
gtEqVal (VInt x) (VInt y) = VBool (x >= y)
gtEqVal (VDouble x) (VDouble y) = VBool (x >= y)

eqVal :: Val -> Val -> Val
eqVal (VInt x) (VInt y) = VBool (x == y)
eqVal (VDouble x) (VDouble y) = VBool (x == y)

neqVal :: Val -> Val -> Val
neqVal (VInt x) (VInt y) = VBool (x /= y)
neqVal (VDouble x) (VDouble y) = VBool (x /= y)

andVal :: Val -> Val -> Val
andVal (VBool x) (VBool y) = VBool (x && y)

orVal :: Val -> Val -> Val
orVal (VBool x) (VBool y) = VBool (x || y)

multiVal :: Val -> Val -> Val
multiVal (VInt x) (VInt y) = VInt (x*y)
multiVal (VDouble x) (VDouble y) = VDouble (x*y)

plusVal :: Val -> Val -> Val
plusVal (VInt x) (VInt y) = VInt (x+y)
plusVal (VDouble x) (VDouble y) = VDouble (x+y)

minusVal :: Val -> Val -> Val
minusVal (VInt x) (VInt y) = VInt (x-y)
minusVal (VDouble x) (VDouble y) = VDouble (x-y)

divVal :: Val -> Val -> Val
divVal (VInt x) (VInt y) = VInt (x `div` y)
divVal (VDouble x) (VDouble y) = VDouble (x / y)



evalExp :: Exp -> Eval Val
evalExp e = case e of
  EInt i -> return $ VInt i
  EDouble d -> return $ VDouble d
  ETrue -> return $ VBool True
  EFalse -> return $ VBool False
  ETimes e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (multiVal u v)
  EDiv e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (divVal u v)
  EPlus e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (plusVal u v)
  EMinus e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (minusVal u v)
  EEq e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (EqVal u v)
  ENEq e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (NeqVal u v)
  ELt e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (LtVal u v)
  EGt e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (GtVal u v)
  ELtEq e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (LtEqVal u v)
  EGtEq e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (GtEqVal u v)
  EAnd e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (AndVal u v)
  EOr e1 e2 -> do
    u <- evalExp e1
    v <- evalExp e2
    return (OrVal u v)
  EApp f es -> do
    vs <- mapM evalExp es
    case f of
      Id "printInt" -> case vs of
        [VInt i] -> do
          liftIO $ putStrLn $ show i
          return VVoid
      Id "printDouble" -> case vs of
        [VDouble d] -> do
          liftIO $ putStrLn $ show d
          return VVoid
  e -> fail $ "Not yet implemented: evalExp for " ++ show e

{- newVar :: Env -> Id -> Val -> Eval ()
newVar env x v = do
    block <- head env
    let block' = Map.insert x v block
    modify $ \ env -> block':env  -}
