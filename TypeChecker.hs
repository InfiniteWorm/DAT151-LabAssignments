{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
module TypeChecker where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

instance MonadError String Err where
  throwError msg = Bad msg
  catchError e h = case e of
    Ok a    -> Ok a
    Bad msg -> h msg

type TC = ReaderT Sig (StateT Cxt Err)

type Sig = Map Id SigEntry
data SigEntry
  = FunSig
   { returnType :: Type
   , args       :: [Arg]
   }

data Cxt = Cxt
  { cxtReturnType :: Type
  , cxtBlocks     :: [Block]
  }
type Block = Map Id Type

typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
  let sig = Map.fromList sigPairs
      sigPairs = map sigEntry defs ++
        [ (Id "printInt", FunSig Type_void [ ADecl Type_int undefined ]),
        (Id "printDouble", FunSig Type_void [ ADecl Type_double undefined ]),
        (Id "readInt", FunSig Type_int [ undefined ]),
        (Id "readDouble", FunSig Type_double [undefined])
        ]
      sigEntry (DFun t f args _stms) = (f, FunSig t args)
  let names = map fst sigPairs
      dup   = names List.\\ List.nub names
  unless (null dup) $ do
    throwError $ "the following functions are defined several times: " ++
      List.intercalate ", " (map printTree dup)
  evalStateT (runReaderT (checkDefs defs) sig) (Cxt Type_void [])
  checkMain sig
 
checkMain :: Sig -> Err ()
checkMain sig = do
  case Map.lookup (Id "main") sig of
    Just (FunSig t args) -> do
     unless (t == Type_int) $ throwError $ "function main can only be declared with int"
     unless (null args) $ throwError $ "function main cannot take any arguments"
    Nothing -> throwError $ "function main does not exists"
   
checkDefs :: [Def] -> TC ()
checkDefs defs = mapM_ checkDef defs

checkDef :: Def -> TC ()
checkDef (DFun t f args stms) = do
  put $ Cxt t [Map.empty]
  checkArgs args
  checkStms stms

checkArgs :: [Arg] -> TC ()
checkArgs args = mapM_ (\ (ADecl t x) -> newVar x t) args

checkStms :: [Stm] -> TC ()
checkStms stms = mapM_ checkStm stms

checkStm :: Stm -> TC ()
checkStm stm = case stm of
  SExp e -> do
    _t <- inferExp e
    return ()
  SDecls t ids -> do
    unless (t/=Type_void) $ throwError $ "Variable declaration cannot have Void as the type"
    forM_ ids $ \id -> do
      newVar id t
    return ()
  SWhile exp _ -> do
    checkExp exp Type_bool
    return ()
  SIfElse exp _ _ -> do
    checkExp exp Type_bool
    return ()
  SInit t id exp -> do
    checkExp exp t
    unless (t/=Type_void) $ throwError $ "Variable declaration cannot have Void as the type"
    newVar id t
    return ()
  SReturn exp -> do
    t <- inferExp exp
    t' <- gets (cxtReturnType)
    unless (t/=t') $ throwError $ "return type mismatch"
    return ()
  SBlock stms -> do
    t <- gets (cxtReturnType)
    put $ Cxt t [Map.empty]
    checkStms stms
    return ()

inferExp :: Exp -> TC Type
inferExp exp = case exp of
  EInt _ -> return Type_int
  EDouble _ -> return Type_double
  ETrue -> return Type_bool
  EFalse -> return Type_bool
  EPlus e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t
  EMinus e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t
  ETimes e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t
  EDiv e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t
  EEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  ENEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  ELt e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  EGt e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  ELtEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  EGtEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  EAnd e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  EOr e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  EId id -> do
    t <- getId id
    return t
  EPostIncr id -> do
    t <- getId id 
    if elem t [Type_int,Type_double]
      then return t
      else throwError $ "Expected type double or int, got type " ++ printTree t
  EPostDecr id -> do
    t <- getId id 
    if elem t [Type_int,Type_double]
      then return t
      else throwError $ "Expected type double or int, got type " ++ printTree t
  EPreIncr id -> do
    t <- getId id 
    if elem t [Type_int,Type_double]
      then return t
      else throwError $ "Expected type double or int, got type " ++ printTree t
  EPreDecr id -> do
    t <- getId id 
    if elem t [Type_int,Type_double]
      then return t
      else throwError $ "Expected type double or int, got type " ++ printTree t
  EAss id exp -> do
    t <- getId id
    checkExp exp t
    return t
  e@(EApp f es) -> do
    sig <- ask
    case Map.lookup f sig of
     Nothing -> throwError $ "function undefined in : " ++ printTree e
     Just (FunSig t args) -> do
      unless (length args == length es) $ throwError $ "wrong number of arguments in " ++ printTree e
      let checkArg e (ADecl t _) = checkExp e t
      zipWithM_ checkArg es args
      return t
  
inferBin :: [Type] -> Exp -> Exp -> TC Type
inferBin types e1 e2 = do
  t <- inferExp e1
  if elem t types
   then do
     checkExp e2 t
     return t
   else 
     throwError $ "wrong type of expression " ++ printTree e1

inferBool :: [Type] -> Exp -> Exp -> TC Type
inferBool types e1 e2 = do
  t <- inferExp e1
  if elem t types
    then do
      checkExp e2 t
      return Type_bool
    else
      throwError $ "wrong type of expression " ++ printTree e1
  
checkExp :: Exp -> Type -> TC ()
checkExp e t = do
  t' <- inferExp e
  unless (t==t') $ throwError $ "Expected type " ++ printTree t ++ ", got type " ++ printTree t'

getId :: Id -> TC Type
getId x = do
  block <- gets (head . cxtBlocks)
  case Map.lookup x block of
    Nothing -> throwError $ "variable undefined : " ++ printTree x
    Just t -> return t

newVar :: Id -> Type -> TC ()
newVar x t = do
  block <- gets (head . cxtBlocks)
  when (Map.member x block) $ throwError $ "variable " ++ printTree x ++ " has already been declared"
  let block' = Map.insert x t block
  modify $ \ cxt -> cxt { cxtBlocks = block' : tail (cxtBlocks cxt) }
  
nyi :: Show a => a -> TC b
nyi a = throwError $ "not yet implemented: checking " ++ show a
