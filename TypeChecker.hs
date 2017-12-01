{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
module TypeChecker where

--importing monad library
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

--import Data.List and Data.Map
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map

--import the abstract syntax, Print and ErrM
import CPP.Abs
import CPP.Print
import CPP.ErrM

--instance of MonadError
instance MonadError String Err where
  throwError msg = Bad msg
  catchError e h = case e of
    Ok a    -> Ok a
    Bad msg -> h msg

--monad type for typechecking
type TC = ReaderT Sig (StateT Cxt Err)

--data type for function signature
--consists of an Id (function name) and SigEntry
type Sig = Map Id SigEntry

--data type for function return type and arguments
--so if this declared in cc file : int somefunction (bool arg1, bool arg2)
--then returnType would be int, and args would be arg1 and arg2
data SigEntry
  = FunSig
   { returnType :: Type
   , args       :: [Arg]
   }

--data type for context. Consists of function return type (cxtReturnType)
--and cxtBlocks (a container for each declared variable within a scope)
--cxtBlocks is our environtment
data Cxt = Cxt
  { cxtReturnType :: Type
  , cxtBlocks     :: [Block]
  }

--for variable declaration
type Block = Map Id Type 

--start here
typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
  --creating / initializing all of the function signatures
  let sig = Map.fromList sigPairs
      -- sigPairs is the function signature : function name, return type, and arguments
      sigPairs = map sigEntry defs ++
        --these 4 function is considered as a built-in function in the lab description
        [ (Id "printInt", FunSig Type_void [ ADecl Type_int undefined ]),
        (Id "printDouble", FunSig Type_void [ ADecl Type_double undefined ]),
        (Id "readInt", FunSig Type_int [] ),
        (Id "readDouble", FunSig Type_double [])
        ]
        --sigEntry is the function signature, so it takes the abstract syntax of DFun
        --and only takes the function name f, return type t, and the arguments
      sigEntry (DFun t f args _stms) = (f, FunSig t args)
  --checking whether there exists multiple function with the same name
  let names = map fst sigPairs
      dup   = names List.\\ List.nub names
  unless (null dup) $ do
    throwError $ "the following functions are defined several times: " ++
      List.intercalate ", " (map printTree dup)
  --start the typeChecker with monad state. the Cxt Type_void [] is the initial state
  evalStateT (runReaderT (checkDefs defs) sig) (Cxt Type_void [])
  --call the checkMain function
  checkMain sig
 
{- f :: Int -> Int
f init = (5.0, init + 1)

g :: Int -> ((), Int)
g oldState = case f oldState of
  (x, newState) -> (..., newState + 1) -}

--looks up for a function called "main"
checkMain :: Sig -> Err ()
checkMain sig = do
  case Map.lookup (Id "main") sig of
    Just (FunSig t args) -> do
     unless (t == Type_int) $ throwError $ "function main can only be declared with int"
     unless (null args) $ throwError $ "function main cannot take any arguments"
    Nothing -> throwError $ "function main does not exists"
   
--check the function definitions, called in line 78 (the evalstateT ...)
checkDefs :: [Def] -> TC ()
--reminder : statement below means : apply function checkDef to each element in defs
checkDefs defs = mapM_ checkDef defs

--put the empty blocks within the context, and do check arguments and statements
checkDef :: Def -> TC ()
checkDef (DFun t f args stms) = do
  put $ Cxt t [Map.empty]
  checkArgs args
  checkStms stms

  {- let checkArg e (ADecl t _) = checkExp e t
  zipWithM_ checkArg es args -}

--declaring all arguments as variables
checkArgs :: [Arg] -> TC ()
--statement below means : If each arg has the abstract syntax of ADecl t x, then declare a new variable.
--then apply that function to each element in args
checkArgs args = mapM_ (\ (ADecl t x) -> newVar x t) args

--same explanation like checkDefs
checkStms :: [Stm] -> TC ()
checkStms stms = mapM_ checkStm stms

--creating a new block
newBlock :: TC ()
newBlock = do
  t <- gets(cxtReturnType)  --gets the current return type
  bl <- gets(cxtBlocks)     --gets the current block
  let bl' = Map.empty : bl  --append empty block to the head of the current block
  put $ Cxt t bl'           --put the current type and the modified block in the context
  return ()

--deleting a block
deleteBlock :: TC ()
deleteBlock = do
  t <- gets(cxtReturnType)   --gets the current return type
  bl <- gets(cxtBlocks)      --gets the current block
  put $ Cxt t $ tail(bl)     --pop the head of the block
  return ()

--checking a statement goes here
checkStm :: Stm -> TC ()
checkStm stm = case stm of
  -- if a statement is an expression
  SExp e -> do
    t <- inferExp e
    return ()

  -- if a statement is a variable declaration
  SDecls t ids -> do
    unless (t/=Type_void) $ throwError $ "Variable declaration cannot have Void as the type"
    forM_ ids $ \id -> do
      newVar id t
    return ()

  -- if a statement is a while loop statement
  SWhile exp stm -> do
    checkExp exp Type_bool
    newBlock
    checkStm stm
    deleteBlock
    return ()

  -- if a statement is an if else statement
  SIfElse exp stms1 stms2 -> do
    checkExp exp Type_bool
    newBlock
    checkStm stms1
    deleteBlock
    
    newBlock
    checkStm stms2
    deleteBlock
    return ()

  --if a statement is a variable declaration with initialization
  SInit t id exp -> do
    checkExp exp t
    unless (t/=Type_void) $ throwError $ "Variable declaration cannot have Void as the type"
    newVar id t
    return ()

  --if a statement is a return statement
  SReturn exp -> do
    t <- inferExp exp
    t' <- gets (cxtReturnType)
    unless (t==t') $ throwError $ "return type mismatch"
    return ()

  --if a statement is a statement block : { statements }
  SBlock stms -> do
    --Armand's notes : 
    --anropa ny block, kör statements, rensa stack (ta bort det block(delete block) man la dit i början) look for deleteblock
    --inbuilt recursion takes care of nestled blocks.  
    --Scope = ctx = block 
    newBlock          --create new block
    checkStms stms    --check statements
    deleteBlock       --delete the added block
    return ()

--type inference for each expression
--basically to determine what is the type for each expression
inferExp :: Exp -> TC Type
inferExp exp = case exp of
  --expression is a literal integer
  EInt _ -> return Type_int

  --expression is a literal double
  EDouble _ -> return Type_double

  --expression is a literal True
  ETrue -> return Type_bool

  --expression is a literal False
  EFalse -> return Type_bool

  --expression is a plus operator between 2 expressions
  EPlus e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t

  --expression is a minus operator between 2 expressions
  EMinus e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t

  --expression is a multiply operator between 2 expressions
  ETimes e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t

  --expression is a division operator between 2 expressions
  EDiv e1 e2 -> do
    t <- inferBin [Type_int, Type_double] e1 e2
    return t

  --expression is an == operator between 2 expressions
  EEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t

  --expression is a != operator between 2 expressions
  ENEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t

  --expression is a < operator between 2 expressions
  ELt e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t

  --expression is a > operator between 2 expressions
  EGt e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  
  --expression is a <= operator between 2 expressions
  ELtEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t

  --expression is a >= operator between 2 expressions
  EGtEq e1 e2 -> do
    t <- inferBool [Type_int, Type_double] e1 e2
    return t
  
  --expression is an && operator between 2 expressions
  EAnd e1 e2 -> do
    t <- inferBool [Type_bool] e1 e2
    return t

  --expression is an || operator between 2 expressions
  EOr e1 e2 -> do
    t <- inferBool [Type_bool] e1 e2
    return t

  --expression is a variable
  EId id -> do
    block <- gets(cxtBlocks)
    t <- lookupVar id block
    return t

  --expression is a ++ operator. Example : i++;
  EPostIncr id -> do
    t <- checkId id [Type_int,Type_double]
    return t

  --expression is a ++ operator. Example : i--;
  EPostDecr id -> do
    t <- checkId id [Type_int,Type_double]
    return t

  --expression is a ++ operator. Example : ++i;
  EPreIncr id -> do
    t <- checkId id [Type_int,Type_double]
    return t

  --expression is a ++ operator. Example : --i;
  EPreDecr id -> do
    t <- checkId id [Type_int,Type_double]
    return t

  --expression is an assignment of value to a variable
  EAss id exp -> do
    block <- gets(cxtBlocks)
    t <- lookupVar id block 
    checkExp exp t
    return t

  --expression is a function call
  e@(EApp f es) -> do
    sig <- ask
    case Map.lookup f sig of
     Nothing -> throwError $ "function undefined in : " ++ printTree e
     Just (FunSig t args) -> do
      unless (length args == length es) $ throwError $ "wrong number of arguments in " ++ printTree e
      let checkArg e (ADecl t _) = checkExp e t
      zipWithM_ checkArg es args
      return t
  
--type inference for +,-,*,/ operator
inferBin :: [Type] -> Exp -> Exp -> TC Type
inferBin types e1 e2 = do
  t <- inferExp e1
  if elem t types
   then do
     checkExp e2 t
     return t
   else 
     throwError $ "wrong type of expression " ++ printTree e1

--type inference for <,<=,>,>=,==,!=,&&,|| operator
inferBool :: [Type] -> Exp -> Exp -> TC Type
inferBool types e1 e2 = do
  t <- inferExp e1
  if elem t types
    then do
      checkExp e2 t
      return Type_bool
    else
      throwError $ "wrong type of expression " ++ printTree e1
  
--checking whether given expression has the same type as the given type
checkExp :: Exp -> Type -> TC ()
checkExp e t = do
  t' <- inferExp e
  unless (t==t') $ throwError $ "Expected type " ++ printTree t ++ ", got type " ++ printTree t'

{- getId :: Id -> TC Type
getId x = do
  block <- gets (head . cxtBlocks)
  case Map.lookup x block of
    Nothing -> throwError $ "variable undefined : " ++ printTree x
    Just t -> return t -}

--searching for a variable within the block
lookupVar :: Id -> [Block] -> TC Type
lookupVar id [] = throwError $ "variable undefined : " ++ printTree id
lookupVar id block = do
  let headbl = head(block)
  case Map.lookup id headbl of
    Nothing -> do
      let tailbl = tail(block)
      lookupVar id tailbl
    Just t -> return t

--check whether the given variable type is a member of the given list of types
checkId :: Id -> [Type] -> TC Type
checkId x types = do
  block <- gets(cxtBlocks)
  t <- lookupVar x block
  if elem t types 
    then do
      return t
  else
    throwError $ "wrong type of variable : " ++ printTree x

--declaring a variable. This is inserting a new variable to the context block
newVar :: Id -> Type -> TC ()
newVar x t = do
  block <- gets (head . cxtBlocks)
  when (Map.member x block) $ throwError $ "variable " ++ printTree x ++ " has already been declared"
  let block' = Map.insert x t block
  modify $ \ cxt -> cxt { cxtBlocks = block' : tail (cxtBlocks cxt) }

--helper functin indicating which statement / expression is not yet implemented in type checker
nyi :: Show a => a -> TC b
nyi a = throwError $ "not yet implemented: checking " ++ show a
