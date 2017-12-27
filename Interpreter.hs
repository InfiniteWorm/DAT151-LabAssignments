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

type Eval = ReaderT Sig (StateT Cxt IO)

type Sig = Map Id SigEntry
data SigEntry
    = FunSig
    { args :: [Arg]
    , body :: [Stm]
    }

data Val
    = VVoid
    | VInt Integer
    | VBool Bool
    | VDouble Double
  deriving (Eq, Ord, Show, Read)



data Cxt = Cxt
  { 
    cxtBlocks     :: [Block]
  }
type Block = Map Id Val

-- | Result
data Res
  = RRet Val
  | RCont

--intepreter entrypoint
interpret :: Program -> IO ()
interpret (PDefs ds) = do
  -- Build signature
  let sig = Map.fromList $ map sigEntry ds
      sigEntry (DFun _t f args ss) = (f, FunSig args ss)
  -- Invoke main
  runMain sig 

--evaluating main function
runMain :: Sig -> IO ()
runMain sig = do
  case Map.lookup (Id "main") sig of
    Just (FunSig [] ss) -> do
      _res <- evalStateT (runReaderT (putCxt (Cxt []) ss) sig) (Cxt [])
      return ()

--what I know is, if the result of an evaluation is RCont, then continue to the next statement
--else if the result is RRet v, then return that value, and then we're done
instance Monoid (Eval Res) where
  mempty       = return RCont
  mappend m m' = m >>= \case
    RCont  -> m'
    RRet v -> return (RRet v)

--initialize context, and then start evaluating statements
putCxt :: Cxt -> [Stm] -> Eval Res
putCxt cxt stms = do
  put $ Cxt [Map.empty]
  evalStms stms

--evaluate whole statements
evalStms :: [Stm] -> Eval Res
evalStms = foldMap evalStm

--statement evaluation
evalStm :: Stm -> Eval Res
evalStm stm = case stm of
  SExp exp -> do                  --evaluating statement as an expression
    _v <- evalExp exp
    return RCont                  
  SDecls t ids -> do              --evaluating variable declaration statement
    --for each variables declared, put that variable into current block, with Void as its initial value
    forM_ ids $ \id -> do
        newVar id VVoid
    return RCont
  SIfElse exp stm1 stm2 -> do     --evaluating if-else statement
    v <- evalExp exp
    if v == VBool True            --if condition is true, go there
        then do
          --create new block
          newBlock
          --evaluate statement, binding the result to res
          res <- evalStm stm1
          --pop the block, restoring the old block
          deleteBlock
          --return the result of evaluating the statement
          return res
        else do                   --if condition is false, go here instead (else)
          --create new block
          newBlock
          --evaluate statement, binding the result to res
          res <- evalStm stm2
          --pop the block, restoring the old block
          deleteBlock
          --return the result of evaluating the statement
          return res
  SWhile exp stm -> do            --evaluating while statemeng
    v <- evalExp exp
    if v == VBool True
      then do
        --create new block
        newBlock
        --evaluate statement, bind the result to res
        res <- evalStm stm
        --re-evaluate the while statement. This way, it will create a "loop" while interpreting while statement
        evalStm (SWhile exp stm)
        --pop the block, restoring the old block
        deleteBlock
        --return the result of evaluating the statements
        return res
      else do
        --if while condition isn't satisfied anymore, end the loop and move on to the next statement
        return RCont
  SInit t id exp -> do          --for initialization statement
    --like SDecls, but instead of giving Void as its initialization,
    --it will evaluate exp first, bind the result to v, and then
    --use v as the initialization value
    v <- evalExp exp
    newVar id v
    return RCont
  SBlock stms -> do              --for evaluating statement blocks
    --create new block
    newBlock
    --evaluate the statements within the block, bind the result to res
    res <- evalStms stms
    --pop the block, restoring the old block
    deleteBlock
    --return the evaluation result
    return res
  SReturn exp -> do              --for evaluating return statement
    --evaluate the expression first
    v <- evalExp exp
    --return RRet v, exclusive only to return statement.
    --this way, it will ignore every statement that comes after return statement
    return (RRet v)


--pushing a new block on top of the old block
newBlock :: Eval ()
newBlock = do
  oldblock <- gets cxtBlocks
  let block = Map.empty : oldblock
  put $ Cxt block
  return ()

--pop block
deleteBlock :: Eval ()
deleteBlock = do
  oldblock <- gets (tail .cxtBlocks)
  put $ Cxt oldblock 
  return ()

--evaluation for < operator
ltVal :: Val -> Val -> Val
ltVal (VInt x) (VInt y) = VBool (x < y)
ltVal (VDouble x) (VDouble y) = VBool (x < y)

--evaluation for <= operator
ltEqVal :: Val -> Val -> Val
ltEqVal (VInt x) (VInt y) = VBool (x <= y)
ltEqVal (VDouble x) (VDouble y) = VBool (x <= y)

--evaluation for > operator
gtVal :: Val -> Val -> Val
gtVal (VInt x) (VInt y) = VBool (x > y)
gtVal (VDouble x) (VDouble y) = VBool (x > y)

--evaluation for >= operator
gtEqVal :: Val -> Val -> Val
gtEqVal (VInt x) (VInt y) = VBool (x >= y)
gtEqVal (VDouble x) (VDouble y) = VBool (x >= y)

--evaluation for == operator
eqVal :: Val -> Val -> Val
eqVal (VInt x) (VInt y) = VBool (x == y)
eqVal (VDouble x) (VDouble y) = VBool (x == y)

--evaluation for != operator
neqVal :: Val -> Val -> Val
neqVal (VInt x) (VInt y) = VBool (x /= y)
neqVal (VDouble x) (VDouble y) = VBool (x /= y)

--lazy evaluation for && operator
andVal :: Val -> Val -> Val
andVal (VBool x) (VBool y) = 
  if VBool x == VBool True
    then VBool (x && y)
    else VBool False

--lazy evaluation for || operator
orVal :: Val -> Val -> Val
orVal (VBool x) (VBool y) = 
  if VBool x == VBool True
    then VBool True
    else VBool (x || y)

--evaluation for * operator
multiVal :: Val -> Val -> Val
multiVal (VInt x) (VInt y) = VInt (x*y)
multiVal (VDouble x) (VDouble y) = VDouble (x*y)

--evaluation for + operator
plusVal :: Val -> Val -> Val
plusVal (VInt x) (VInt y) = VInt (x+y)
plusVal (VDouble x) (VDouble y) = VDouble (x+y)

--evaluation for - operator
minusVal :: Val -> Val -> Val
minusVal (VInt x) (VInt y) = VInt (x-y)
minusVal (VDouble x) (VDouble y) = VDouble (x-y)

--evaluation for / operator
divVal :: Val -> Val -> Val
divVal (VInt x) (VInt y) = VInt (x `div` y)
divVal (VDouble x) (VDouble y) = VDouble (x / y)

--evaluation for ++ operator
incrVal :: Val -> Val
incrVal (VInt x) = VInt (x + 1)
incrVal (VDouble x) = VDouble (x +1.0)

--evaluation for -- operator
decrVal :: Val -> Val
decrVal (VInt x) = VInt (x - 1)
decrVal (VDouble x) = VDouble (x -1.0)

--evaluate expressions
evalExp :: Exp -> Eval Val
evalExp e = case e of
  EInt i -> return $ VInt i         --if e is an integer literal
  EDouble d -> return $ VDouble d   --if e is a double literal
  ETrue -> return $ VBool True      --if e is a boolean true literal
  EFalse -> return $ VBool False    --if e is a boolean false literal
  ETimes e1 e2 -> do                --if e is a multiplication expression (x*y)
    u <- evalExp e1
    v <- evalExp e2
    return (multiVal u v)
  EDiv e1 e2 -> do                  --if e is a division expression (x/y)
    u <- evalExp e1
    v <- evalExp e2
    return (divVal u v)
  EPostIncr id -> do                --if e is a post-increment expression (x++)
    block <- gets(cxtBlocks)
    u <- lookupVar id block
    assignVar id (incrVal u) block
    return u
  EPostDecr id -> do                --if e is a post-decrement expression (x--)
    block <- gets(cxtBlocks)
    u <- lookupVar id block
    assignVar id (decrVal u) block
    return u
  EPreIncr id -> do                 --if e is a pre-increment expression (x++)
    block <- gets(cxtBlocks)
    u <- lookupVar id block
    assignVar id (incrVal u) block
    return (incrVal u)
  EPreDecr id -> do                 --if e is a pre-decrement expression (x--)
    block <- gets(cxtBlocks)
    u <- lookupVar id block
    assignVar id (decrVal u) block
    return (decrVal u)
  EPlus e1 e2 -> do                 --if e is an addition expression (x+y)
    u <- evalExp e1
    v <- evalExp e2
    return (plusVal u v)
  EMinus e1 e2 -> do                --if e is a subtraction expression (x-y)
    u <- evalExp e1
    v <- evalExp e2
    return (minusVal u v)
  EEq e1 e2 -> do                   --if e is an equality expression (x==y)
    u <- evalExp e1
    v <- evalExp e2
    return (eqVal u v)
  ENEq e1 e2 -> do                  --if e is an inequality expression (x!=y)
    u <- evalExp e1
    v <- evalExp e2
    return (neqVal u v)
  ELt e1 e2 -> do                   --if e is a less-than expression (x<y)
    u <- evalExp e1
    v <- evalExp e2
    return (ltVal u v)
  EGt e1 e2 -> do                   --if e si a greater-than expression (x>y)
    u <- evalExp e1
    v <- evalExp e2
    return (gtVal u v)
  ELtEq e1 e2 -> do                 --if e is a less-than-equal expression (x<=y)
    u <- evalExp e1
    v <- evalExp e2
    return (ltEqVal u v)
  EGtEq e1 e2 -> do                 --if e is a greater-than-equal expression (x>=y)
    u <- evalExp e1
    v <- evalExp e2
    return (gtEqVal u v)
  EAnd e1 e2 -> do                  --if e is an and expression (x && y)
    u <- evalExp e1
    if u == VBool True              --lazy evaluation here
      then do
        v <- evalExp e2
        return (andVal u v)
      else
        return $ VBool False
  EOr e1 e2 -> do                   --if e is an or expression (x || y)
    u <- evalExp e1
    if u == VBool True              --lazy evaluation too, same as && expression
      then 
        return $ VBool True
      else do
        v <- evalExp e2
        return (orVal u v)
  EId id -> do                      --if e is a variable literal
    block <- gets(cxtBlocks)
    e <- lookupVar id block
    return e
  EAss id exp -> do                 --if e is an assignment expression (x = 5)
    v <- evalExp exp
    block <- gets(cxtBlocks)
    assignVar id v block
    return v
  EApp f es -> do                   --if e is a function call expression
    vs <- mapM evalExp es
    case f of
      Id "printInt" -> case vs of   --for built-in function printInt
        [VInt i] -> do
          liftIO $ putStrLn $ show i
          return VVoid
      Id "printDouble" -> case vs of  --for built-in function printDouble
        [VDouble d] -> do
          liftIO $ putStrLn $ show d
          return VVoid
      Id "readInt" -> case vs of    --for built-in function readInt
        [] -> do
          input <- liftIO $ getLine
          return (VInt (read input))
      Id "readDouble" -> case vs of --for built-in function readDouble
        [] -> do
          input <- liftIO $ getLine
          return (VDouble (read input))
      _ -> do                       --for any function declared in the .cc file
        --get the current signature
        sig <- ask
        --find the function in the signature
        case Map.lookup f sig of
          Just (FunSig args stms) -> do
            --backup the old context
            oldcxt <- gets cxtBlocks
            --get only the argument name (because it's originally bundled with type (ADecl type id))
            --but here we only want the id (variable name)
            let argname = map (\ (ADecl _ id) -> id) args
                --constructing a block so that it can be used by the function
                fblock = Map.fromList(zip argname vs)
                fblock' = fblock : oldcxt
            --put the modified block to Cxt
            put $ Cxt fblock'
            --evaluate the statement, bind the result to res
            res <- evalStms stms
            --restore the old context
            put $ Cxt oldcxt

            --a function usually has return statement (if its type is void, it don't have return statement)
            --hence, there can be 2 possibilities of res, either RRet v (from SReturn), or RCont (from every statement not SReturn)
            case res of
              RRet v ->
                return v
              RCont ->
                return VVoid

--putting new variable inside the context
newVar :: Id -> Val -> Eval ()
newVar x v = do
  block <- gets(head . cxtBlocks)
  let block' = Map.insert x v block
  modify $ \ cxt -> cxt {cxtBlocks = block' : tail (cxtBlocks cxt)}

--looking up variable within the current block
lookupVar :: Id -> [Block] -> Eval Val
lookupVar x block = do
  let headblock = head(block)
  case Map.lookup x headblock of
    Nothing -> do
      let tailblock = tail(block)
      lookupVar x tailblock
    Just v -> do
      if v == VVoid
        then fail $ "Uninitialized variable " ++ printTree x
        else return v

--searching for a variable within a block, then update its value
assignVar :: Id -> Val -> [Block] -> Eval ()
assignVar id val block = do
  let headblock = head(block)
      tailblock = tail(block)
  case Map.lookup id headblock of
    Nothing -> do
      --if found nothing in the head, then look through its tail
      assignVar id val tailblock
      --after it finished, re-construct the block
      block' <- gets cxtBlocks
      let newblock = headblock : block'
      put $ Cxt newblock
    Just v -> do
      --update the value of the variable
      let block' = Map.insert id val headblock
      --re-construct the block
          newblock = block' : tailblock
      put $ Cxt newblock
