module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM


type Env = [[(Id, Type)]]

--initialization of an empty environment stack
emptyEnv :: Env
emptyEnv = [[]]

--adding variable to the current scope
addVar :: Env -> Type -> Id -> Err Env
addVar (scope:rest) x t = 
    case lookup x scope of
      Nothing -> return (((x,t):scope):rest)
      Just _  -> fail ("Variable " ++ printTree x ++ " already declared.")

--searching a variable within a scope
lookupVar :: Env -> Id -> Err Type
lookupVar [] x = fail $ "Unknown variable " ++ printTree x ++ "."
lookupVar (scope:rest) x = case lookup x scope of
                             Nothing -> lookupVar rest x
                             Just t  -> return t

--adding a scope to the stack							 
addScope :: Env -> Env
addScope env = []:env

--program is a sequence of function definitions
typecheck :: Program -> Err ()
typecheck (PDefs defs) = checkDefs emptyEnv defs

--function definitions can be more than 1
checkDefs :: Env -> [Def] -> Err ()
checkDefs env [] = return()
checkDefs env (def:defs) = do def` <- checkDef env def
							  checkDefs def` defs

--a single function definition has 1 or more arguments, and 1 or more statements							  
checkDef :: Env -> Def -> Err ()
checkDef env d = 
	case d of
		DFun t x args stms -> do addVar env x t
								 checkArgs env args
								 checkStms env stms
								 
--arguments can be more than 1
checkArgs :: Env -> [Arg] -> Err ()
checkArgs env [] = return ()
checkArgs env (arg:args) = do arg` <- checkArg env arg
							  checkArgs arg` args
							  
--a single argument behaves like variable declaration					
checkArg :: Env -> Arg -> Err()
checkArg env arg =
	case a of
		ADecl t x -> do if t == Type_void
						then putStrLn "Argument cannot be declared with void"
						else addvar env x t

--there can be more than 1 statements within a function body
checkStms :: Env -> [Stm] -> Err ()
checkStms env [] = return ()
checkStms env (st:stms) = do env` <- checkStm env st
                             checkStms env` stms

--types of statements
checkStm :: Env -> Stm -> Err Env
checkStm env s = 
    case s of
      SDecls t x      -> addVar env t x


--checking whether a type of an expression matches the given type from parameter
checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

--type inference for expressions		 
inferExp :: Env -> Exp -> Err Type
inferExp env e = 
    case e of
      EId x         -> lookupVar env x
      EInt _         -> return Type_int
      EDouble _      -> return Type_double
      EPlus e1 e2    -> do t1 <- inferExp env e1
                           t2 <- inferExp env e2
                           if t1 == t2 
                             then return t1
                             else fail (printTree e1 ++ " has type " ++ printTree t1
                                         ++ " but " ++ printTree e2 
                                         ++ " has type " ++ printTree t2)

