{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Compiler where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import Data.Maybe
import Data.Map(Map)
import qualified Data.Map as Map

import System.Process
import System.Process (callProcess)
import System.FilePath
import System.Directory

import CPP.Abs
import CPP.Print


type Compile = RWS Sigc Output St

type Sigc = Map Id Fun

data Fun = Fun
    {
        funId      :: Id,
        funFunType :: FunType
    }

--first Type in FunType is for the return type of the function
--second Type in FunType is for the arguments
data FunType = FunType Type [Type]

data St = St
    {
        cx              :: [BlockC],
        retType         :: Type,
        limitLocals     :: Int,
        nextAddr        :: Int,
        currentStack    :: Int,
        limitStack      :: Int,
        nextLabel       :: Label
    }

type BlockC = Map Id Addr
{- data Cx = cx 
    {
        cxtBlock :: [Block]
    } -}

newtype Label = L { theLabel :: Int }
  deriving (Eq, Enum, Show)

{- type Label = Int -}

initSt :: St
initSt = St {
    cx = [],
    limitLocals = 0,
    nextAddr = 0,
    currentStack = 0,
    limitStack = 0,
    nextLabel = L 0,
    retType = Type_void
}

-- | Empty state. 
type Output = [String]

type Addr = Int

--if you want to add command, then do this 3 step : 
--1. add data code here
--2. change ...
--3. stack ...
data Code
    = Store Type Addr
    | Load Type Addr
    | IConst Integer
    | Pop Type
    | Return Type
    | Call Fun
    | Inc Type Addr Int
    | Add Type
    | Sub Type
    | Div Type
    | Mul Type
    | Bipush Integer
    | IfLt Label
    | IfLe Label
    | IfGt Label
    | IfGe Label
    | IfEq Label
    | IfNeq Label
    | IfEqZ Label
    | Goto Label
    | Lbl Label
    | Dup
    | And Type
    | Or Type


------------------------------------------
class ToJVM a where
    toJVM :: a -> String

instance ToJVM Type where
    toJVM t = case t of
        Type_int -> "I"
        Type_void -> "V"
        Type_bool -> "Z"

instance ToJVM FunType where
    toJVM (FunType typ typs) = "(" ++ (toJVM =<< typs) ++ ")" ++ toJVM typ

instance ToJVM Fun where
    toJVM (Fun (Id funName) retType) = funName ++ toJVM retType

instance ToJVM Label where
    toJVM (L l) = "L" ++ show l

builtIn :: [(Id, Fun)]
builtIn = 
    [ (Id "printInt", Fun (Id "Runtime/printInt") $ FunType Type_void [Type_int]),
      (Id "readInt", Fun (Id "Runtime/readInt") $ FunType Type_int [])
    ]

funType :: Def -> FunType
funType (DFun t _ as _) = FunType t $ map (\ (ADecl t' _) -> t') as
------------------------------------------

class Size a where
    size :: a -> Int

instance Size Type where
    size t = case t of
        Type_int -> 1
        Type_bool -> 1
        Type_void -> 0

instance Size FunType where
    size (FunType t ts) = sum (map size ts) - size t

instance Size Fun where
    size (Fun _ ft) = size ft

incStack :: Size t => t -> Compile()
incStack t = modStack (size t)

decStack :: Size t => t -> Compile()
decStack t = modStack (0 - size t)

modStack :: Int -> Compile ()
modStack n = do
    old <- gets limitStack
    new <- (n +) <$> gets currentStack
    modify $ \ st -> st {currentStack = new}
    if new > old 
        then
            modify $ \ st -> st {limitStack = new}
        else
            modify $ \ st -> st {limitStack = old}

-----------------------------------------------------

grabOutput :: Compile () -> Compile Output
grabOutput m = do
    r <- ask
    s <- get
    let((), s', w) = runRWS m r s
    put s'
    return w

prefix :: Type -> String
prefix t = case t of
    Type_int -> "i"
    Type_bool -> "i"
    Type_void -> ""

instance ToJVM Code where
    toJVM c = case c of
        Store t n -> prefix t ++ "store " ++ show n
        Load t n -> prefix t  ++ "load " ++ show n
        Pop t -> "pop"
        Dup -> "dup"
        Return t -> prefix t ++ "return"
        Call f -> "invokestatic " ++ toJVM f
        IConst i -> 
            if i <= 5
                then "iconst_" ++ show i
                else "ldc " ++ show i
        Inc t a i -> prefix t ++ "inc " ++ show a ++ " " ++ show i
        Add t -> prefix t ++ "add"
        Sub t -> prefix t ++ "sub"
        Div t -> prefix t ++ "div"
        Mul t -> prefix t ++ "mul"
        Bipush i -> "bipush " ++ show i
        IfEq lbl -> "if_icmpeq " ++ toJVM lbl
        IfNeq lbl -> "if_icmpne " ++ toJVM lbl
        IfGe lbl -> "if_icmpge " ++ toJVM lbl
        IfLe lbl -> "if_icmple " ++ toJVM lbl
        IfGt lbl -> "if_icmpgt " ++ toJVM lbl
        IfLt lbl -> "if_icmplt " ++ toJVM lbl
        IfEqZ lbl -> "ifeq " ++ toJVM lbl
        Goto lbl -> "goto " ++ toJVM lbl
        And t -> prefix t ++ "and"
        Or t -> prefix t ++ "or"
        Lbl lbl -> toJVM lbl ++  ":" 

emit :: Code -> Compile ()

emit (Store Type_void _) = return ()
emit (Load Type_void _) = return()
emit (Pop Type_void) = return()
emit c = do
    tell [toJVM c]
    case c of
        Store t _ -> decStack t
        Load t _ -> incStack t
        Pop t -> decStack t
        Return t -> decStack t
        Call f -> decStack f
        IConst _ -> incStack Type_int
        Inc t _ _ -> incStack t
        Add t -> decStack t
        Sub t -> decStack t
        Div t -> decStack t
        Mul t -> decStack t
        Bipush _ -> incStack Type_int
        IfEq _ -> decStack Type_int
        IfNeq _ -> decStack Type_int
        IfGe _ -> decStack Type_int
        IfGt _ -> decStack Type_int
        IfLe _ -> decStack Type_int
        IfLt _ -> decStack Type_int
        IfEqZ _ -> decStack Type_int
        Dup -> incStack Type_int
        And _ -> decStack Type_int
        Or _ -> decStack Type_int
        Lbl _ -> return()
        Goto _ -> return()

------------------
newVar :: Id -> Type -> Compile ()
newVar x t = do
    headblock <- gets (head . cx)
    tailblock <- gets (tail . cx)
    --get current limitLocals
    currentlocal <- gets(limitLocals)
    --get the current available address
    currentAddr <- gets(nextAddr)

    let newlocal = currentlocal + 1
    let block' = Map.insert x currentAddr headblock

    --updating the next available address
    let nextAddress = currentAddr + size t
    modify $ \cxt -> cxt {cx = block' : tailblock,limitLocals = newlocal, nextAddr = nextAddress}
    return ()

newLabel2 :: Compile Label
newLabel2 = do
    lbl <- gets nextLabel
    case lbl of
        L 0 -> do
            modify $ \cxt -> cxt {nextLabel = L 1}
            return $ L 0
        L i -> do
            let i' = i + 1
            modify $ \cxt -> cxt {nextLabel = L i'} 
            return $ L i


-- | Return address of a variable.
lookupVar :: Id -> [BlockC] -> Compile Addr
lookupVar id [] = return 100;
lookupVar id block = do
    let headbl = head(block)
    case Map.lookup id headbl of
        Nothing -> do
            let tailbl = tail(block)
            lookupVar id tailbl
        Just a -> return a


-- | Not yet implemented.

nyi :: Print a => a -> b
nyi t = error $ "Not yet implemented: compilation of: " ++ printTree t
------------------

newBlock :: Compile ()
newBlock = do
    block <- gets (cx)
    let bl' = Map.empty : block
    modify $ \st -> st {cx = bl'}
    return ()

popBlock :: Compile ()
popBlock = do
    block <- gets (cx)
    add <- gets(nextAddr)
    let headbl = head (block)
    let tailbl = tail (block)
    
    modify $ \st -> st {cx = tailbl, nextAddr = add - length headbl}
    return ()

compile :: String -> Program -> IO ()
compile name prg@(PDefs defs) = do
    let sig = Map.fromList $
            builtIn ++
            map (\ def@(DFun _ f@(Id x) _ _ ) -> (f, Fun (Id $ takeFileName name ++ "/" ++ x) (funType def) )) defs
    let ((), w) = evalRWS (compileProgram (takeFileName name) prg) sig initSt
    -- Print to stdout.
    --mapM_ putStrLn w
    -- Write to .j file and call jasmin
    let jfile = addExtension name "j"
    writeFile jfile $ unlines w
    callProcess "java" ["-jar","jasmin.jar",jfile]
    renameFile ((takeFileName name) ++ ".class") (addExtension name ".class")
    
-- | Compiling the program.
    
compileProgram :: String -> Program -> Compile ()
compileProgram name (PDefs defs) = do
    tell header
    mapM_ compileFun defs
    where
    header =
        [ ";; BEGIN HEADER"
        , ""
        , ".class public " ++ takeFileName name
        , ".super java/lang/Object"
        , ""
        , ".method public <init>()V"
        , "  .limit locals 1"
        , ""
        , "  aload_0"
        , "  invokespecial java/lang/Object/<init>()V"
        , "  return"
        , ""
        , ".end method"
        , ""
        , ".method public static main([Ljava/lang/String;)V"
        , "  .limit locals 1"
        , "  .limit stack  1"
        , ""
        , "  invokestatic " ++ takeFileName name ++ "/main()I"
        , "  pop"
        , "  return"
        , ""
        , ".end method"
        , ""
        , ";; END HEADER"
        ]

compileFun :: Def -> Compile ()
compileFun def@(DFun t f args ss) = do
    -- function header
    tell [ "", ".method public static " ++ toJVM (Fun f $ funType def) ]
    -- prepare environment
    lab <- gets nextLabel
    put initSt{ nextLabel = lab }

    put initSt { retType = t}

    newBlock
    mapM_ (\ (ADecl t' x) -> newVar x t') args

    -- compile statements
    w <- grabOutput $ do
        mapM_ compileStm ss

    -- output limits
    ll <- gets limitLocals
    ls <- gets limitStack
    tell [ "  .limit locals " ++ show ll
        , "  .limit stack  " ++ show ls
        ]

    -- output code, indented by 2
    tell $ map (\ s -> if null s then s else "  " ++ s) w

    -- function footer
    if t == Type_void
        then emit(Return Type_void)
        else do
            emit (IConst 0)
            emit (Return Type_int)
    tell [ "", ".end method"]

compileStm :: Stm -> Compile ()
compileStm s =
    case s of
        SExp e -> do
            compileExp e
            case e of 
                EApp _ _ -> return()
                otherwise -> emit (Pop Type_int)
        SDecls t ids -> do
            forM_ ids $ \id -> newVar id t
        SInit t id exp -> do
            --declare new variable
            newVar id t
            --compile the exp
            compileExp exp
            --store to the declared variable
            block <- gets(cx)
            a <- lookupVar id block
            emit(Store t a)
        SReturn exp -> do
            compileExp exp           
            rType <- gets(retType) 
            emit (Return rType)
            return ()
        SIfElse exp stm1 stm2 -> do
            false <- newLabel2
            true <- newLabel2
            compileExp exp
            emit(IfEqZ false)
            compileStm stm1
            emit(Goto true)
            emit(Lbl false)
            compileStm stm2
            emit(Lbl true)
        SBlock stms -> do
            newBlock
            mapM_ compileStm stms
            popBlock
        SWhile exp stm -> do
            test <- newLabel2
            end <- newLabel2
            emit (Lbl test)
            compileExp exp
            emit (IfEqZ end)
            compileStm stm
            emit (Goto test)
            emit (Lbl end)

compileExp :: Exp -> Compile ()
compileExp e =
    case e of
        ETrue -> do
            emit(IConst 1)
            return()
        EFalse -> do
            emit(IConst 0)
            return ()
        EInt i -> do
            emit (IConst i)
            return ()
        EId id -> do
            block <- gets(cx)
            a <- lookupVar id block
            emit (Load Type_int a)
        EPlus e1 e2 -> do
            compileExp (e1)
            compileExp (e2)
            emit (Add Type_int)
        EMinus e1 e2 -> do
            compileExp (e1)
            compileExp (e2)
            emit (Sub Type_int)
        ETimes e1 e2 -> do
            compileExp (e1)
            compileExp (e2)
            emit (Mul Type_int)
        EDiv e1 e2 -> do
            compileExp (e1)
            compileExp (e2)
            emit (Div Type_int)
        EAss id e1 -> do
            compileExp e1
            block <- gets(cx)
            a <- lookupVar id block
            emit(Store Type_int a)
            emit(Load Type_int a)
        ELt e1 e2 -> do
            emit(IConst 1)
            compileExp (e1)
            compileExp (e2)
            true <- newLabel2
            emit (IfLt true)
            emit (Pop Type_int)
            emit (IConst 0)
            emit (Lbl true)
        ELtEq e1 e2 -> do
            emit(IConst 1)
            compileExp (e1)
            compileExp (e2)
            true <- newLabel2
            emit (IfLe true)
            emit (Pop Type_int)
            emit (IConst 0)
            emit (Lbl true)
        EGt e1 e2 -> do
            emit(IConst 1)
            compileExp (e1)
            compileExp (e2)
            true <- newLabel2
            emit (IfGt true)
            emit (Pop Type_int)
            emit (IConst 0)
            emit (Lbl true)   
        EGtEq e1 e2 -> do
            emit(IConst 1)
            compileExp (e1)
            compileExp (e2)
            true <- newLabel2
            emit (IfGe true)
            emit (Pop Type_int)
            emit (IConst 0)
            emit (Lbl true) 
        EEq e1 e2 -> do
            emit(IConst 1)
            compileExp (e1)
            compileExp (e2)
            true <- newLabel2
            emit (IfEq true)
            emit (Pop Type_int)
            emit (IConst 0)
            emit (Lbl true) 
        ENEq e1 e2 -> do
            emit(IConst 1)
            compileExp (e1)
            compileExp (e2)
            true <- newLabel2
            emit (IfNeq true)
            emit (Pop Type_int)
            emit (IConst 0)
            emit (Lbl true) 
        EAnd e1 e2 -> do --lazy evaluation on && operator
            compileExp(e1)
            true <- newLabel2
            false <- newLabel2
            emit (IfEqZ true)
            emit (IConst 1)
            compileExp(e2)
            emit (And Type_int)
            emit (Goto false)
            emit (Lbl true)
            emit (IConst 0)
            emit (Lbl false)
        EOr e1 e2 -> do --lazy evaluation on || operator
            compileExp(e1)
            emit(IConst 1)
            true <- newLabel2
            false <- newLabel2
            emit (IfEq true)
            emit (IConst 0)
            compileExp(e2)
            emit(Or Type_int)
            emit (Goto false)
            emit (Lbl true)
            emit (IConst 1)
            emit (Lbl false)
        EPreIncr id -> do
            block <- gets(cx)
            a <- lookupVar id block
            emit (Inc Type_int a 1)
            emit (Load Type_int a)
        EPostIncr id -> do
            block <- gets(cx)
            a <- lookupVar id block
            emit (Load Type_int a)
            emit (Inc Type_int a 1)
        EPostDecr id -> do
            block <- gets(cx)
            a <- lookupVar id block
            emit (Load Type_int a)
            emit (Inc Type_int a (-1))
        EPreDecr id -> do
            block <- gets(cx)
            a <- lookupVar id block
            emit (Inc Type_int a $ -1)
            emit (Load Type_int a)
        EApp fname args -> do
            sig <- ask
            forM_ args $ \arg -> compileExp(arg)
            case Map.lookup fname sig of
                Just f -> emit (Call f)
        --e -> nyi e
