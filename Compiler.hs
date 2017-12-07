{-
1. Address for Variable Declaration? especially for the nested blocks later on in SBlock
2. Slide 27, lecture 6. 
    How to do Labels? In boolean operators it seems that we have to jump to a certain labels.
    How to do that?
3. Slide 17, lecture 6.
    It says that if value is needed, then we need to store and load
    How do we check that?
-}

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

import System.Process (callProcess)
import System.FilePath.Posix (addExtension)

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
  deriving (Eq, Enum)

initSt :: St
initSt = St {
    cx = [],
    limitLocals = 0,
    nextAddr = 0,
    currentStack = 0,
    limitStack = 0,
    nextLabel = L 0
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
    [ (Id "printInt", Fun (Id "Runtime/printInt") $ FunType Type_void [Type_int])
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
        Return t -> prefix t ++ "return"
        Call f -> "invokestatic" ++ toJVM f
        IConst i -> "ldc " ++ show i
        Add t -> prefix t ++ "add"
        Sub t -> prefix t ++ "sub"
        Div t -> prefix t ++ "div"
        Mul t -> prefix t ++ "mul"
        Bipush i -> "bipush " ++ show i

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
        Add t -> decStack t
        Sub t -> decStack t
        Div t -> decStack t
        Mul t -> decStack t
        Bipush _ -> incStack Type_int

------------------
--add limitlocal every time a variable is declared
newVar :: Id -> Type -> Compile ()
newVar x t = do
    headblock <- gets (head . cx)
    tailblock <- gets (tail . cx)
    currentlocal <- gets(limitLocals)
    currentAddr <- gets(nextAddr)
    let newlocal = currentlocal + 1
    let block' = Map.insert x currentAddr headblock
    --increase the next available address by size t
    let nextAddress = currentAddr + size t
    modify $ \cxt -> cxt {cx = block' : tailblock,limitLocals = newlocal, nextAddr = nextAddress}
    return ()

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
    let bl' = tail (block)
    modify $ \st -> st {cx = bl'}
    return ()

compile :: String -> Program -> IO ()
compile name prg@(PDefs defs) = do
    let sig = Map.fromList $
            builtIn ++
            map (\ def@(DFun _ f@(Id x) _ _ ) -> (f, Fun (Id $ name ++ "/" ++ x) (funType def) )) defs
    let ((), w) = evalRWS (compileProgram name prg) sig initSt
    -- Print to stdout.
    mapM_ putStrLn w
    -- Write to .j file and call jasmin
    let jfile = addExtension name "j"
    writeFile jfile $ unlines w
    --callProcess "jasmin" [jfile]
    
-- | Compiling the program.
    
compileProgram :: String -> Program -> Compile ()
compileProgram name (PDefs defs) = do
    tell header
    mapM_ compileFun defs
    where
    header =
        [ ";; BEGIN HEADER"
        , ""
        , ".class public " ++ name
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
        , "  invokestatic " ++ name ++ "/main()I"
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
    tell [ "", ".end method"]

compileStm :: Stm -> Compile ()
compileStm s = do
    case s of
        SExp e -> do
            compileExp e
            emit(Pop Type_int)
            return ()
        SDecls t ids -> do
            forM_ ids $ \id -> do
                newVar id t
            return ()
        SInit t id exp -> do
            --declare new variable
            newVar id t
            --compile the exp
            compileExp exp
            --store & load to the declared variable
            --need the address
            block <- gets(cx)
            a <- lookupVar id block
            emit(Store t a)
            emit(Load t a)
            return ()
        s -> nyi s

compileExp :: Exp -> Compile ()
compileExp e = do
    case e of
        ETrue -> do
            emit(Bipush 1)
            return()
        EFalse -> do
            emit(Bipush 0)
            return ()
        EInt i -> do
            emit (IConst i)
            return ()
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
        ELt e1 e2 -> do
            emit(Bipush 1)
            compileExp (e1)
            compileExp (e2)
            --emit if_icmplt missing
            --create / generate new label
            --declare new label
            --emit labels
            emit (Pop Type_int)
            emit (Bipush 0)
        e -> nyi e