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
      (Id "readInt", Fun (Id "Runtime/readInt") $ FunType Type_void [])
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
        Call f -> "invokestatic" ++ toJVM f
        IConst i -> "ldc " ++ show i
        Inc t a i -> prefix t ++ "inc " ++ show a ++ " " ++ show i
        Add t -> prefix t ++ "add"
        Sub t -> prefix t ++ "sub"
        Div t -> prefix t ++ "div"
        Mul t -> prefix t ++ "mul"
        Bipush i -> "bipush " ++ show i
        IfEq lbl -> "if_icmpeq " ++ toJVM lbl
        IfNeq lbl -> "if_icmne " ++ toJVM lbl
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
        Lbl _ -> incStack Type_void
        Goto _ -> incStack Type_void

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

newLabel :: Label -> Compile ()
newLabel (L {theLabel = tl}) = do
    let tl' = tl + 1
    modify $ \cxt -> cxt {nextLabel = L tl'} 


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
            block <- gets(cx)
            a <- lookupVar id block
            emit(Store t a)
            emit(Load t a)
            return ()
        SReturn exp -> do
            compileExp exp           
            rType <- gets(retType) 
            emit (Return rType)
            return ()
        SWhile exp stm -> do
            init <- gets nextLabel
            newLabel init
            lb1 <- gets nextLabel
            emit(Lbl init)
            compileExp exp
            emit(IfEqZ lb1)
            compileStm stm
            emit(Goto init)
            emit(Lbl lb1)
        --need to do : SWhile, SBlock, SIfElse
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
            label <- gets nextLabel
            newLabel label

            emit(Bipush 1)
            compileExp (e1)
            compileExp (e2)

            label' <- gets nextLabel

            emit(IfLt label')
            emit (Pop Type_int)
            emit (Bipush 0)
            emit (Lbl label')
        EPreIncr id -> do
            block <- gets(cx)
            a <- lookupVar id block
            emit (Load Type_int a)
            emit (Inc Type_int a 1)
        --Need to do : EApp, EPre/Post Inc/Decr, and E Lt/Gt/Le/Ge/And/Or
        e -> nyi e
