{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module DeepShallow where

import Prelude hiding (mod,min,(<),(<=),(>),(>=),(==),(/=),(&&),(++))
import qualified Prelude
import Control.Applicative (Applicative (..))
import Control.Monad (ap,forM_)
import Control.Monad.State hiding (forM)
import Data.Array
import Data.Array.IO hiding (newArray)
import Data.Array.Base (getNumElements)
import Data.IORef
import Data.List (unfoldr)
import Data.Tree hiding (drawTree)
import Data.Tree.View

-- Preliminaries

(<) :: Ord a => FunC a -> FunC a -> FunC Bool
(<) = fromFunC $ Prim "(<)" (Prelude.<)

(<=) :: Ord a => FunC a -> FunC a -> FunC Bool
(<=) = fromFunC $ Prim "(<=)" (Prelude.<=)

(>) :: Ord a => FunC a -> FunC a -> FunC Bool
(>) = fromFunC $ Prim "(>)" (Prelude.>)

(>=) :: Ord a => FunC a -> FunC a -> FunC Bool
(>=) = fromFunC $ Prim "(>=)" (Prelude.>=)

(==) :: Eq a => FunC a -> FunC a -> FunC Bool
(==) = fromFunC $ Prim "(==)" (Prelude.==)

(/=) :: Eq a => FunC a -> FunC a -> FunC Bool
(/=) = fromFunC $ Prim "(/=)" (Prelude./=)

mod :: FunC Int -> FunC Int -> FunC Int
mod = fromFunC $ Prim "mod" Prelude.mod

min :: Ord a => FunC a -> FunC a -> FunC a
min = fromFunC $ Prim "min" Prelude.min

instance Syntactic () where
  type Internal () = ()
  toFunC ()  = Lit ()
  fromFunC _ = ()

infixr 3 &&
(&&) :: FunC Bool -> FunC Bool -> FunC Bool
(&&) = fromFunC $ Prim "(&&)" (Prelude.&&)

class Type a

instance Type Int
instance Type Bool
instance Type Float
instance Type ()

-- Deep Embedding

data FunC a where
  (:$) :: FunC (a -> b) -> FunC a -> FunC b    -- Application
  Lam  :: (FunC a -> FunC b) -> FunC (a -> b)  -- Abstraction

  -- Symbols
  Lit   :: Show a => a -> FunC a
  If    :: FunC (Bool -> a -> a -> a)
  While :: FunC ((s -> Bool) -> (s -> s) -> s -> s)
  Pair  :: FunC (a -> b -> (a,b))
  Fst   :: FunC ((a,b) -> a)
  Snd   :: FunC ((a,b) -> b)
  Prim  :: String -> a -> FunC a

  -- Interpretation of variables
  Value    :: a -> FunC a       -- Value of a variable
  Variable :: String -> FunC a  -- Name of a variable

  -- Pure arrays
  Arr    :: FunC (Int -> (Int -> a) -> Array Int a)
  ArrLen :: FunC (Array Int a -> Int)
  ArrIx  :: FunC (Array Int a -> Int -> a)

  Sequential :: FunC (s -> (s -> (a,s)) -> Int -> Array Int a)

  -- Monads
  Return :: Monad m => FunC (a -> m a)
  Bind   :: Monad m => FunC (m a -> (a -> m b) -> m b)

  -- Monadic arrays
  NewArray_   :: FunC (Int -> IO (IOArray Int a))
  GetArray    :: FunC (IOArray Int a -> Int -> IO a)
  PutArray    :: FunC (IOArray Int a -> Int -> a -> IO ())
  LengthArray :: FunC (IOArray Int a -> IO Int)
  FreezeArray :: FunC (IOArray Int a -> IO (Array Int a))
  ThawArray   :: FunC (Array Int a   -> IO (IOArray Int a))

  -- Monadic loops
  ForM   :: Monad m => FunC (Int -> (Int -> m ()) -> m ())
  WhileM :: Monad m => FunC (m Bool -> m () -> m ())

  -- Monadic references
  NewRef   :: FunC (a -> IO (IORef a))
  ReadRef  :: FunC (IORef a -> IO a)
  WriteRef :: FunC (IORef a -> a -> IO ())

pair :: FunC a -> FunC b -> FunC (a,b)
pair a b = Pair :$ a :$ b

-- Primitive Functions and Literals

instance (Num a, Show a) => Num (FunC a) where
  fromInteger = Lit . fromInteger
  a + b       = Prim "(+)" (+) :$ a :$ b
  a - b       = Prim "(-)" (-) :$ a :$ b
  a * b       = Prim "(*)" (*) :$ a :$ b
  abs a       = Prim "abs" abs :$ a
  signum a    = Prim "signum" signum :$ a

true, false :: FunC Bool
true  = Lit True
false = Lit False

-- Higher-Order Functions

ex1 :: FunC Int
ex1 = while (<= 100) (*2) 1

-- Evaluation

eval :: FunC a -> a
eval (f :$ a)   = eval f $! eval a
eval (Lam f)    = eval . f . Value
eval (Lit l)    = l
eval If         = \c t f -> if c then t else f
eval While      = \c b i -> head $ dropWhile c $ iterate b i
eval Pair       = (,)
eval Fst        = fst
eval Snd        = snd
eval (Prim _ f) = f
eval (Value a)  = a
eval Arr         = \l ixf -> let lm1 = l - 1
                            in  listArray (0,lm1) [ixf i | i  <- [0..lm1]]
eval ArrLen      = \a -> (1 +) $ uncurry (flip (-)) $ bounds a
eval ArrIx       = (!)
eval Sequential  = \init step l -> listArray (0,l-1) $ take l $
                                unfoldr (Just . step) init
eval Return      = return
eval Bind        = (>>=)
eval NewArray_   = \i -> newArray_ (0,i-1)
eval GetArray    = readArray
eval PutArray    = writeArray
eval LengthArray = getNumElements
eval FreezeArray = freeze
eval ThawArray   = thaw
eval ForM        = \l body -> forM_ [0 .. l-1] body
eval WhileM      = \cond body -> let loop = do c <- cond
                                               if c
                                               then body >> loop
                                               else return ()
                                 in loop
eval NewRef      = newIORef
eval ReadRef     = readIORef
eval WriteRef    = writeIORef

-- Extensible User Interfaces

class Syntactic a where
    type Internal a
    toFunC   :: a -> FunC (Internal a)
    fromFunC :: FunC (Internal a) -> a

instance Syntactic (FunC a) where
    type Internal (FunC a) = a
    toFunC   ast = ast
    fromFunC ast = ast

ifC :: Syntactic a => FunC Bool -> a -> a -> a
ifC c t e = fromFunC (If :$ c :$ toFunC t :$ toFunC e)

c ? (t,e) = ifC c t e

-- Pairs

instance (Syntactic a, Syntactic b) => Syntactic (a,b) where
    type Internal (a,b) = (Internal a, Internal b)
    toFunC (a,b)        = Pair :$ toFunC a :$ toFunC b
    fromFunC p          = (fromFunC (Fst :$ p), fromFunC (Snd :$ toFunC p))

forLoop :: Syntactic s => FunC Int -> s -> (FunC Int -> s -> s) -> s
forLoop len init step = snd $ while (\(i,s) -> i < len)
                                    (\(i,s) -> (i+1, step i s))
                                    (0,init)

gcd :: FunC Int -> FunC Int -> FunC Int
gcd a b = fst $ while (\(a,b) -> a /= b)
                      (\(a,b) -> a > b ? ( (a-b,b) , (a,b-a) ))
                      (a,b)

-- Embedding functions

instance (Syntactic a, Syntactic b) => Syntactic (a -> b) where
    type Internal (a -> b) = Internal a -> Internal b
    toFunC f   = Lam (toFunC . f . fromFunC)
    fromFunC f = \a -> fromFunC (f :$ toFunC a)

while :: Syntactic s => (s -> FunC Bool) -> (s -> s) -> s -> s
while = fromFunC While

-- Option

data Option a = Option { isSome :: FunC Bool, fromSome :: a }

instance Syntactic a => Syntactic (Option a) where
    type Internal (Option a) = (Bool,Internal a)
    fromFunC m               = Option (fromFunC Fst m) (fromFunC Snd m)
    toFunC (Option b a)      = fromFunC Pair b a

class Inhabited a where
    example :: FunC a

instance Inhabited Bool  where example = true
instance Inhabited Int   where example = 0
instance Inhabited Float where example = 0

some :: a -> Option a
some a = Option true a

none :: (Syntactic a, Inhabited (Internal a)) => Option a
none = Option false (fromFunC example)

option :: (Syntactic a, Syntactic b) => b -> (a -> b) -> Option a -> b
option noneCase someCase opt = ifC (isSome opt)
                                   (someCase (fromSome opt))
                                   noneCase

instance Functor Option where
    fmap f (Option b a) = Option b (f a)

instance Monad Option where
    return a  = some a
    opt >>= k = b { isSome = isSome opt ? (isSome b, false) }
      where b = k (fromSome opt)

instance Applicative Option
  where
    pure  = return
    (<*>) = ap

resistance :: FunC Float -> FunC Float -> Option (FunC Float)
resistance r1 r2 = do rp1 <- divF 1 r1
                      rp2 <- divF 1 r2
                      divF 1 (rp1 + rp2)

divF :: FunC Float -> FunC Float -> Option (FunC Float)
divF a b = b==0 ? (none, some $ div a b)
  where
    div = fromFunC $ Prim "(/)" (/)

-- Vectors

len :: FunC (Array Int a) -> FunC Int
len = fromFunC ArrLen

(<!>) :: Syntactic a => FunC (Array Int (Internal a)) -> FunC Int -> a
(<!>) = fromFunC ArrIx

data Vector a where
    Indexed :: FunC Int -> (FunC Int -> a) -> Vector a

instance Syntactic a => Syntactic (Vector a) where
    type Internal (Vector a) = Array Int (Internal a)
    toFunC (Indexed l ixf)   = fromFunC Arr l ixf
    fromFunC arr             = Indexed (len arr) (\ix -> arr <!> ix)

zipWithVec :: (Syntactic a, Syntactic b) =>
              (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWithVec f (Indexed l1 ixf1) (Indexed l2 ixf2)
  = Indexed (min l1 l2) (\ix -> f (ixf1 ix) (ixf2 ix))

sumVec :: (Syntactic a, Num a) => Vector a -> a
sumVec (Indexed l ixf) = forLoop l 0 (\ix s -> s + ixf ix)

instance Functor Vector where
    fmap f (Indexed l ixf) = Indexed l (f . ixf)

scalarProd :: (Syntactic a, Num a) => Vector a -> Vector a -> a
scalarProd a b = sumVec (zipWithVec (*) a b)

-- Rendering the AST

toTreeArgs :: FunC a -> [Tree String] -> State Int (Tree String)
toTreeArgs (f :$ a) as = do
    at <- toTreeArgs a []
    toTreeArgs f (at:as)
toTreeArgs (Lam f) as = do
    v <- get; put (v+1)
    let var = Variable ('v' : show v)
    body <- toTreeArgs (f var) []
    return $ case as of
        [] -> Node ("Lam v" Prelude.++ show v) [body]
        _  -> Node (":$") (body:as)
toTreeArgs (Variable v) as = return $ Node v as
toTreeArgs sym as = return $ Node (showSym sym) as
  where
    showSym :: FunC a -> String
    showSym (Lit a)     = show a
    showSym If          = "If"
    showSym While       = "While"
    showSym Pair        = "Pair"
    showSym Fst         = "Fst"
    showSym Snd         = "Snd"
    showSym (Prim f _)  = f
    showSym Arr         = "Arr"
    showSym ArrLen      = "ArrLen"
    showSym ArrIx       = "ArrIx"
    showSym Sequential  = "Sequential"
    showSym Return      = "Return"
    showSym Bind        = "Bind"
    showSym NewArray_   = "NewArray_"
    showSym GetArray    = "GetArray"
    showSym PutArray    = "PutArray"
    showSym LengthArray = "LengthArray"
    showSym FreezeArray = "FreezeArray"
    showSym ThawArray   = "ThawArray"
    showSym ForM        = "ForM"
    showSym WhileM      = "WhileM"
    showSym NewRef      = "NewRef"
    showSym ReadRef     = "ReadRef"
    showSym WriteRef    = "WriteRef"

drawAST :: Syntactic a => a -> IO ()
drawAST = drawTree . toTree . toFunC

toTree :: FunC a -> Tree String
toTree a = evalState (toTreeArgs a []) 0

-- Fusion

memorize  :: Syntactic a => Vector a -> Vector a
memorize (Indexed l ixf) = Indexed l (\n -> fromFunC Arr l ixf <!> n)

scalarProdMem :: (Syntactic a, Num a) => Vector a -> Vector a -> a
scalarProdMem a b = sumVec (memorize (zipWithVec (*) a b))

-- Sequential Vectors

scanVec :: Syntactic a => (a -> b -> a) -> a -> Vector b -> Vector a
scanVec f z (Indexed l ixf) = Indexed (l+1) ixf'
  where ixf' i = forLoop (i-1) z $ \j s ->
                   f s (ixf j)

data Seq a = forall s . Syntactic s => Seq s (s -> (a,s)) (FunC Int)

scanSeq :: Syntactic a => (a -> b -> a) -> a -> Seq b -> Seq a
scanSeq f z (Seq init step l) = Seq init' step' (l+1)
  where init' = (z,init)
        step' (a,s) = let (b,s') = step s
                      in (a,(f a b,s'))

vecToSeq :: Vector a -> Seq a
vecToSeq (Indexed l ixf) = Seq 0 step l
  where step i = (ixf i, i+1)

-- Monads

data Mon m a = M { unM :: forall b . ((a -> FunC (m b)) -> FunC (m b)) }

instance Monad m => Monad (Mon m) where
    return a  = M $ \k -> k a
    M m >>= f = M $ \k -> m (\a -> unM (f a) k)

instance Monad m => Functor (Mon m) where
    fmap f m = m >>= return . f

instance Monad m => Applicative (Mon m)
  where
    pure  = return
    (<*>) = ap

instance (Monad m, Syntactic a) => Syntactic (Mon m a) where
    type Internal (Mon m a) = m (Internal a)
    toFunC (M m) = m (fromFunC Return)
    fromFunC m   = M $ \k -> fromFunC Bind m k

type M a = Mon IO a
type MArr a = FunC (IOArray Int a)

newArray    :: FunC Int -> M (MArr a)
getArray    :: MArr a -> FunC Int -> M (FunC a)
putArray    :: MArr a -> FunC Int -> FunC a -> M ()
lengthArray :: MArr a -> M (FunC Int)
freezeArray :: MArr a -> M (FunC (Array Int a))
thawArray   :: FunC (Array Int a) -> M (MArr a)

newArray    =  fromFunC NewArray_
getArray    =  fromFunC GetArray
putArray    =  fromFunC PutArray
lengthArray =  fromFunC LengthArray
freezeArray =  fromFunC FreezeArray
thawArray   =  fromFunC ThawArray

forM :: Monad m => FunC Int -> FunC Int -> (FunC Int -> Mon m ()) -> Mon m ()
forM start stop body = fromFunC ForM (stop - start) (body . (+start))

whileM :: Monad m => Mon m (FunC Bool) -> Mon m () -> Mon m ()
whileM = fromFunC WhileM

insertionSort :: Ord a => FunC Int -> MArr a -> M ()
insertionSort l arr = do
  forM 1 l $ \i -> do
    value <- getArray arr i
    j <- newRef (i-1)
    let cond = do jv <- readRef j
                  aj <- getArray arr jv
                  return (jv >= 0 && aj > value)
    whileM cond $ do
      jv <- readRef j
      a <- getArray arr jv
      putArray arr (jv+1) a
      writeRef j (jv-1)
    jv <- readRef j
    putArray arr (jv+1) value

type Ref a = FunC (IORef a)

newRef :: FunC a -> M (Ref a)
newRef = fromFunC NewRef

readRef :: Ref a -> M (FunC a)
readRef = fromFunC ReadRef

writeRef :: Ref a -> FunC a -> M ()
writeRef = fromFunC WriteRef

-- Push vectors

data Push a = Push ((FunC Int -> a -> M ()) -> M ()) (FunC Int)

enum :: FunC Int -> FunC Int -> Push (FunC Int)
enum start stop = Push f (stop - start)
  where f w = forM start stop $ \i ->
                w i i

(++) :: Push a -> Push a -> Push a
Push f1 l1 ++ Push f2 l2 = Push f (l1 + l2)
  where f w = do f1 w
                 f2 (\i a -> w (i+l1) a)

dup :: Push a -> Push a
dup (Push f l) = Push g (2*l)
  where g w = f (\i a -> w i a >> w (i + l) a)

store :: Push (FunC a) -> M (FunC (Array Int a))
store (Push f l) = do
  arr <- newArray l
  f (putArray arr)
  freezeArray arr

-- Mutable data structures

data Buffer a = Buffer
    { indexBuf :: FunC Int -> M a
    , putBuf   :: a -> M ()
    }

initBuffer :: forall a . Syntactic a => Vector a -> M (Buffer a)
initBuffer vec = do
    buf <- thawArray (toFunC vec)
    l   <- lengthArray buf
    ir  <- newRef 0
    let get j = do
          i <- readRef ir
          fmap fromFunC $ getArray buf $ calcIndex l i j
        put a = do
          i <- readRef ir
          writeRef ir ((i+1) `mod` l)
          putArray buf i $ toFunC a
    return (Buffer get put)
  where
    calcIndex l i j = (l+i-j-1) `mod` l

fib :: FunC Int -> M (FunC Int)
fib n = do
  let twoOnes = Indexed 2 $ \_ -> 1    -- Initial buffer [1,1]
  buf <- initBuffer twoOnes
  forM 1 n $ \_ -> do
    a <- indexBuf buf 0
    b <- indexBuf buf 1
    putBuf buf (a+b)
  indexBuf buf 0


testFib = eval (toFunC fib) 10
fibList = 1 : 1 : zipWith (+) fibList (tail fibList)
