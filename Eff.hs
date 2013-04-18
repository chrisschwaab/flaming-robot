
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators,
             RankNTypes, FlexibleContexts, DeriveFunctor,
             OverlappingInstances #-}
-- {-# OPTIONS_GHC
--       -Wall -fno-warn-orphans
--       -fno-warn-unused-matches          #-}

import Control.Applicative
import Control.Monad
-- import Control.Monad.Codensity
-- import Control.Monad.Reader
import qualified Control.Monad.State as MS
import Control.Monad.Error
import Control.Monad.Writer hiding (lift)
import Control.Monad.Coroutine

type family Res (e :: * -> *) :: *

type Handler e m a = forall t. e t -> (t -> Res e -> m a) -> Res e -> m a

data Elem :: k -> [k] -> * where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

data Env (m :: * -> *) :: [* -> *] -> * where
  Nil  :: Env m '[]
  Cons :: (forall a. Handler e m a) -> Res e -> Env m es -> Env m (e ': es)

data SubList :: [* -> *] -> [* -> *] -> * where
  SubNil  :: SubList '[] '[]
  SubKeep :: SubList es fs -> SubList (x ': es) (x ': fs)
  SubDrop :: SubList es fs -> SubList es (x ': fs)

class SubListC (es :: [* -> *]) (fs :: [* -> *]) where
  subList  :: SubList es fs
instance SubListC '[] '[] where
  subList = SubNil

--class SubListC' (es :: [* -> *]) (x :: * -> *) (fs :: [* -> *]) where
--  subList' :: SubList es (x ': fs)
--instance SubListC' es x fs => SubListC es (x ': fs) where
--  subList = subList'
--instance SubListC es fs => SubListC' (x ': es) x fs where
--  subList' = SubKeep subList
--instance SubListC es fs => SubListC' es x fs where
--  subList' = SubDrop subList

instance SubListC es fs => SubListC (x ': es) (x ': fs) where
  subList = SubKeep subList
instance SubListC es fs => SubListC es (x ': fs) where
  subList = SubDrop subList

dropEnv :: SubList es fs -> Env m fs -> Env m es
dropEnv SubNil      Nil            = Nil
dropEnv (SubKeep p) (Cons h r env) = Cons h r (dropEnv p env)
dropEnv (SubDrop p) (Cons h r env) = dropEnv p env

rebuildEnv :: SubList es fs -> Env m fs -> Env m es -> Env m fs
rebuildEnv SubNil      Nil             Nil             = Nil
rebuildEnv (SubKeep p) (Cons _ _ envf) (Cons h r enve) = Cons h r (rebuildEnv p envf enve)
rebuildEnv (SubDrop p) (Cons h r envf) enve            = Cons h r (rebuildEnv p envf enve)

execEff :: Elem e es -> e a -> (a -> Env m es -> m t) -> Env m es -> m t
execEff Here      eff k (Cons handle res env) = handle eff (\v res' -> k v (Cons handle res' env)) res
execEff (There i) eff k (Cons handle res env) = execEff i eff (\v env' -> k v (Cons handle res env')) env

newtype Eff m es r a = Eff { fromEff :: (a -> Env m es -> m r) -> Env m es -> m r }

instance Monad (Eff m es r) where
  return a     = Eff $ \k -> k a
  Eff m >>= f  = Eff $ \k -> m (\a -> fromEff (f a) k)

instance Functor (Eff m es r) where
  fmap f = (>>= return . f)

new :: (forall a. Handler e m a) -> Res e -> Eff m (e ': es) r a -> Eff m es r a
new handle r (Eff eff) = Eff $ \k env -> eff (\v (Cons handle _ env') -> k v env') (Cons handle r env)

mkEffectP :: Elem e es -> e a -> Eff m es r a
mkEffectP p e = Eff $ execEff p e

liftP :: SubList es fs -> Eff m es r a -> Eff m fs r a
liftP p (Eff f) = Eff $ \k envf ->
  f (\v enve' -> k v (rebuildEnv p envf enve')) (dropEnv p envf)

liftE :: SubListC es fs => Eff m es r a -> Eff m fs r a
liftE = liftP subList

runEff :: (a -> m r) -> Eff m es r a -> Env m es -> m r
runEff ret (Eff f) env = f (\v env' -> ret v) env

runEffM :: Monad m => Eff m es r r -> Env m es -> m r
runEffM = runEff return

runEffA :: Applicative m => Eff m es r r -> Env m es -> m r
runEffA = runEff pure

runPure :: Eff Id es r r -> Env Id es -> r
runPure e env = fromId $ runEff Id e env

-- Running
data Id a = Id { fromId :: a }

-- State
data State (s :: *) :: * -> * where
  Get :: State s s
  Put :: s -> State s ()

type instance Res (State s) = s

stateHandler :: Handler (State s) m r
stateHandler Get       k st = k st st
stateHandler (Put st') k st = k () st'

stateHandler2 :: Handler (State s) (MS.State s) r
stateHandler2 Get       k r = MS.get     >>= flip k r
stateHandler2 (Put st') k r = MS.put st' >>= flip k r

get :: Eff m '[State s] r s
get = mkEffectP Here Get

put :: s -> Eff m '[State s] r ()
put s = mkEffectP Here (Put s)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving (Show, Functor)

tag :: Tree a -> Eff m '[State Int] r (Tree Int)
tag (Leaf)       = return Leaf
tag (Node _ l r) = do
                      l' <- tag l
                      n  <- get
                      put (n+1)
                      r' <- tag r
                      return (Node n l' r')

testTree :: Tree Bool
testTree = Node True (Node False Leaf Leaf) Leaf

runTest :: Tree Int
runTest = runPure (tag testTree) (Cons stateHandler 5 Nil)

runTest2 :: Tree Int
runTest2 = flip MS.evalState 4 $ runEffM (tag testTree) (Cons stateHandler2 5 Nil)


-- Non-deterministic choice
data Choice a :: * -> * where
  Choose :: Choice a a

type instance Res (Choice a) = ()

alwaysTrue :: Handler (Choice Bool) m r
alwaysTrue Choose k r = k True r

allBool :: Handler (Choice Bool) [] r
allBool Choose k r = k True r ++ k False r

choose :: Eff m '[Choice a] r a
choose = mkEffectP Here Choose

fruit :: Eff m '[Choice Bool] r String
fruit = do
          a <- choose
          b <- choose
          let form  = if a then "raw" else "cooked"
              fruit = if b then "apple" else "banana"
          return (form ++ " " ++ fruit)

data (:::) t (e :: * -> *) :: * -> * where
  Apply :: e a -> (t ::: e) a

type instance Res (t ::: e) = Res e

name :: t -> e a -> (t ::: e) a
name _ r = Apply r

label :: t -> Env m (e ': es) -> Env m ((t ::: e) ': es)
label _ (Cons handle r env) = Cons (\(Apply e) -> handle e) r env

unlabel :: t -> Env m ((t ::: e) ': es) -> Env m (e ': es)
unlabel t (Cons handle r env) = Cons (\e -> handle (name t e)) r env

(-:) :: t -> Eff m '[e] r s -> Eff m '[t ::: e] r s
t -: (Eff eff) = Eff $ \k lenv ->
  eff (\v uenv' -> k v (label t uenv')) (unlabel t lenv)

data Tag = Tag
data Count = Count
tagCount :: Tree a -> Eff m '[Count ::: State Int, Tag ::: State Int] r (Tree (Int, a))
tagCount Leaf = do
                  n <- liftE (Count -: get)
                  liftP (SubKeep subList) (Count -: put (n+1))
                  return Leaf
tagCount (Node x l r) = do
                          l' <- tagCount l
                          lbl <- liftE (Tag -: get)
                          liftE (Tag -: put (lbl + 1))
                          r' <- tagCount r
                          return $ Node (lbl, x) l' r'

testFruit1 = runEffM fruit (Cons allBool () Nil)
testFruit2 = runPure fruit (Cons alwaysTrue () Nil)

-- I/O
data Channel :: * -> * where
  Read  :: Channel String
  Write :: String -> Channel ()

type instance Res Channel = ()

readChannel :: Eff m '[Channel] r String
readChannel = mkEffectP Here Read

writeChannel :: String -> Eff m '[Channel] r ()
writeChannel s = mkEffectP Here (Write s)

ioChannel :: Handler Channel IO r
ioChannel Read      k r = getLine    >>= flip k r
ioChannel (Write s) k r = putStrLn s >>= flip k r

channelProg = do
  s <- readChannel
  writeChannel s
  writeChannel s

testIoChannel = runEffM channelProg (Cons ioChannel () Nil)

type L = MS.StateT [String] (Writer [String])

listChannel :: Handler Channel L r
listChannel Read k r = do
                         (x:xs) <- MS.get
                         MS.put xs
                         k x r
listChannel (Write s) k r = tell [s] >>= flip k r

testListChannel = execWriter $
                  flip MS.evalStateT (repeat "hi") $
                  runEffM channelProg (Cons listChannel () Nil)

data Bot
botelim :: Bot -> a
botelim bot = undefined

-- Exceptions
data Exception e :: * -> * where
  Raise :: e -> Exception e Bot

type instance Res (Exception e) = ()

raise :: e -> Eff m '[Exception e] r a
raise e = fmap botelim $ mkEffectP Here (Raise e)

optionalize :: Handler (Exception e) Maybe r
optionalize (Raise e) k r = Nothing

exceptionProg :: Eff Maybe '[] r Bool
exceptionProg =
  new optionalize () $
    if 23 < 30
     then raise "True"
     else return False

testException :: Maybe Bool
testException = runEffM exceptionProg Nil

exceptionHandler :: MonadError e m => Handler (Exception e) m r
exceptionHandler (Raise e) k r = throwError e

exceptionProg2 :: MonadError String m => Eff m '[] r Bool
exceptionProg2 =
  new exceptionHandler () $
    if 23 < 30
     then raise "True"
     else return False

testException2 :: Either String Bool
testException2 = runEffM exceptionProg2 Nil

-- catch :: MonadError e m => Eff m es r r -> (e -> Eff m es r r) -> Eff m es r r
-- catch prog handler = Eff $ \k env ->
--   catchError (runEffM prog env) (\e -> runEffM (handler e) env)

--toHandler :: (e -> Eff m es r a) -> Handler (Exception e) m r

-- catch :: Eff m (Exception e ': es) r r -> (e -> Eff m es r r) -> Eff m es r r
-- catch prog handler =
--                  new (\(Raise e) k r -> handler e ) () prog
--   Eff $ \k env ->
--  catchError (runEffM prog env) (\e -> runEffM (handler e) env)


-- Cooperative multithreading

-- data Coop (m :: * -> *) (es :: [* -> *]) :: * -> * where
--   Yield :: Coop m es ()
--   Fork  :: Eff m es () -> Coop m es ()
--
-- type instance Res (Coop m es) = ()
--
-- type C m es = Coroutine Id (Eff m es)
--
-- roundRobin :: Handler (Coop m es) (MS.StateT [C m es ()] (C m es))
-- roundRobin Yield () () = undefined
--
--
-- -- k :: () -> [Eff m es ()] -> m a
-- -- t :: Eff m es ()
--
-- -- do
--                     --   (t:ts) <- get
--                     --   undefined


-- Multiple effects

tag' :: (a -> Eff m es r b) -> Tree a -> Eff m es r (Tree b)
tag' f (Leaf)       = return Leaf
tag' f (Node a l r) = do
                        l' <- tag' f l
                        b  <- f a
                        r' <- tag' f r
                        return (Node b l' r')

myF :: String -> Eff m '[State Int, Channel] r Int
myF s = do
             liftE (writeChannel s)
             i <- liftE get
             liftE (put (i + 1))
             return i

progChannelState :: Eff m '[Channel] r (Tree Int)
progChannelState = new stateHandler 5 $
         tag' myF (fmap show testTree)

testChannelState :: IO (Tree Int)
testChannelState = runEffM (new ioChannel () progChannelState) Nil

type List = []

map' :: (a -> Eff m es r b) -> List a -> Eff m es r (List b)
map' f []     = return []
map' f (a:as) = liftM2 (:) (f a) (map' f as)

data Free f a where
  Pure   :: a -> Free f a
  Impure :: f (Free f a) -> Free f a

instance Functor f => Monad (Free f) where
  return         = Pure
  Pure   a >>= f = f a
  Impure x >>= f = Impure (fmap (>>=f) x)
