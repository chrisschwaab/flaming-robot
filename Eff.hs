
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators, RankNTypes #-}
-- {-# OPTIONS_GHC
--       -Wall -fno-warn-orphans
--       -fno-warn-unused-matches          #-}

import Control.Applicative
import Control.Monad
-- import Control.Monad.Codensity
-- import Control.Monad.Reader
import qualified Control.Monad.State as MS
import Control.Monad.Writer
import Control.Monad.Coroutine

type family Res (e :: * -> *) :: *

type Handler e m = forall a t. e t -> (t -> Res e -> m a) -> Res e -> m a

data Elem :: k -> [k] -> * where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

data Env (m :: * -> *) :: [* -> *] -> * where
  Nil  :: Env m '[]
  Cons :: Handler e m -> Res e -> Env m es -> Env m (e ': es)

execEff :: Elem e es -> e a -> (a -> Env m es -> m t) -> Env m es -> m t
execEff Here      eff k (Cons handle res env) = handle eff (\v res' -> k v (Cons handle res' env)) res
execEff (There i) eff k (Cons handle res env) = execEff i eff (\v env' -> k v (Cons handle res env')) env

newtype Eff m es a = Eff { fromEff :: forall b. (a -> Env m es -> m b) -> Env m es -> m b }

instance Monad (Eff m es) where
  return a     = Eff $ \k -> k a
  Eff m >>= f  = Eff $ \k -> m (\a -> fromEff (f a) k)

new :: Handler e m -> Res e -> Eff m (e ': es) a -> Eff m es a
new handle r (Eff eff) = Eff $ \k env -> eff (\v (Cons handle _ env') -> k v env') (Cons handle r env)

mkEffectP :: Elem e es -> e a -> Eff m es a
mkEffectP p e = Eff $ execEff p e

runEff :: (a -> m a) -> Eff m es a -> Env m es -> m a
runEff ret (Eff f) env = f (\v env' -> ret v) env

runEffM :: Monad m => Eff m es a -> Env m es -> m a
runEffM = runEff return

runEffA :: Applicative m => Eff m es a -> Env m es -> m a
runEffA = runEff pure

runPure :: Eff Id es a -> Env Id es -> a
runPure e env = fromId $ runEff Id e env

-- Running
data Id a = Id { fromId :: a }

-- State
data State (s :: *) :: * -> * where
  Get :: State s s
  Put :: s -> State s ()

type instance Res (State s) = s

stateHandler :: Handler (State s) m
stateHandler Get       k st = k st st
stateHandler (Put st') k st = k () st'

stateHandler2 :: Handler (State s) (MS.State s)
stateHandler2 Get       k r = MS.get     >>= flip k r
stateHandler2 (Put st') k r = MS.put st' >>= flip k r

get :: Eff m '[State s] s
get = mkEffectP Here Get

put :: s -> Eff m '[State s] ()
put s = mkEffectP Here (Put s)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving Show

tag :: Tree a -> Eff m '[State Int] (Tree Int)
tag (Leaf)       = return Leaf
tag (Node _ l r) = do
                      l' <- tag l
                      n  <- get
                      put (n+1)
                      r' <- tag r
                      return (Node n l' r')

test :: Tree Bool
test = Node True (Node False Leaf Leaf) Leaf

runTest :: Tree Int
runTest = runPure (tag test) (Cons stateHandler 5 Nil)

runTest2 :: Tree Int
runTest2 = flip MS.evalState 4 $ runEffM (tag test) (Cons stateHandler2 5 Nil)


-- Non-deterministic choice
data Choice a :: * -> * where
  Choose :: Choice a a

type instance Res (Choice a) = ()

alwaysTrue :: Handler (Choice Bool) m
alwaysTrue Choose k r = k True r

allBool :: Handler (Choice Bool) []
allBool Choose k r = k True r ++ k False r

choose :: Eff m '[Choice a] a
choose = mkEffectP Here Choose

fruit :: Eff m '[Choice Bool] String
fruit = do
          a <- choose
          b <- choose
          let form  = if a then "raw" else "cooked"
              fruit = if b then "apple" else "banana"
          return (form ++ " " ++ fruit)


testFruit1 = runEffM fruit (Cons allBool () Nil)
testFruit2 = runPure fruit (Cons alwaysTrue () Nil)

-- I/O
data Channel :: * -> * where
  Read  :: Channel String
  Write :: String -> Channel ()

type instance Res Channel = ()

readChannel :: Eff m '[Channel] String
readChannel = mkEffectP Here Read

writeChannel :: String -> Eff m '[Channel] ()
writeChannel s = mkEffectP Here (Write s)

ioChannel :: Handler Channel IO
ioChannel Read      k r = getLine    >>= flip k r
ioChannel (Write s) k r = putStrLn s >>= flip k r

channelProg = do
  s <- readChannel
  writeChannel s
  writeChannel s

testIoChannel = runEffM channelProg (Cons ioChannel () Nil)

type L = MS.StateT [String] (Writer [String])

listChannel :: Handler Channel L
listChannel Read k r = do
                         (x:xs) <- MS.get
                         MS.put xs
                         k x r
listChannel (Write s) k r = tell [s] >>= flip k r

testListChannel = execWriter $
                  flip MS.evalStateT (repeat "hi") $
                  runEffM channelProg (Cons listChannel () Nil)

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

type List = []

map' :: (a -> Eff m es b) -> List a -> Eff m es (List b)
map' f []     = return []
map' f (a:as) = liftM2 (:) (f a) (map' f as)

data Free f a where
  Pure   :: a -> Free f a
  Impure :: f (Free f a) -> Free f a

instance Functor f => Monad (Free f) where
  return         = Pure
  Pure   a >>= f = f a
  Impure x >>= f = Impure (fmap (>>=f) x)
