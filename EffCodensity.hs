
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators, RankNTypes, ScopedTypeVariables #-}

import Control.Applicative
import Control.Monad
-- import Control.Monad.Cont
-- import Control.Monad.Codensity
import Control.Monad.Reader
import qualified Control.Monad.State as MS

type family Res (e :: * -> *) :: *

newtype Cod m a = Cod { fromCod :: forall b. (a -> m b) -> m b }

instance Monad (Cod m) where
  return a     =  Cod $ \k -> k a
  Cod f >>= g  =  Cod $ \k -> f (\a -> fromCod (g a) k)

type Handler e m = forall t. e t -> Cod (ReaderT (Res e) m) t

data Elem :: k -> [k] -> * where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

data Env (m :: * -> *) :: [* -> *] -> * where
  Nil  :: Env m '[]
  Cons :: Handler e m -> Res e -> Env m es -> Env m (e ': es)

liftCod :: (forall a. g a -> h a) -> (forall a. h a -> g a) -> Cod g a -> Cod h a
liftCod gh hg (Cod f) = Cod $ \k -> gh (f (\v -> hg (k v)))

lift' :: Monad m => Cod (ReaderT (Res e) m) t -> Cod (ReaderT (Env m (e ': es)) m) t
lift' (Cod f) =
  Cod $ \k -> do
                Cons handle res env <- ask
                withReaderT (\(Cons handle res env) -> res) $
                  f (\v -> withReaderT (\res' -> Cons handle res' env) (k v))


execEff :: Monad m => Elem e es -> e a -> Cod (ReaderT (Env m es) m) a
execEff Here      eff = Cod $ \k -> do
                          Cons handle res env <- ask
                          withReaderT (\(Cons handle res env) -> res) $
                            fromCod (handle eff) $
                              (\v -> withReaderT (\res' -> Cons handle res' env) $ k v)
execEff (There i) eff = Cod $ \k -> do
                          Cons handle res env <- ask
                          withReaderT (\(Cons handle res env) -> env) $
                            fromCod (execEff i eff)
                              (\v -> withReaderT (Cons handle res) $ k v)

type Eff m es = Cod (ReaderT (Env m es) m)

new :: Handler e m -> Res e -> Eff m (e ': es) a -> Eff m es a
new handle r eff = Cod $ \k -> withReaderT (\env -> Cons handle r env) $
                                 fromCod eff
                                   (\v -> withReaderT (\(Cons handle _ env') -> env') $ k v)

mkEffectP :: Monad m => Elem e es -> e a -> Eff m es a
mkEffectP p e = execEff p e

runEffM :: Monad m => Eff m es a -> Env m es -> m a
runEffM eff = runReaderT (fromCod eff return)

runPure :: Eff Id es a -> Env Id es -> a
runPure eff env = fromId (runEffM eff env)

-- Running
data Id a = Id { fromId :: a }

instance Monad Id where
  return     = Id
  Id a >>= f = f a

-- State
data State :: * -> * -> * where
  Get :: State a a
  Put :: a -> State a ()

type instance Res (State s) = s

stateHandler :: Monad m => Handler (State s) m
stateHandler Get       = Cod $ \k -> ask >>= k
stateHandler (Put st') = Cod $ \k -> withReaderT (const st') (k ())

stateHandler2 :: Handler (State s) (MS.State s)
stateHandler2 Get       = Cod $ \k -> MS.get     >>= k
stateHandler2 (Put st') = Cod $ \k -> MS.put st' >>= k


get :: Monad m => Eff m '[State s] s
get = mkEffectP Here Get

put :: Monad m => s -> Eff m '[State s] ()
put s = mkEffectP Here (Put s)

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving Show

tag :: Monad m => Tree a -> Eff m '[State Int] (Tree Int)
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
