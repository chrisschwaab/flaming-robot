
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators #-}

type family Res (e :: * -> *) :: *

class Handler e m where
  handle :: Res e -> e t -> (Res e -> t -> m a) -> m a

data Elem :: k -> [k] -> * where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

data EffM (m :: * -> *) :: [* -> *] -> * -> * where
  Return    :: a -> EffM m es a
  New       :: Handler e m => Res e -> EffM m (e ': es) a ->
               (a -> EffM m es b) -> EffM m es b
  MkEffectP :: Elem e es -> e a ->
               (a -> EffM m es b) -> EffM m es b

instance Monad (EffM m es) where
  return                  = Return
  Return a          >>= g = g a
  New r e f         >>= g = New r e (\a -> f a >>= g)
  MkEffectP p eff f >>= g = MkEffectP p eff (\a -> f a >>= g)

-- Running
data Id a = Id { fromId :: a }

data Env (m :: * -> *) :: [* -> *] -> * where
  Nil  :: Env m '[]
  Cons :: Handler e m => Res e -> Env m es -> Env m (e ': es)

execEff :: Env m es -> Elem e es -> e a -> (Env m es -> a -> m t) -> m t
execEff (Cons res env) Here eff k = handle res eff (\res' v -> k (Cons res' env) v)
execEff (Cons res env) (There i) eff k = execEff env i eff (\env' -> k (Cons res env'))

effInt :: Env m es -> EffM m es a -> (Env m es -> a -> m b) -> m b
effInt env (Return a)        k = k env a
effInt env (New r prog c)    k = effInt (Cons r env) prog
                                   (\(Cons _ env') v -> effInt env' (c v) k)
effInt env (MkEffectP p e c) k = execEff env p e (\env' v -> effInt env' (c v) k)

runPure :: Env Id es -> EffM Id es a -> a
runPure env prog = fromId (effInt env prog (\env' -> Id))

-- State
data State :: * -> * -> * where
  Get :: State a a
  Put :: a -> State a ()

type instance Res (State s) = s

instance Handler (State s) m where
  handle st Get       k = k st st
  handle st (Put st') k = k st' ()

get :: EffM m '[State s] s
get = MkEffectP Here Get Return

put :: s -> EffM m '[State s] ()
put s = MkEffectP Here (Put s) Return

data Tree a = Leaf | Node a (Tree a) (Tree a)
  deriving Show

tag :: Tree a -> EffM m '[State Int] (Tree Int)
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
runTest = runPure (Cons 5 Nil) (tag test)


data Free f a where
  Pure   :: a -> Free f a
  Impure :: f (Free f a) -> Free f a

instance Functor f => Monad (Free f) where
  return         = Pure
  Pure   a >>= f = f a
  Impure x >>= f = Impure (fmap (>>=f) x)
