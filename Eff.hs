
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators, RebindableSyntax #-}

import Prelude (Int, fromInteger, (+), undefined, Show(..), Bool(..))

type family Res (e :: * -> *) :: *

class Handler e m where
  handle :: Res e -> e t -> (Res e -> t -> m a) -> m a

data Elem :: k -> [k] -> * where
  Here  :: Elem x (x ': xs)
  There :: Elem x xs -> Elem x (y ': xs)

data EffM (m :: * -> *) :: [* -> *] -> * -> * where
  Return    :: a -> EffM m es a
  Bind      :: EffM m es a -> (a -> EffM m es b) -> EffM m es b
  New       :: (Handler e m) =>
               Res e -> EffM m (e ': es) a -> EffM m es a
  MkEffectP :: Elem e es -> e t -> EffM m es t

return :: a -> EffM m es a
return = Return

(>>=) = Bind
(>>) a f = a >>= \_ -> f

fail = undefined

-- Running
data Id a = Id { fromId :: a }

data Env (m :: * -> *) :: [* -> *] -> * where
  Nil  :: Env m '[]
  Cons :: Handler e m => Res e -> Env m es -> Env m (e ': es)

execEff :: Env m es -> Elem e es -> e a -> (Env m es -> a -> m t) -> m t
execEff (Cons res env) Here eff k = handle res eff (\res' v -> k (Cons res' env) v)
execEff (Cons res env) (There i) eff k = execEff env i eff (\env' -> k (Cons res env'))

effInt :: Env m es -> EffM m es a -> (Env m es -> a -> m b) -> m b
effInt env (Return a)      k = k env a
effInt env (Bind prog c)   k = effInt env prog (\env' a -> effInt env' (c a) k)
effInt env (New r prog)    k = effInt (Cons r env) prog (\(Cons _ env') -> k env')
effInt env (MkEffectP p e) k = execEff env p e k

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
get = MkEffectP Here Get

put :: s -> EffM m '[State s] ()
put s = MkEffectP Here (Put s)

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

{-
class Handler e m where
  handle :: res -> (e res res') -> (res' -> m a) -> m a

class EFFECT (e :: * -> * -> *) where
  type Res

data State :: * -> * -> * where
  Get :: State a a
  Put :: b -> State a b

instance Handler State m where
  handle st Get     k = k st
  handle st (Put n) k = k n


data EffM (m :: * -> *) :: [* -> * -> *] -> [* -> * -> *] -> * -> * where
  Return :: a -> EffM m es es a
  Bind   :: EffM m es es' a -> (a -> EffM m es' es'' b) -> EffM m es es'' b
  New    :: (EFFECT e, Handler e m) =>
            Res -> EffM m (e ': es) (e ': es') a -> EffM m es es' a

-}