{-# LANGUAGE MultiParamTypeClasses, GADTs, KindSignatures, TypeFamilies,
             FlexibleInstances, FlexibleContexts,
             OverlappingInstances, UndecidableInstances #-}
module EffInterp where
import qualified Data.Map as M
import Control.Monad.Identity

-- class Res e res | e -> res    
type family Res (e :: * -> *)

class Handler e m where
  handle :: e t -> (Res e -> t -> m a) -> Res e -> m a

data Pair (e :: * -> *) es where
data Any e es where
  Here :: Any e (Pair e es)
  There :: Any e es -> Any e (Pair e' es)

data Env (m :: * -> *) es where
  Cons :: Res e -> Env m es -> Env m (Pair e es)
  Nil :: Env m ()

data Subset es fs where
  SubNil :: Subset () ()
  Keep :: Subset es fs -> Subset (Pair e es) (Pair e fs)
  Drop :: Subset es fs -> Subset es (Pair e fs)

data EffM (m :: * -> *) es a where
  Return :: a -> EffM m es a
  Bind :: EffM m es a -> (a -> EffM m es b) -> EffM m es b
  MkEffectP :: Handler e m => Any e es -> e a -> EffM m es a
  New :: Res e -> EffM m (Pair e es) a -> EffM m es a
  LiftP :: Subset es fs -> EffM m es a -> EffM m fs a

dropEnv :: Subset es fs -> Env m fs -> Env m es
dropEnv SubNil         Nil           = Nil
dropEnv (Keep esSubFs) (e `Cons` es) = e `Cons` dropEnv esSubFs es
dropEnv (Drop esSubFs) (e `Cons` es) = dropEnv esSubFs es

rebuildEnv :: Subset es fs -> Env m fs -> Env m es -> Env m fs
rebuildEnv SubNil         Nil           Nil           = Nil
rebuildEnv (Keep esSubFs) (e `Cons` es) (_ `Cons` fs) =
  e `Cons` rebuildEnv esSubFs es fs
rebuildEnv (Drop esSubFs) (e `Cons` es) fs            =
  e `Cons` rebuildEnv esSubFs es fs

effInt :: Env m es -> EffM m es a -> (Env m es -> a -> m b) -> m b
effInt env (Return x) k = k env x
effInt env (Bind f c) k = effInt env f (\env' p' -> effInt env' (c p') k)
effInt env (MkEffectP eInEs effP) k = execEff env eInEs effP k
effInt env (New res prog) k = effInt (res `Cons` env) prog
                                (\(_ `Cons` env'') v -> k env'' v)
effInt env (LiftP p prog) k = effInt (dropEnv p env) prog
                                (\env' v' -> k (rebuildEnv p env env') v')

execEff :: Handler e m
        => Env m es -> Any e es -> e a -> (Env m es -> a -> m t) -> m t
execEff (res `Cons` env) Here eff k = 
  handle eff (\res' v -> k (res' `Cons` env) v) res
execEff (res `Cons` env) (There p) eff k =
  execEff env p eff (\env' v -> k (res `Cons` env') v)

data State s a where
  Get :: State s s
  Put :: s' -> State s' ()
type instance Res (State s) = s
instance Handler (State s) m where
  handle Get      k s = k s s
  handle (Put s') k s = k s' ()

data Channel s a where
  Write :: s -> Channel s ()
  Read :: Channel s s
type instance Res (Channel s) = ()
instance (Read s, Show s) => Handler (Channel s) IO where
  handle (Write s) k () = putStrLn (show s) >> k () ()
  handle Read      k () = k () . read =<< getLine

noisySFibs :: Int -> EffM IO (Pair (Channel String)
                               (Pair (State (M.Map Int Int)) ())) Int
noisySFibs 0 = Return 1
noisySFibs 1 = Return 1
noisySFibs n =
  Bind (MkEffectP Here . Write $ "Computing fib[" ++ show n ++ "]") $ \() ->
  Bind (MkEffectP (There Here) Get) $ \fibs ->
  Bind (case M.lookup (n-1) fibs of
          Just a  -> Return a
          Nothing -> noisySFibs (n-1)) $ \a ->
  Bind (MkEffectP (There Here) Get) $ \fibs ->
  Bind (case M.lookup (n-2) fibs of
          Just b  -> Return b
          Nothing -> noisySFibs (n-2)) $ \b ->
  Bind (MkEffectP (There Here) Get) $ \fibs ->
  Bind (MkEffectP (There Here) $ Put (M.insert n (a + b) fibs)) $ \() ->
  Return (a + b)

runEff :: Env m es -> (a -> m b) -> EffM m es a -> m b
runEff env ret prog = effInt env prog (\env a -> ret a)

runEffM :: Monad m => Env m es -> EffM m es a -> m a
runEffM env prog = runEff env return prog

runPure :: Env Identity es -> EffM Identity es a -> a
runPure env prog = runIdentity (runEffM env prog)

testNoisySFibs :: Int -> IO Int
testNoisySFibs n = runEffM Nil $
  New M.empty $
  New () $
    noisySFibs n

writeChannel :: Handler (Channel s) m => s -> EffM m (Pair (Channel s) ()) ()
writeChannel = MkEffectP Here . Write

get :: Handler (State s) m => EffM m (Pair (State s) ()) s
get = MkEffectP Here Get
put :: Handler (State s) m => s -> EffM m (Pair (State s) ()) ()
put = MkEffectP Here . Put

noisySFibs' :: Int -> EffM IO (Pair (Channel String)
                                 (Pair (State (M.Map Int Int)) ())) Int
noisySFibs' 0 = Return 1
noisySFibs' 1 = Return 1
noisySFibs' n =
  Bind (LiftP chanSubP . writeChannel $ "Computing fib[" ++ show n ++ "]") $ \() ->
  Bind (LiftP stateSubP get) $ \fibs ->
  Bind (case M.lookup (n-1) fibs of
          Just a  -> Return a
          Nothing -> noisySFibs' (n-1)) $ \a ->
  Bind (LiftP stateSubP get) $ \fibs ->
  Bind (case M.lookup (n-2) fibs of
          Just b  -> Return b
          Nothing -> noisySFibs' (n-2)) $ \b ->
  Bind (LiftP stateSubP get) $ \fibs ->
  Bind (LiftP stateSubP . put $ M.insert n (a + b) fibs) $ \() ->
  Return (a + b)
  where chanSubP :: Subset (Pair (Channel String) ())
                           (Pair (Channel String)
                             (Pair (State (M.Map Int Int)) ()))
        chanSubP = Keep (Drop SubNil)
        stateSubP :: Subset (Pair (State (M.Map Int Int)) ())
                            (Pair (Channel String)
                              (Pair (State (M.Map Int Int)) ()))
        stateSubP = Drop (Keep SubNil)

testNoisySFibs' :: Int -> IO Int
testNoisySFibs' n = runEffM Nil $
  New M.empty $
  New () $
    noisySFibs n

class    IsSub' q es  fs where isSub' :: q -> Subset es fs
instance IsSub' q () ()  where isSub' _ = SubNil
instance (e ~ e', IsSub' () es fs) => IsSub' () (Pair e es) (Pair e' fs) where
  isSub' () = Keep (isSub' ())
instance IsSub' () es fs => IsSub' q es (Pair e' fs) where
  isSub' _ = Drop (isSub' ())

class IsSub' () es fs => IsSub es fs where isSub :: Subset es fs
instance IsSub' () es fs => IsSub es fs where isSub = isSub' ()

writeChannel':: (Handler (Channel a) m, IsSub (Pair (Channel a) ()) fs)
             => a -> EffM m fs ()
writeChannel' = LiftP isSub . writeChannel
get' :: (Handler (State s) m, IsSub (Pair (State s) ()) fs) => EffM m fs s
get' = LiftP isSub get
put' :: (Handler (State s) m, IsSub (Pair (State s) ()) fs) => s -> EffM m fs ()
put' = LiftP isSub . put

--noisySFibs'' :: Int -> EffM IO (Pair (Channel String) (Pair (State (M.Map Int Int)) ())) Int
--noisySFibs'' 0 = Return 1
--noisySFibs'' 1 = Return 1
--noisySFibs'' n =
--  Bind (writeChannel' $ "Computing fib[" ++ show n ++ "]") $ \() ->
--  Bind (LiftP isSub get) $ \fibs ->
--Bind (case M.lookup (n-1) fibs of
--        Just a  -> Return a
--        Nothing -> noisySFibs' (n-1)) $ \a ->
--Bind (LiftP stateSubP get) $ \fibs ->
--Bind (case M.lookup (n-2) fibs of
--        Just b  -> Return b
--        Nothing -> noisySFibs' (n-2)) $ \b ->
--Bind get' $ \fibs ->
--Bind (put' $ M.insert n (a + b) fibs) $ \() ->
--Return (a + b)
--  undefined