\documentclass[preprint,cm,10pt]{sigplanconf}

%include polycode.fmt
%include forall.fmt

%\usepackage{color}
%\input{solarized.theme}
%%include effects.fmt

\usepackage{amsmath}
\usepackage{xcolor}

\title{Algebraic Reasoning over Algebraic Effects}
\authorinfo{Christopher Schwaab}
           {}
           {christopher.schwaab@@gmail.com}
\authorinfo{Steven Keuchel \and Tom Schrijvers}
           {University of Ghent}
           {\{steven.keuchel,tom.schrijvers\}@@ugent.be}
\date{}

\bibliography{refs}
\bibliographystyle{plain}

\long\def\ignore#1{}

\newcommand{\tom}[1]{\textcolor{red}{[\textsc{Tom:}}#1\textcolor{red}{]}}

\begin{document}
\ignore{
\begin{code}
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators,
             RankNTypes, FlexibleContexts, DeriveFunctor,
             OverlappingInstances #-}

import qualified Data.Map as M
import Data.Map (Map)

import Control.Applicative
import Control.Monad
import Control.Monad.Coroutine
import Control.Monad.Error
import qualified Control.Monad.State as MS
import Control.Monad.Writer hiding (lift)
\end{code}
}

\maketitle

\begin{abstract}
\end{abstract}

\section{Introduction}
One of the great advantages of functional programming is the ease with
which programs can be algebraically manipulated; however this simple
purity can be at odds with actual software whose key ingredients
include side-effects.  Modern functional systems solve this problem by
structuring programs using monads to uniformly specify and encapsulate
effects---in this way a term's type specifies its possible behaviors.
Moreover this approach to writing effectful programs in a pure setting
has been shown to retain the simple, equational style of reasoning
enjoyed by its effect-free counterpart~\cite{reasoning about effects,
  just do it}.  Still, monads present difficulties such as how to
separately introduce and combine new behaviors.  In turn arguably the
most popular solution to this problem---using monad
\emph{transformers}---comes with yet another set of problems.

\emph{Algebraic effects}~\cite{algebraic effects} offer an alternative
approach to structuring programs using free monads in which the
explicit order of effects is no longer exposed.  Moving to a regular
method of structuring effects allows for a simple description of both
how to combine individual effects as well as how to invoke
computations requiring only a subset of the current effect set.

While algebraic effects offer an attractive simplicity, they are also
less expressive than the direct monadic approach because the
interaction between effects can have real semantic value.  As an
example, threading state through a non-deterministic computation is
not equivalent to performing a non-deterministic, stateful computation
admitting backtracking.  Moreover the free-syntax interpretive
approach to effect handling appears to complicate reasoning because
the handler can potentially change the meaning of an operation.
Despite the small loss in expressivity, effect handlers appear to
offer an approach to organizing computational behavior in a way that
is both flexible and modular that is worth exploration.

Despite the great success that can be attributed to monads Gibbons and
Hinze~\cite{just do it} point out that little work has been done on
formal reasoning about functional programs exhibiting effects.
Inspired by their elegant approach to axiomatic reasoning over monadic
computations we show the same principle naturally adapts to the
setting of algebraic effects.

In this paper we begin with a brief background to reasoning in the
presence of effects.  Following we adapt the algebraic effects DSL
given by Brady~\cite{brady} to a Haskell setting, detailing our
implementation. We end by showing that reasoning over programs with
algebraic effects is both simple and direct, without any loss in
modularity.  Although in the paper proofs are given by hand, to boost
confidence the example given has been mechanized in Agda.

\section{Background}
The idea behind Gibbons' and Hinze's approach to reasoning about
programs with effects is to consider operations only by their
algebraic laws.  This alone is enough to manipulate programs in useful
ways via term substitution---as an example when trying to show the
correctness of some optimization.  To exemplify the idea consider the
simple effect-polymorphic counter described in \emph{MRI (FIXME
  presumably we should refer to this?  And how should we do so, by the
  full title?)}
< tick :: StateM Int m => m ()
< tick = get >>= put . (+1)
Clearly calling $\mathit{tick}$, $n$ times is equivalent to adding $n$ to the
current state, but how can we formalize this?

\subsection{Reasoning about State}
The behavior of a stateful computation can be captured by five easy
laws~\cite{MRI} that all implementations of $\mathit{StateM}$ satisfy.
\begin{align*}
get \gg m &\equiv m \tag{GetQuery} \\
get \gg= \lambda s \rightarrow get \gg= f \; s &\equiv get \gg= \lambda s \rightarrow f \; s \; s \tag{GetGet} \\
put \; x \gg put \; y &\equiv put \; y \tag{PutPut} \\
put \; x \gg get &\equiv put \; x \gg return \; x \tag{PutGet} \\
get \gg= put &\equiv return \; () \tag{GetPut}
\end{align*}
In order these can be taken to mean that
\begin{enumerate}
\item reading the state alone has no effect on the rest of the program, \\
\item successive reads have no effect, reading state once is sufficient, \\
\item putting a new state overwrites previously written values, \\
\item reading a state just written is equivalent to returning the value that was
  written and, \\
\item rewriting the current state has no effect.
\end{enumerate}
These laws are enough to show
\begin{equation*}
rep \; n \; tick \equiv get \gg= put \circ (+n)
\end{equation*}
Where $rep$ is defined as
< rep 0 mx = return ()
< rep (n+1) mx = mx >>= rep n mx
Oliveira et. al.~\cite{mri} give a proof by induction on $n$, with the base case
\begin{align*}
&\quad rep \; 0 \; (get \gg= put \circ (+1)) \\
&\equiv \{- \text{unfold rep 0} -\} \\
&\quad return \; () \\
&\equiv \{- \text{GetPut law} -\} \\
&\quad get \gg= put \\
&\equiv \{- \text{id is neutral element of function composition} -\} \\
&\quad get \gg= put \circ id \\
&\equiv \{- \text{0 is netural element of addition} -\} \\
&\quad get \gg put \circ (+0)
\end{align*}
and the induction case
\begin{align*}
  ...
\end{align*}

%===============================================================================
\section{Algebraic Effects in Haskell}
% [✓] interface & types with example
% [ ] implementation without liftP
%     (point out that for an interpreter you might not get a monad which
%      is important for reasoning)
% [x] handler implementation
% [x] another effect handler
% [x] lifting with an added effect
% [x] handler implementation


%-------------------------------------------------------------------------------
\subsection{The User's Perspective}

Our approach to algebraic effects is based on Brady's implementation of
algebraic effects~\cite{brady} in \emph{Idris}.  We provide the user with a
\emph{monadic} DSL for writing effectful computations.  The type of an
effectful computation is |Eff m es r a|, where the four type parameters are as
follows:
\begin{itemize}
\item |a| is the type of the immediate (or intermediate) value produced by the computation,
\item |r| is the type of the eventual value produce by the overall computation, and
\item |es| is the type-level list of effects that can be used in the computation, and
\item |m| is the \emph{context} within which the overall computation is run.
\end{itemize}
% FIXME {e ': es => e : es}

Programming with the |Eff| DSL quite closely resembles the traditional approach
to programming with monadic effects.  Indeed, as |Eff m es r| is a monad, it is
equipped with |return| and |>>=| for injecting pure values in the computation
and sequentially composing computations.

< return     ::  a -> Eff m es r a
< (>>=)      ::  Eff m es r a -> (a -> Eff m es r b) 
<            ->  Eff m es r b

In addition, various effects |e| may provide their own primitive operations to
extend the DSL's capabilities. For instance, the |State| effect may offers primitives
|get| and |put|. This means that, apart from its type, the definition of the memoized 
fibonacci function |sfibs| looks no different than if it were written against
the |State| monad.
% FIXME {'[State (M.Map Int Int)] => [State (M.Map Int Int)]}
> sfibs :: Int -> Eff m [State (Map Int Int)] r Int
> sfibs n | n < 2     = return 1
> sfibs n | otherwise = do
>   fibs <- get
>   case M.lookup n fibs of
>     Just c  -> return c
>     Nothing -> do
>       a <- sfibs (n-1)
>       b <- sfibs (n-2)
>       get >>= put . M.insert n (a + b)
>       return (a + b)
By declaring the |State| effect in its list of effects, |sfibs| is free to call
any of |State|'s associated operations in the same way they would
be called in the monadic |State| setting.  

\tom{This would be a good place to show how a user can run an effectful computation.
     Only provide signatures and show a top-level expression with result.}

If additional effects are required such as IO, they must simply be included in
the effects list. For instance, this variant of |sfibs| prints a message
whenever a new value in the sequence has been computed.
% FIXME {'[Channel, State (M.Map Int Int)] => [Channel, State (M.Map Int Int)]}
> noisySFibs :: Int
>            -> Eff m [Channel, State (M.Map Int Int)] r Int
> noisySFibs n | n < 2 = return 1
> noisySFibs n | otherwise = do
>   writeChannel (show n)
>   fibs <- get
>   a <- case M.lookup (n-1) fibs of
>          Just a  -> return a
>          Nothing -> noisySFibs (n-1)
>   fibs <- get
>   b <- case M.lookup (n-2) fibs of
>          Just b  -> return b
>          Nothing -> noisySFibs (n-2)
>   get >>= put . M.insert n (a + b)
>   return (a + b)

To do so, it declares the |Channel| effect in addition to the |State| effect,
and invokes the |Channel| operation |writeChannel|.

\tom{We need to find a good spot for these. This subsection is too early to introduce |mkEffectP|.}
In addition to those two operations, it provides two more primitive operations.
The function |mkEffectP| invokes an effect |e| computation |e a| into the current computation
effect currently in scope, and |new| introduces a new effect in a computation.

\begin{itemize}
\item
|mkEffectP| invokes an
effect currently in scope.

< mkEffectP  :: Elem e es -> e a -> Eff m es r a

\item  |new| introduces a new effect in a computation.

< new        :: (forall a. Handler e m a) -> Res e
<            -> Eff m (e : es) r a -> Eff m es r a

\end{itemize}

% Notice that effectful computations of type |a| returning a value of type |r|
% additionally specify in their signature |Eff m es r a| an overall
% \emph{context} |m| within which to run------and the list of effects required |es|.


%-------------------------------------------------------------------------------
\subsection{Implementing Effects}
The implementation of effects begins with the type of effectful computations
> newtype Eff m es r a = Eff {
>   fromEff ::
>     (a -> Env m es -> m r) -> Env m es -> m r }
Note that unlike Brady whose effects are evaluated by an interpreter, terms here
are written in direct continuation passing style.  

and it will later be seen that
this simplifies the reasoning process.

Here an effectful computation is
contextualized by an environment: |Env m es|.  The purpose of the
environment is two-fold: it tracks the list of effects available to this
computation; and it associates a handler with each effect in scope.  Thus the
type of an environment should be expected to follow the shape of its value where
each handler introduced pushes an associated effect onto the effect list.
%Each effect manages a so called \emph{resource} which can simply be some state
%carried through each invocation.  Additionally with the introduction of an effect
%an associated \emph{handler} must be specified, providing the actual
%implementation of an effect's operations.

An environment can then be introduced as a list of handlers and their
associated resources, decorated by the computational context and a list of
effects in scope.
% FIXME {'[] => []} {e ': es => e : es}
> data Env (m :: * -> *) :: [* -> *] -> * where
>   Nil  :: Env m []
>   Cons :: (forall a. Handler e m a) -> Res e
>     -> Env m es -> Env m (e : es)
Where the type of a handler is
> type Handler e m a =
>   forall t. e t -> (t -> Res e -> m a) -> Res e -> m a
Thus a handler maps effects of type $e \; t$ given a continuation that takes a
result and an updated resource; and the current value of this effect's
associated resource.

This is all the machinery required to implement the effects language.

\subsection{Implementing the Effects Combinators}
Referring back to the signature for an effect, the reader may expect for |Eff|
to form a monad.  Inspecting more closely, notice that |Eff| is simply the
composition of the |Codensity| and |Reader| monad transformers and thus
trivially forms a monad itself.

Introducing the first two operations exposed by the effects language, the
definitions of |return| and |>>=| can now be given as
> instance Monad (Eff m es r) where
>   return a     = Eff $ \k -> k a
>   Eff m >>= f  = Eff $ \k ->
>     m (\a -> fromEff (f a) k)
Here |return| simply yields its value to the rest of the computation. To
implement |>>=| the result of an effectful computation |m| is passed into |f|
and the the resulting computation is run.

Recall that the fixed set of operations exposed by an effect are invoked
by |mkEffectP|, meaning to execute an operation the computation is obliged
to prove the associated effect is in scope.  Such a proof can be given as an
object of the list membership type
% FIXME {e ': es => e : es} {e' ': es => e' : es}
> data Elem e es where
>   Here  :: Elem e (e : es)
>   There :: Elem e es -> Elem e (e' : es)
Respectively these cases can be taken to mean that either an element is a
member because it is found at the top of a list; or if an element is a member
of some list |es| it is also a list of a superset of |es|. Equipped with the
above |mkEffectP| can be given
> mkEffectP :: Elem e es -> e a -> Eff m es r a
> mkEffectP p e = Eff $ execEff p e
where |execEff| simply looks up and excutes the handler associated with the
effect |e| in the current environment.  By case analysis on |p|
> execEff :: Elem e es -> e a
>         -> (a -> Env m es -> m t) -> Env m es -> m t
> execEff Here      eff k (Cons handle res env) =
>   handle eff (\v res' -> k v (Cons handle res' env)) res
> execEff (There i) eff k (Cons handle res env) =
>   execEff i eff
>           (\v env' -> k v (Cons handle res env')) env

Given that to call an operation its effect must be in scope, a convenient method
of introducing new effects should be available.  This is the purpose of |new|,
which creates a new effect with its initial resource by wrapping a computation
by a handler for its associated operations
% FIXME {e ': es => e : es}
> new :: (forall a. Handler e m a) -> Res e
>     -> Eff m (e : es) r a -> Eff m es r a
> new handle r (Eff eff) = Eff $ \k env ->
>   eff (\v (Cons handle _ env') -> k v env')
>       (Cons handle r env)
First the computation |eff| is run in an environment extended with the new
effect type, following the newly introduced effect is dropped from the resulting
environment, and the return value is passed into the remaining continuation.

\subsection{Examples}

\subsection{Combining Effectful Computations}

\section{Reasoning about Effects}

\section{Conclusion}

\section{Future Work}

\section*{References}
%@INCLUDE_BIBLIOGRAPHY@

\end{document}
