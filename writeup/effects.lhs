\documentclass[preprint,cm,10pt]{sigplanconf}
%include polycode.fmt

\usepackage{amsmath}
\usepackage{amsmath}


\title{Algebraic Reasoning over Algebraic Effects}
\authorinfo{Steven Keuchel \and Tom Schrijvers}
           {University of Ghent}
           {\{steven.keuchel,tom.schrijvers\}@ugent.be}
\authorinfo{Christopher Schwaab}
           {}
           {christopher.schwaab@gmail.com}
\date{}

\bibliography{refs}
\bibliographystyle{plain}

\newcommand{ignore}{#1}{}

\begin{document}
\ignore{
\begin{code}
{-# LANGUAGE DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FlexibleInstances,
             PolyKinds, TypeFamilies, TypeOperators,
             RankNTypes, FlexibleContexts, DeriveFunctor,
             OverlappingInstances #-}

import qualified Data.Map  as M

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
Clearly calling $tick$, $n$ times is equivalent to adding $n$ to the current
state, but how can we formalize this?

\subsection{Reasoning about State}
The behavior of a stateful computation can be captured by five easy
laws~\cite{MRI} that all implementations of $\mathrm{StateM}$ satisfy.
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

\section{Algebraic Effects in Haskell}
\emph{TODO Introduce effects.}

Following Brady's \emph{Idris} implementation~\cite{brady} effects are
introduced as a DSL.  Effectful computations include in their signature
the list of effects required and an overall \emph{context} within which
to run---this could be for example a monad.  The framework exposes four
primary operations
\begin{itemize}
\item $return$ to lift values into computations;
\item $bind$ to bind a computation's result;
\item $mkEffectP$ to invoke an effect currently in scope, and;
\item $new$ to introduce a new effect to the current computation.
\end{itemize}
Additionally the DSL provides $liftP$ as a means for running
computations that require only a subset of the effects currently in scope.

Each effect manages a so called \emph{resource} which can simply be some state
carried through each invocation.  Additionally with the introduction of an effect
an associated \emph{handler} must be specified, providing the actual
implementation
of an effect's operations.

The effects implementation begins with the introduction of effectful computations
> newtype Eff m es r a = Eff {
>   fromEff ::
>     (a -> Env m es -> m r) -> Env m es -> m r }
Note that unlike Brady whose effects are evaluated by an interpreter, terms here
are written in direct continuation passing style and it will later be seen that
this simplifies the reasoning process.  Here an effectful computation is
contextualized by an environment: $Env \; m \; es$.  The purpose of the
environment is two-fold: it tracks the list of effects available to this
computation; and it associates a handler with each effect in scope.  Thus the
type of an environment should be expected to follow the shape of its value where
each handler introduced pushes an associated effect onto the effect list.

An environment can then be introduced as a list of handlers and their
associated resources, decorated by the computational context and a list of
effects in scope.
> data Env (m :: * -> *) :: [* -> *] -> * where
>   Nil  :: Env m '[]
>   Cons :: (forall a. Handler e m a) -> Res e -> Env m es -> Env m (e ': es)
Where the type of a handler is
> type Handler e m a = forall t. e t -> (t -> Res e -> m a) -> Res e -> m a
Thus a handler maps effects of type $e \; t$ given a continuation that takes a
result and an updated resource; and the current value of this effect's
associated resource.

This is all the machinery required to implement the effects language.

\subsection{Implementing the Effects Combinators}
Referring back to the signature for an effect, the reader may expect for
$Eff$ to form a monad.  Inspecting more closely, notice that $Eff$ is
simply the composition of the $Codensity$ and $Reader$ monad transformers
and thus trivially forms a monad itself.

Introducing the first two operations exposed by the effects language,
the definitions of $return$ and $bind$ can now be given as
> instance Monad (Eff m es r) where
>   return a     = Eff $ \k -> k a
>   Eff m >>= f  = Eff $ \k -> m (\a -> fromEff (f a) k)
Here $return$ simply yields its value to the rest of the computation.
To implement $bind$ the result of an effectful computation $m$ is passed
into $f$ and the the resulting computation is run.

Recall that the fixed set of operations exposed by an effect are invoked
by $mkEffectP$, meaning to execute an operation the computation is obliged
to prove the associated effect is in scope.  Such a proof can be given as an
object of the list membership type
> data Elem e es where
>   Here  :: Elem e (e ': es)
>   There :: Elem e es -> Elem e (e' ': es)
Respectively these cases can be taken to mean that either an element is a
member because it is found at the top of a list; or if an element is a member
of some list $es$ it is also a list of a superset of $es$.
Equipped with the above $mkEffectP$ can be given
> mkEffectP :: Elem e es -> e a -> Eff m es r a
> mkEffectP p e = Eff $ execEff p e
where $execEff$ simply looks up and excutes the handler associated with the
effect $e$ in the current environment.  By case analysis on $p$
> execEff :: Elem e es -> e a -> (a -> Env m es -> m t) -> Env m es -> m t
> execEff Here      eff k (Cons handle res env) =
>   handle eff (\v res' -> k v (Cons handle res' env)) res
> execEff (There i) eff k (Cons handle res env) =
>   execEff i eff (\v env' -> k v (Cons handle res env')) env

Given that to call an operation its effect must be in scope, a convenient
method of introducing new effects should be available.  This is the purpose
of $new$, which creates a new effect with its initial resource by wrapping
a computation by a handler for its associated operations
> new :: (forall a. Handler e m a) -> Res e -> Eff m (e ': es) r a -> Eff m es r a
> new handle r (Eff eff) = Eff $ \k env ->
>   eff (\v (Cons handle _ env') -> k v env') (Cons handle r env)
First the computation $eff$ is run in an environment extended with the new effect
type, following the newly introduced effect is dropped from the resulting
environment, and the return value is passed into the remaining continuation.

\subsection{Examples}
The above operations are enough to begin writing useful programs with effects.
As a simple example consider a stateful function to compute the $n$th
fibbonacci number, using a table to lookup previously computed values.
Note the regular monadic style enjoyed by effectful computations.
> sfibs :: Int -> Eff m '[State (M.Map Int Int)] r Int
> sfibs 0 = return 1
> sfibs 1 = return 1
> sfibs n = do
>   fibs <- get
>   case M.lookup n fibs of
>     Just c  -> return c
>     Nothing -> do a <- sfibs (n-1)
>                   b <- sfibs (n-2)
>                   get >>= put . M.insert n (a + b)
>                   return (a + b)
What does the implementation of an effect look like?

\subsection{Combining Effectful Computations}

\section{Reasoning about Effects}

\section{Conclusion}

\section{Future Work}

\section*{References}
%@INCLUDE_BIBLIOGRAPHY@

\end{document}
