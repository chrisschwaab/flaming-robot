====
DONE
====

### Brady's IDRIS Implementation

* ported to Haskell
  + removed resource state tracking
  + eliminated DSL abstract syntax tree
  + monad instance
  + state, choice, I/O, unsatisfactory exceptions handlers
  + automatic lifting of get/put with type classes
    rather than IDRIS's tactic


* partial Agda implementation
  + postulated state properties
  + tick fusion proof
  + proof of get/put, put/get and put/put laws for state handler

====
TODO
====

### Short Term

* port implementation back to IDRIS
* mechanize monad laws
* express and enforce laws on handlers
* look at the impact of lifting on laws
* check reasoning in literature (e.g., compare to Handlers in Action)
* write-up

### Longer Term
* what does the restriction to algebraic handlers buy us?
  in terms of modularity, reasoning, ... ?
* can we fix the handler implementation of a modular component
  and exploit it for reasoning?
* interaction laws for reasoning
* make Brady's catch more flexible
* expose monadic form ContT r (ReaderT e m)
* contrast with Eff and recover its features:
  + lack of effect typing
  + return/val + operations + finally
    (seems related to strategy trees)
  + layer the context m
  + reraise exceptions 
* write-up
  + choose semantics by reordering effects
