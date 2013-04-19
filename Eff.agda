

module Eff where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Unit
open import Data.Vec hiding (_>>=_; [_])
open import Relation.Binary.PropositionalEquality hiding ([_])
import Level

Handler : (Set → Set) → Set → (Set → Set) → Set → Set₁
Handler E Res M R = {A : Set} → E A → (A -> Res -> M R) -> Res -> M R

record Effect : Set₂ where
  field
    ⌊_⌋      : Set → Set
    Res     : Set
    Laws    : (M : Set → Set) → ((R : Set) → Handler ⌊_⌋ Res M R) → Set₁

open Effect

record HANDLER (E : Effect) (M : Set → Set) : Set₁ where
  field
    handle : ∀ R → Handler ⌊ E ⌋ (Res E) M R
    laws   : Laws E M handle

open HANDLER

data Env (M : Set → Set) : List Effect → Set₂ where
  Nil  : Env M []
  Cons : {E : Effect} {ES : List Effect} (handler : HANDLER E M) -> Res E -> Env M ES -> Env M (E ∷ ES)

data Elem (e : Effect) : List Effect → Set₂ where
  Here  : {es : List Effect} → Elem e (e ∷ es)
  There : {e' : Effect} {es : List Effect} → Elem e es -> Elem e (e' ∷ es)

execEff : ∀ {e es m t a} → Elem e es -> ⌊ e ⌋  a -> (a -> Env m es -> m t) -> Env m es -> m t
execEff Here      f k (Cons handler res env) = handle handler _ f (\v res' -> k v (Cons handler res' env)) res
execEff (There i) f k (Cons handler res env) = execEff i f (\v env' -> k v (Cons handler res env')) env

data Eff (m : Set → Set) (es : List Effect) (r a : Set) : Set₂ where
  eff  : ((a -> Env m es -> m r) -> Env m es -> m r) → Eff m es r a

fromEff : ∀ {m es r a} → Eff m es r a → (a -> Env m es -> m r) -> Env m es -> m r
fromEff (eff f) = f

mkEffectP : ∀ {e es m r a} → Elem e es -> ⌊ e ⌋ a -> Eff m es r a
mkEffectP p e = eff (execEff p e)

return : ∀ {es m r a} → a → Eff m es r a
return a = eff (λ k env → k a env)

_>>=_ : ∀ {a b es m r} → Eff m es r a → (a → Eff m es r b) → Eff m es r b
eff x >>= f = eff (λ k env → x (λ a → fromEff (f a) k) env)

_>>_ : ∀ {a b es m r} → Eff m es r a → Eff m es r b → Eff m es r b
m >> n = m >>= λ _ → n

data State (S : Set) : Set → Set where
  Get : State S S
  Put : (s : S) → State S ⊤

record StateLaws (S : Set) (m : Set → Set) (handle : (a : Set) → Handler (State S) S m a) : Set₁ where
  field
    put-put : ∀ (r : Set) (s t : S) k →
                handle r (Put s) (λ _ → handle r (Put t) k) ≡ handle r (Put t) k
    put-get : ∀ (r : Set) (s : S) k →
                handle r (Put s) (λ _ → handle r Get k) ≡ handle r (Put s) (λ _ → k s)
    get-put : ∀ (r : Set) (s : S) k →
                handle r Get (λ v → handle r (Put v) k) ≡ k tt

STATE : Set → Effect
STATE S = record { ⌊_⌋ = State S; Res = S; Laws = StateLaws S }

get : ∀ {s m r} → Eff m [ STATE s ] r s
get = mkEffectP Here Get

put : ∀ {s m r} → s → Eff m [ STATE s ] r ⊤
put s = mkEffectP Here (Put s)

stateHandler : ∀ S m r → Handler (State S) S m r
stateHandler S m r Get     k s = k s s
stateHandler S m r (Put s) k _ = k tt s

stateHANDLER : ∀ S M → HANDLER (STATE S) M
stateHANDLER S M =
  record {
    handle = stateHandler S M;
    laws = record {
             put-put = λ r s t k → refl;
             put-get = λ r s k → refl;
             get-put = λ r s k → refl
    }
  }

tick : ∀ {m r} → Eff m [ STATE ℕ ] r ⊤
tick = get >>= λ s → put (suc s)

rep : ∀ {m es r a} → ℕ → Eff m es r a → Eff m es r ⊤
rep zero    f = return tt
rep (suc n) f = f >> rep n f

put-put : ∀ {S m r} (s t : S) → put {S} {m} {r} s >> put t ≡ put t
put-put {S} {m} {r} s t = cong eff (extensionality₁ (λ k → extensionality₂ (λ {(Cons handler res env) →
        {!StateLaws.put-put (laws handler) r s t!} }
   )))
  where open ≡-Reasoning
        postulate
          extensionality₁ : Extensionality _ _
          extensionality₂ : Extensionality _ _

-- postulate
--   put-put : ∀ {S m r} {s t : S} → put {S} {m} {r} s >> put t ≡ put t
--   get-put : ∀ {S m r} → get >>= put {S} {m} {r} ≡ return tt
--   put-get : ∀ {S m r} {s : S} → put {S} {m} {r} s >> get ≡ put s >> return s

--   associativity : ∀ {M ES R A B C} (ma : Eff M ES R A) f (g : B → Eff M ES R C) →
--                  ma >>= (λ x → f x >>= g) ≡ (ma >>= f) >>= g
--   left-unit : ∀ {M ES R A B} → (a : A) (f : A -> Eff M ES R B) →
--                   return {ES} {M} {R} a >>= f ≡ f a

-- tick-fusion : ∀ {m r} n → rep n (tick {m} {r}) ≡ get >>= (put ∘ _+_ n)
-- tick-fusion zero    = sym get-put
-- tick-fusion (suc n) =
--    begin
--      rep (suc n) tick
--    ≡⟨ refl ⟩
--      tick >> rep n tick
--    ≡⟨ cong₂ _>>_ refl (tick-fusion n) ⟩
--      tick >> (get >>= (put ∘ _+_ n))
--    ≡⟨ refl ⟩
--      (get >>= (λ s → put (suc s))) >> (get >>= (put ∘ _+_ n))
--    ≡⟨ refl ⟩
--      (get >>= (λ s → put (suc s))) >>= (λ _ → get >>= (put ∘ _+_ n))
--    ≡⟨ associativity (get >>= (λ s → put (suc s))) (λ _ → get) (λ z → put (n + z)) ⟩
--      ((get >>= (λ s → put (suc s))) >>= (λ _ → get)) >>= (put ∘ _+_ n)
--    ≡⟨ cong₂ _>>=_ (sym (associativity get (λ z → put (suc z)) (λ _ → get))) refl ⟩
--      (get >>= (λ z → put (suc z) >> get)) >>= (put ∘ _+_ n)
--    ≡⟨ cong₂ _>>=_ (cong₂ _>>=_ refl (extensionality (λ x → put-get))) refl ⟩
--      (get >>= (λ z → put (suc z) >> return (suc z))) >>= (put ∘ _+_ n)
--    ≡⟨ sym (associativity get (λ z → put (suc z) >>= (λ _ → return (suc z))) (λ z → put (n + z))) ⟩
--      get >>= (λ z → (put (suc z) >> return (suc z)) >>= (put ∘ _+_ n))
--    ≡⟨ cong₂ _>>=_ refl (extensionality λ z →
--         begin
--           (put (suc z) >> return (suc z)) >>= (put ∘ _+_ n)
--         ≡⟨ sym (associativity _ _ _) ⟩
--           put (suc z) >> (return (suc z) >>= (put ∘ _+_ n))
--         ≡⟨ cong₂ _>>_ refl (left-unit _ _) ⟩
--           put (suc z) >> put (n + suc z)
--         ≡⟨ put-put ⟩
--           put (n + suc z)
--         ≡⟨ cong put (m+1+n≡1+m+n n z) ⟩
--           (put (suc (n + z))
--         ∎))
--     ⟩
--      get >>= (put ∘ _+_ (suc n))
--    ∎
--   where open ≡-Reasoning
--         postulate
--           extensionality : Extensionality _ _
--         m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
--         m+1+n≡1+m+n zero    n = refl
--         m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

-- postulate
--   S : Set
--   s : S
--   t : S
--   m : Set → Set

-- test : m ⊤
-- test = {!fromEff (return tt)  k (Cons (λ x x₁ x₂ → handle x x₁ x₂) res Nil) !}
--   where postulate k      : (x : ⊤) (x₁ : Env m [ STATE S ]) → m _
--                   handle : ∀ {r} → Handler (STATE S) m r
--                   res    : Res (STATE S)



-- --  ∀ k →
-- --  handle (Put s) (λ _ → handle (Put t) k)
-- --  ≡ handle (Put t) k
-- --