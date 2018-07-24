module FiniteAutomata where

open import Data.Fin
open import Data.Bool
open import Data.List
open import Function using (_∘_)
open import Data.Product using (_×_; _,_)
open import Universe
open import Relation.Binary.PropositionalEquality

record DFA : Set₂ where
  field
    Q   : Set
    eqQ : Q → Q → Bool
    Σ   : Set
    δ   : Q × Σ → Q
    q₀  : Q
    F   : Q → Bool

data relation {A B : Set} (f : A → B) : A → B → Set₁ where
  pair : ∀ {a : A} {b : B} → f a ≡ b → relation f a b

record NFA : Set₂ where
  field
    Q  : Set
    eqQ : Q → Q → Bool
    Σ  : Set
    δ  : Q × Σ → Q → Bool
    q₀ : Q
    F  : Q → Bool

toRelation : ∀ {A B : Set} → (eqB : B → B → Bool) → (f : A → B) → (A → B → Bool)
toRelation eqB f = λ a b → eqB (f a) b

construct-nfa-from-dfa : DFA → NFA
construct-nfa-from-dfa record { Q = Q ; eqQ = eqQ ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record { Q = Q ; eqQ = eqQ ; Σ = Σ ; δ = toRelation eqQ δ ; q₀ = q₀ ; F = F }

data pset (A : Set)  : Set where
  pset-construct : ∀ {χ : A → Bool} → (a : A) → (χ a ≡ Bool.true) → pset A

construct-dfa-from-nfa : NFA → DFA
construct-dfa-from-nfa record { Q = Q ; eqQ = eqQ ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record { Q = pset Q ; eqQ = eqQpset ; Σ = Σ ; δ = δpset ; q₀ = {!!} ; F = {!!} }
    where
      eqQpset : pset Q → pset Q → Bool
      eqQpset (pset-construct a p) (pset-construct b q) = eqQ a b
      δpset : pset Q × Σ → pset Q
      δpset (pset-construct a x , t) = {! !}

flip-relation : ∀ {A B : Set} → (A × B → A → Bool) → (A × B → A → Bool)
flip-relation R (p , t) q = R (q , t) p

flip-dfa : DFA → NFA
flip-dfa d with construct-nfa-from-dfa d 
flip-dfa d | record { Q = Q ; eqQ = eqQ ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
               record { Q = Q ; eqQ = eqQ ; Σ = Σ ; δ = flip-relation δ ; q₀ = q₀ ; F = F }

accepts-h : (M : DFA) → List (DFA.Σ M) → (DFA.Q M) → Bool
accepts-h M []       state = (DFA.F M) state
accepts-h M (c ∷ cs) state = accepts-h M cs ((DFA.δ M) (state , c)) 

_accepts_ : (M : DFA) → List (DFA.Σ M) → Bool
M accepts input = accepts-h M input (DFA.q₀ M)

data alphabet : Set where
  a b : alphabet

foo : Fin 3 × alphabet → Fin 3
foo (zero , a) = suc zero
foo (suc st , a) = zero
foo (zero , b) = suc zero
foo (suc st , b) = suc zero

is-accepting : Fin 3 → Bool
is-accepting zero    = false
is-accepting (suc x) = true

sample-dfa : DFA
sample-dfa =
  record { Q = Fin 3 ; eqQ = eqQ ; Σ = alphabet ; δ = foo ; q₀ = zero ; F = is-accepting }
    where
      eqQ : Fin 3 → Fin 3 → Bool
      eqQ x y with compare x y
      eqQ x y | equal _ = Bool.true
      eqQ x y | _       = Bool.false
