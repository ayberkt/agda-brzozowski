module FiniteAutomata where

open import Data.List
open import Data.Product using (_×_; _,_)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Nullary using (yes; no)

open import Subset using (Subset)
open import Level  using (suc; Level)

record DFA {l : Level} : Set (suc l) where
  field
    Q   : Set l
    Σ   : Set
    δ   : Q × Σ → Q
    q₀  : Q
    F   : Subset Q
    F?  : Decidable F

record NFA {l : Level} : Set (suc l) where
  field
    Q   : Set l
    Σ   : Set
    δ   : Q × Σ → Subset Q
    q₀  : Q
    F   : Subset Q
    F?  : Decidable F

-- Takes a function f : A → B and returns a relation R(x, y) that is inhabited
-- iff f x ≡ y represented as a function A → ℙ(B).
to-relation : ∀ {A B : Set} → (f : A → B) → (A → Subset B)
to-relation f a = λ x → x ≡ f a

-- Inclusion for DFAs into NFAs simply by converting the function into a
-- relation.
to-nfa : DFA → NFA
to-nfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record { Q = Q ; Σ = Σ ; δ = to-relation δ ; q₀ = q₀ ; F = F ; F? = F? }

-- NFA reversal.
flip-relation : ∀ {A B : Set} → (A × B → Subset A) → (A × B → Subset A)
flip-relation {A} {B} R = R-inv
  where
    R-inv : A × B → Subset A
    R-inv (p , t) = λ q → (R (q , t)) p

-- Reverse transitions of a DFA by using `flip-relation` on its transition
-- relation.
rev : NFA → NFA
rev record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record { Q = Q ; Σ = Σ ; δ = flip-relation δ ; q₀ = q₀ ; F = F ; F? = F? }

to-dfa : ∀ {l : Level} → NFA {l} → DFA {suc l}
to-dfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record
    {
      Q = Subset Q       -- new set of states is the set of all subsets of Q.
    ; Σ = Σ              -- the alphabet is unchanged.
    ; δ = δ'             -- the new transition function defined in the where clause.
    ; q₀ = λ x → x ≡ q₀ -- the singleton set containing the start state.
    ; F = λ U → {!!}    -- F delineates sets that contain at least one final state.
    ; F? = {!!}          -- proof that F is a decidable subset.
    }
    where
      -- The new transition function.
      δ' : Subset Q × Σ → Subset Q
      δ' (Q , t) = λ x → δ (x , t) x
