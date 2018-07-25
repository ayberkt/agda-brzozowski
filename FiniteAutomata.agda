module FiniteAutomata where

open import Data.List
open import Data.Product using (_×_; _,_)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import Subset using (Subset)
open import Level  using (suc)

record DFA {l} : Set (suc l) where
  field
    Q   : Set l
    Σ   : Set
    δ   : Q × Σ → Q
    q₀  : Q
    F   : Data.Product.Σ (Subset Q) (λ P → Decidable P)

record NFA {l} : Set (suc l) where
  field
    Q   : Set l
    Σ   : Set
    δ   : Q × Σ → Subset Q
    q₀  : Q
    F   : Data.Product.Σ (Subset Q) (λ P → Decidable P)

to-relation : ∀ {A B : Set} → (f : A → B) → (A → Subset B)
to-relation f a = λ x → x ≡ f a

to-nfa : DFA → NFA
to-nfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record { Q = Q ; Σ = Σ ; δ = to-relation δ ; q₀ = q₀ ; F = F }

-- NFA reversal.
flip-relation : ∀ {A B : Set} → (A × B → Subset A) → (A × B → Subset A)
flip-relation R (p , t) = λ x → (R (x , t)) p

rev : NFA → NFA
rev record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record { Q = Q ; Σ = Σ ; δ = flip-relation δ ; q₀ = q₀ ; F = F }

to-dfa : NFA → DFA
to-dfa record { Q = Q ; Σ = Σ ; δ = δ-orig ; q₀ = q₀ ; F = (F , F?) } =
  record
    {
      Q = Subset Q
    ; Σ = Σ
    ; δ = δ'
    ; q₀ = λ x → x ≡ q₀
    ; F = (λ x → {! !}) , {!!}
    }
    where
      δ' : Subset Q × Σ → Subset Q
      δ' (Q , t) = λ x → δ-orig (x , t) x
