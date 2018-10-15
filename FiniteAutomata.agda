module FiniteAutomata where

open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; fromℕ≤)
open import Data.Product using (_×_; _,_)
open import Data.Bool    using (Bool; true; false)
open import Data.Maybe   using (Maybe)

_≋_ : ∀ {n : ℕ} → Fin n → Fin n → Bool
zero ≋ zero = true
zero ≋ suc y = false
suc x ≋ zero = false
suc x ≋ suc y = x ≋ y

record DFA : Set where
  field
    states      : ℕ
    transitions : ℕ

  Q  = Fin states
  Σ  = Fin transitions

  field
    δ  : Q × Σ → Q
    q₀ : Q
    F  : Q → Bool

record NFA : Set where
  field
    |states| : ℕ
    |transitions| : ℕ

  Q = Fin |states|
  Σ = Fin |transitions|

  field
    δ  : Q × Σ → (Q → Bool)
    q₀ : Q
    F  : Q → Bool

to-nfa : DFA → NFA
to-nfa record { states = states ; transitions = transitions ; δ = δ ; q₀ = q₀ ; F = F } =
  record
    { |states| = states
    ; |transitions| = transitions
    ; δ = δ'
    ; q₀ = q₀
    ; F = F
    }
    where
      δ' : Fin states × Fin transitions → (Fin states → Bool)
      δ' (p , t) q = δ (p , t) ≋ q

to-dfa : NFA → DFA
to-dfa record { |states| = |states| ; |transitions| = |transitions| ; δ = δ ; q₀ = q₀ ; F = F } =
  record
    { states = {!!}
    ; transitions = |transitions|
    ; δ = {!!}
    ; q₀ = fromℕ≤{toℕ q₀}{|states| * |states|} lemma
    ; F = {!!} }
  where
    δ' : Fin |states| × Fin |transitions| → (Fin |states| → Bool)
    δ' (p , t) q = {!!}
    lemma : ℕ.suc (toℕ q₀) Data.Nat.≤ |states| * |states|
    lemma = {!!}
