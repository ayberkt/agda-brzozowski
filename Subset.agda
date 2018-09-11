module Subset where

open import Level          using (suc; _⊔_; zero)
open import Relation.Unary using (Pred)
open import Data.Product   using (_×_)

Subset : ∀ {l} → (A : Set l) → Set (l ⊔ suc zero)
Subset {l} A = Pred A zero

_≈_ : ∀ {ℓ} {a : Set ℓ} → Subset a → Subset a → Set ℓ
P ≈ Q = ∀ x → (P x → Q x) × (Q x → P x)
