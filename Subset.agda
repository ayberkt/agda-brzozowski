module Subset where

open import Level          using (suc)
open import Relation.Unary using (Pred)
open import Data.Product   using (_×_)

Subset : ∀ {l} → (A : Set l) → Set (suc l)
Subset {l} A = Pred A l

_≈_ : ∀ {ℓ} {a : Set ℓ} → Subset a → Subset a → Set ℓ
P ≈ Q = ∀ x → (P x → Q x) × (Q x → P x)
