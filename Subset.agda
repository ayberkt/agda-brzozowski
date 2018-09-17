module Subset where

open import Level          using (suc; _⊔_; zero; Level)
open import Relation.Unary using (Pred)
open import Data.Product   using (_×_)

Subset : ∀ {l} → (l′ : Level) → (A : Set l) → Set _
Subset {l} l′ A = Pred A l′
