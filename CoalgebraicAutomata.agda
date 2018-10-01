module CoalgebraicAutomata (A : Set) where

open import Data.Bool
open import Size
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Surjection using (Surjective)
open import Data.Product using (∃)

data List (i : Size) (A : Set) : Set where
  []  : List i A
  _∷_ : {j : Size< i} (x : A) (xs : List j A) → List i A

foldr : ∀ {i} {A B : Set} → (A → B → B) → B → List i A → B
foldr c n [] = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

map : ∀ {i A B} → (A → B) → List i A → List i B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

any : ∀ {i A} → (A → Bool) → List i A → Bool
any p xs = foldr _∨_ false (map p xs)

record Lang i : Set where
  coinductive
  field
    ν : Bool
    δ : ∀ {j : Size< i} → A → Lang j

record DA (S : Set) : Set where
  field
    q₀ : S
    ν  : S → Bool
    δ  : S → A → S

  -- A list of states is accepting if it contains at least one final state.
  νs : ∀ {i} (ss : List i S) → Bool
  νs ss = any ν ss

  -- We step to a new listo f states by pointwise applying the transition function.
  δs : ∀ {i} (ss : List i S) → A → List i S
  δs ss a = map (λ s → δ s a) ss

  -- x_w in Bonsangue et al's notation.
  δ* : ∀ {i} → S → List i A → S
  δ* x []        = x
  δ* x (t ∷ ts) = δ (δ* x ts) t

  r : ∀ {i} → List i A → S
  r w = δ* q₀ w

  o : ∀ {i} → S → (List i A → Bool)
  o x w = ν (δ* x w)

-- Note that "M is reachable" if all states are reachable
-- from the initial state.
reachable : ∀ {S : Set} → DA S → Set
reachable M = ∀ y → ∃ λ x → (DA.r M) x ≡ y

-- "M is observable" if different states recognize different languages i.e., if
-- they have different "observable behavior".
--
-- An observable automaton is minimal.
observable : ∀ {S : Set} → DA S → Set
observable M = ∀ {x₀ x₁} → (DA.o M) x₀ ≡ (DA.o M) x₀ → x₀ ≡ x₁

lang : ∀ {i} {S} (da : DA S) → S → Lang i
Lang.ν (lang da s)   = DA.ν da s
Lang.δ (lang da s) a = lang da (DA.δ da s a)
