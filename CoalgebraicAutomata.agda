module CoalgebraicAutomata (A : Set) where

open import Data.Bool using (true; false; _∨_; not) renaming (Bool to 𝟚)
open import Size
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃; _×_; _,_; uncurry; Σ-syntax; ∃-syntax)
open import Data.Unit    using (⊤; tt)

𝟙 : Set
𝟙 = ⊤

data List (i : Size) (A : Set) : Set where
  []  : List i A
  _∷_ : {j : Size< i} (x : A) (xs : List j A) → List i A

foldr : ∀ {i} {A B : Set} → (A → B → B) → B → List i A → B
foldr c n [] = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

snoc : ∀ {i} {j : Size< i} {A : Set} → (x : A) → List j A → List i A
snoc {i} {A} x' [] = x' ∷ []
snoc x' (x ∷ xs)   = x ∷ (snoc x xs)

rev : ∀ {i} {A : Set} → List i A → List i A
rev [] = []
rev (x ∷ xs) = snoc x (rev xs)

map : ∀ {i A B} → (A → B) → List i A → List i B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

any : ∀ {i A} → (A → 𝟚) → List i A → 𝟚
any p xs = foldr _∨_ false (map p xs)

record Lang i : Set where
  coinductive
  field
    ν : 𝟚
    δ : ∀ {j : Size< i} → A → Lang j

_∋_ : ∀ {i} → Lang i → List i A → 𝟚
l ∋ [] = Lang.ν l
l ∋ (a ∷ as) = Lang.δ l a ∋ as

record DA (S : Set) : Set where
  field
    q₀ : S
    ν  : S → 𝟚
    δ  : S → A → S

  -- A list of states is accepting if it contains at least one final state.
  νs : ∀ {i} → List i S → 𝟚
  νs as = any ν as

  -- We step to a new listo f states by pointwise applying the transition function.
  δs : ∀ {i} → List i S → A → List i S
  δs as a = map (λ s → δ s a) as

  -- x_w in Bonsangue et al's notation.
  δ* : ∀ {i} → S → List i A → S
  δ* x []        = x
  δ* x (t ∷ ts) = δ (δ* x ts) t

  r : ∀ {i} → List i A → S
  r w = δ* q₀ w

  o : ∀ {i} → S → Lang i
  Lang.ν (o s)   = ν s
  Lang.δ (o s) a = o (δ s a)
  -- o x w = ν (δ* x w)

-- Note that "M is reachable" if all states are reachable
-- from the initial state.
reachable : ∀ {S : Set} → DA S → Set
reachable M = ∀ s → ∃[ as ](DA.r M as ≡ s)

-- "M is observable" if different states recognize different languages i.e., if
-- they have different "observable behavior".
--
-- By asserting the injectivity of (DA.o M), we are really saying that "there are
-- no two distinct states such that after applying all transitions in w, the output
-- behavior of the resulting state is the same". This captures exactly minimality.
--
-- An observable automaton is minimal.
observable : ∀ {S : Set} → DA S → Set
observable M = ∀ s₀ s₁ → DA.o M s₀ ≡ DA.o M s₁ → DA.ν M s₀ ≡ DA.ν M s₁

𝟚^[_] : ∀ {V W : Set} → (f : V → W) → (W → 𝟚) → (V → 𝟚)
𝟚^[ f ] g = λ v → g (f v)

2^1=2 : ∀ {A : Set} → (A → 𝟙 → 𝟚) → (A → 𝟚)
2^1=2 f = λ x → f x tt

-- The main construction.
main : ∀ {S : Set} → (t : S → A → S) → ((S → 𝟚) → (A → S → 𝟚))
main {S} t f a s = 𝟚^[ uncurry t ] f (s , a)

pow : ∀ {S} → DA S → DA (S → 𝟚)
pow {S} record { q₀ = q₀ ; ν = ν ; δ = δ } =
  record { q₀ = ν ; ν = 2^1=2 𝟚^[ (λ tt → q₀) ] ; δ = main δ }

theorem-2-1 : ∀ {S da} → reachable {S} da → observable (pow da)
theorem-2-1 {S} {da} f = {!!}

theorem-2-2-⇒ : ∀ {i S} {w : List i A} (da : DA S)
              → DA.o da (DA.q₀ da) ∋ w ≡ true
              → DA.o (pow da) (DA.q₀ (pow da)) ∋ (rev w) ≡ true
theorem-2-2-⇒ da p = {!!}

theorem-2-2-⇐ : ∀ {i S} (da : DA S)
                → (w : List i A)
                → DA.o (pow da) (DA.q₀ (pow da)) ∋ w ≡ true
                → DA.o da (DA.q₀ da) ∋ (rev w) ≡ true
theorem-2-2-⇐ da [] p = {!!}
theorem-2-2-⇐ da (a ∷ as) p = {!!}
