module CoalgebraicAutomata (A : Set) where

open import Data.Bool using (true; false; _∨_; not) renaming (Bool to 𝟚)
open import Size
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Surjection using (Surjective)
open import Data.Product using (∃; _×_; _,_; uncurry; Σ-syntax)
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

record DA (S : Set) : Set where
  field
    q₀ : 𝟙 → S
    ν  : S → 𝟚
    δ  : S → A → S

  -- A list of states is accepting if it contains at least one final state.
  νs : ∀ {i} (ss : List i S) → 𝟚
  νs ss = any ν ss

  -- We step to a new listo f states by pointwise applying the transition function.
  δs : ∀ {i} (ss : List i S) → A → List i S
  δs ss a = map (λ s → δ s a) ss

  -- x_w in Bonsangue et al's notation.
  δ* : ∀ {i} → (𝟙 → S) → List i A → S
  δ* x []        = x tt
  δ* x (t ∷ ts) = δ (δ* x ts) t

  r : ∀ {i} → List i A → S
  r w = δ* q₀ w

  o : ∀ {i} → (𝟙 → S) → (List i A → 𝟚)
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

contra-pow-functor : ∀ {V W : Set} → (f : V → W) → (W → 𝟚) → (V → 𝟚)
contra-pow-functor f g = λ v → g (f v)

2^1=2 : ∀ {A : Set} → (A → 𝟙 → 𝟚) → (A → 𝟚)
2^1=2 f = λ x → f x tt

-- The main construction.
brzo : ∀ {S : Set} → (t : S → A → S) → ((S → 𝟚) → (A → S → 𝟚))
brzo {S} t = step-3
  where
    step-2 : (S → 𝟚) → (S × A → 𝟚)
    step-2 = contra-pow-functor (uncurry t)
    step-3 : (S → 𝟚) → (A → S → 𝟚)
    step-3 f a s = step-2 f (s , a)

pow : ∀ {S} → DA S → DA (S → 𝟚)
pow {S} record { q₀ = q₀ ; ν = ν ; δ = δ } =
  record { q₀ = λ tt → ν   ; ν = 2^1=2 (contra-pow-functor q₀) ; δ = brzo δ }

theorem-2-1 : ∀ {S X} → reachable {S} X → observable (pow X)
theorem-2-1 = {!!}

-- theorem-2-2 : ∀ {S X} →
