module FiniteAutomata where

open import Relation.Binary.PropositionalEquality
open import Data.List        using (List; []; _∷_)
open import Data.Maybe       using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Unary   using (Decidable)
open import Data.Product     using (_×_; _,_; Σ-syntax)
open import Data.Unit        using (⊤)
open import Data.Empty       using (⊥)
open import Function         using (_∘_)
open import Subset           using (Subset)
open import Level            using (suc; Level; Lift; _⊔_)

record DFA {l₁ l₂ : Level} : Set (suc (l₁ ⊔ l₂)) where
  field
    Q   : Set l₁
    Σ   : Set
    δ   : Q × Σ → Q
    q₀  : Q
    F   : Subset l₂ Q

record NFA {l₁ l₂ : Level} : Set (suc (l₁ ⊔ l₂)) where
  field
    Q   : Set l₁
    Σ   : Set
    δ   : Q × Maybe Σ → Subset l₁ Q
    q₀  : Q
    F   : Subset l₂ Q

-- Takes a function f : A → B and returns a relation R(x, y) that is inhabited
-- iff f x ≡ y represented as a function A → ℙ(B).
non-deterministic : ∀ {l₁ : Level} {A : Set l₁} {B : Set}
                 → (f : A × B → A) → (A × Maybe B → Subset l₁ A)
non-deterministic f (a , just b)  = λ x → f (a , b) ≡ x
non-deterministic f (a , nothing) = λ x → Lift ⊥

-- Inclusion for DFAs into NFAs simply by converting the function into a
-- relation.
to-nfa : ∀ {l₁ l₂ : Level} → DFA {l₁} {l₂} → NFA {l₁}
to-nfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record { Q = Q ; Σ = Σ ; δ = non-deterministic δ ; q₀ = q₀ ; F = F }

-- NFA reversal.
flip-relation : ∀  {l₁ l₂ : Level} {A : Set l₁} {B : Set l₂}
             → (A × B → Subset l₁ A) → (A × B → Subset l₁ A)
flip-relation {l₁} {l₂} {A} {B} R = R-inv
  where
    -- R-inv is a new relation that gives the opposite set of states, that is,
    -- q ∈ R(p, t) holds iff there is a transition to q from p via t and

    -- q ∈ R-inv(p, t) holds iff p ∈ R(q, t) so the transitions are *flipped*.
    R-inv : A × B → Subset l₁ A
    R-inv (p , t) = λ q → (R (q , t)) p

-- Augment a given set of states with a new start state "★".
-- `inj` injects the given states to the new set.
data [_]+★ {l : Level} (Q : Set l) : Set l where
  inj : Q → [ Q ]+★
  ★  : [ Q ]+★

-- Reverse transitions of a DFA by using `flip-relation` on its transition
-- relation.
rev : ∀ {l₁ l₂ : Level} → NFA {l₁} {l₂} → NFA {l₁} {l₂}
rev {l₁} {l₂} record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record { Q = [ Q ]+★ ; Σ = Σ ; δ = δ' ; q₀ = ★ ; F = {!!} }
    where
      F' : Subset l₂ [ Q ]+★
      F' (inj q) = {!!} -- TODO: should be q ≡ q₀.
      F' ★      = Lift ⊥
      δ' : [ Q ]+★ × Maybe Σ → Subset l₁ ([ Q ]+★)
      δ' (inj p , t)       (inj q) = (δ (q , t)) p
      δ' (inj p , t)       ★      = Lift ⊥
      δ' (★    , just t)  (inj q) = Lift ⊥
      -- TODO: the following case should add ε transitions to the final states
      -- of the given NFA.
      δ' (★    , nothing) (inj q) = {!!} -- should be F q
      δ' (★    , t)       ★      = Lift ⊥

to-dfa : ∀ {l₁ l₂ : Level} → NFA {l₁} {l₂} → DFA {suc l₁} {l₁ ⊔ l₂}
to-dfa {l₁} {l₂} record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F } =
  record
    {
      Q = Subset l₁ Q -- new set of states is the set of all subsets of Q.
    ; Σ = Σ              -- the alphabet is unchanged.
    ; δ = δ'             -- the new transition function defined in the where clause.
    ; q₀ = λ x → x ≡ q₀ -- the singleton set containing the start state.
    -- F delineates sets that contain at least one final state.
    ; F = λ U → Σ[ y ∈ Q ] (U y × F y)
    }
    where
      -- The new transition function.
      -- δ (Q' , t) must be { p | ∃q∈Q'.q has a transition to p }
      δ' : Subset l₁ Q × Σ → Subset l₁ Q
      δ' (Q' , t) = λ p → Σ[ q ∈ Q ] (Q' q × δ (q , just t) p)

data is-reachable {l₁ l₂ : Level} (M : DFA {l₁} {l₂}) : (DFA.Q M) → Set l₁ where
  -- The start state is reachable by definition.
  start-reachable   : is-reachable M (DFA.q₀ M)
  -- To construct an inhabitant of `is-reachable M p` with `further-reachable`
  -- we need three things: (1) some state `q`, (2) a proof that `q` is
  -- reachable, and (3) the existence of a transition `t` taking which on `q`
  -- leads to `p`. In the presence of these three, `further-reachable` witnesses
  -- the fact that `p` is reachable.
  further-reachable : ∀ {p : DFA.Q M}
                   → (q : DFA.Q M)
                   → is-reachable M q
                   → Σ[ t ∈ (DFA.Σ M) ] (DFA.δ M) (q , t) ≡ p
                   → is-reachable M p

-- Returns the sub-DFA that consists of the set of reachable states.
reach : ∀ {l₁ l₂ : Level} → DFA {l₁} {l₂} → DFA {l₁} {l₂}
reach {l₁} {l₂} M@(record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F }) =
  record { Q = Q' ; Σ = Σ ; δ = δ' ; q₀ = (q₀ , start-reachable) ; F = F' }
    where
      Q' : Set l₁
      Q' = Σ[ p ∈ Q ] (is-reachable M p)
      δ' : Q' × Σ → Q'
      δ' ((p , p-reachable) , t) = δ (p , t) , further-reachable p p-reachable (t , refl)
      F' : Q' → Set l₂
      F' (p , p-reach) = F p

accepts-rec : ∀ {l₁ l₂ : Level}
           → (M : DFA{l₁}{l₂})
           → (DFA.Q M)
           → List (DFA.Σ M)
           → Set l₂
accepts-rec M p [] = (DFA.F M) p
accepts-rec M p (c ∷ cs) = accepts-rec M ((DFA.δ M) (p , c)) cs

_accepts_ : ∀ {l₁ l₂ : Level} → (M : DFA{l₁}{l₂}) → List (DFA.Σ M) → Set l₂
M accepts s = accepts-rec M (DFA.q₀ M) s

-- ℒ M: the set of all strings accepted by DFA M.
ℒ : ∀ {l : Level} (M : DFA{l}) → Set
ℒ M = Σ[ s ∈ List (DFA.Σ M) ] (M accepts s)

brzozowski : ∀ {l₁ l₂} → DFA {l₁} {l₂} → DFA {suc (suc l₁)} {l₂ ⊔ suc l₁}
brzozowski m = reach (to-dfa (rev (to-nfa (reach (to-dfa (rev (to-nfa m)))))))

brzozowski-same-lang-⇒ : ∀ {l₁ l₂} (M : DFA {l₁} {l₂}) (s : List (DFA.Σ M))
                       → M accepts s
                       → (brzozowski M) accepts s
brzozowski-same-lang-⇒ M s p = {!!}

brzozowski-same-lang-⇐ : ∀ {l₁ l₂} (M : DFA {l₁} {l₂}) (s : List (DFA.Σ M))
                       → (brzozowski M) accepts s
                       → M accepts s
brzozowski-same-lang-⇐ M s x = {!!}
