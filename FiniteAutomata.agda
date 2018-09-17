module FiniteAutomata where

open import Relation.Binary.PropositionalEquality
open import Data.List        using (List; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Unary   using (Decidable)
open import Data.Product     using (_×_; _,_; Σ-syntax)
open import Data.Unit        using (⊤)
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
    F?  : Decidable F

record NFA {l₁ l₂ : Level} : Set (suc (l₁ ⊔ l₂)) where
  field
    Q   : Set l₁
    Σ   : Set
    δ   : Q × Σ → Subset l₁ Q
    q₀  : Q
    F   : Subset l₂ Q
    F?  : Decidable F

-- Takes a function f : A → B and returns a relation R(x, y) that is inhabited
-- iff f x ≡ y represented as a function A → ℙ(B).
to-relation : ∀ {l₁ l₂ : Level} {A : Set l₁} {B : Set l₂}
           → (f : A → B) → (A → Subset l₂ B)
to-relation f a = λ x → x ≡ f a

-- Inclusion for DFAs into NFAs simply by converting the function into a
to-nfa : ∀ {l₁ l₂ : Level} → DFA {l₁} {l₂} → NFA {l₁}
to-nfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record { Q = Q ; Σ = Σ ; δ = to-relation δ ; q₀ = q₀ ; F = F ; F? = F? }

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

-- Reverse transitions of a DFA by using `flip-relation` on its transition
-- relation.
rev : ∀ {l₁ l₂ : Level} → NFA {l₁} {l₂} → NFA {l₁} {l₂}
rev M = record M { δ = flip-relation (NFA.δ M) }

to-dfa : ∀ {l₁ l₂ : Level} → NFA {l₁} {l₂} → DFA {suc l₁} {l₁ ⊔ l₂}
to-dfa {l₁} {l₂} record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record
    {
      Q = Subset l₁ Q -- new set of states is the set of all subsets of Q.
    ; Σ = Σ              -- the alphabet is unchanged.
    ; δ = δ'             -- the new transition function defined in the where clause.
    ; q₀ = λ x → x ≡ q₀ -- the singleton set containing the start state.
    -- F delineates sets that contain at least one final state.
    ; F = λ U → Σ[ y ∈ Q ] (U y × F y)
    ; F? = {!!}
    -- proof that F is a decidable subset.
    }
    where
      -- The new transition function.
      -- δ (Q' , t) must be { p | ∃q∈Q'.q has a transition to p }
      δ' : Subset l₁ Q × Σ → Subset l₁ Q
      δ' (Q' , t) = λ p → Σ[ q ∈ Q ] (Q' q × δ (q , t) p)

data is-reachable {l₁ l₂ : Level} (M : DFA{l₁}{l₂}) : (DFA.Q M) → Set (l₁) where
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
reach : DFA → DFA
reach M@(record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? }) =
  record { Q = Q' ; Σ = Σ ; δ = δ' ; q₀ = (q₀ , start-reachable) ; F = F' ; F? = {!!} }
    where
      Q' : Set
      Q' = Σ[ p ∈ Q ] (is-reachable M p)
      δ' : Q' × Σ → Q'
      δ' ((p , p-reachable) , t) = δ (p , t) , further-reachable p p-reachable (t , refl)
      F' : Q' → Set
      F' (p , p-reach) = F p

-- TODO: Brzozowski's algorithm will look something like the following.
-- brzozowski = reach ∘ to-dfa ∘ rev ∘ reach ∘ to-dfa ∘ rev

accepts-rec : ∀ {l : Level} → (M : DFA{l}) → (DFA.Q M) → List (DFA.Σ M) → Set
accepts-rec M p [] = (DFA.F M) p
accepts-rec M p (c ∷ cs) = accepts-rec M ((DFA.δ M) (p , c)) cs

_accepts_ : ∀ {l : Level} → (M : DFA{l}) → List (DFA.Σ M) → Set
M accepts s = accepts-rec M (DFA.q₀ M) s

-- ℒ M: the set of all strings accepted by DFA M.
ℒ : ∀ {l : Level} (M : DFA{l}) → Set
ℒ M = Σ[ s ∈ List (DFA.Σ M) ] (M accepts s)
