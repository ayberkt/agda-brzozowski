module FiniteAutomata where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Relation.Nullary using (yes; no)
open import Relation.Unary   using (Decidable)
open import Data.Product     using (_×_; _,_)
open import Data.Unit        using (⊤)
open import Function         using (_∘_)
open import Subset           using (Subset)
open import Level            using (suc; Level; Lift)

record DFA {l : Level} : Set (suc l) where
  field
    Q   : Set l
    Σ   : Set
    δ   : Q × Σ → Q
    q₀  : Q
    F   : Subset Q
    F?  : Decidable F

record NFA {l : Level} : Set (suc l) where
  field
    Q   : Set l
    Σ   : Set
    δ   : Q × Σ → Subset Q
    q₀  : Q
    F   : Subset Q
    F?  : Decidable F

-- Takes a function f : A → B and returns a relation R(x, y) that is inhabited
-- iff f x ≡ y represented as a function A → ℙ(B).
to-relation : ∀ {A B : Set} → (f : A → B) → (A → Subset B)
to-relation f a = λ x → x ≡ f a

-- Inclusion for DFAs into NFAs simply by converting the function into a
-- relation.
to-nfa : DFA → NFA
to-nfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record { Q = Q ; Σ = Σ ; δ = to-relation δ ; q₀ = q₀ ; F = F ; F? = F? }

-- NFA reversal.
flip-relation : ∀ {A B : Set} → (A × B → Subset A) → (A × B → Subset A)
flip-relation {A} {B} R = R-inv
  where
    -- R-inv is a new relation that gives the opposite set of states, that is,
    -- q ∈ R(p, t) holds iff there is a transition to q from p via t and

    -- q ∈ R-inv(p, t) holds iff p ∈ R(q, t) so the transitions are *flipped*.
    R-inv : A × B → Subset A
    R-inv (p , t) = λ q → (R (q , t)) p

-- Reverse transitions of a DFA by using `flip-relation` on its transition
-- relation.
rev : NFA → NFA
rev record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record { Q = Q ; Σ = Σ ; δ = flip-relation δ ; q₀ = q₀ ; F = F ; F? = F? }

to-dfa : NFA → DFA
to-dfa record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? } =
  record
    {
      Q = Subset Q       -- new set of states is the set of all subsets of Q.
    ; Σ = Σ              -- the alphabet is unchanged.
    ; δ = δ'             -- the new transition function defined in the where clause.
    ; q₀ = λ x → x ≡ q₀ -- the singleton set containing the start state.
    -- F delineates sets that contain at least one final state.
    ; F = λ U → (Data.Product.Σ Q (λ y → U y × F y))
    ; F? = {!!}
    -- proof that F is a decidable subset.
    }
    where
      -- The new transition function.
      δ' : Subset Q × Σ → Subset Q
      δ' (Q , t) = λ x → δ (x , t) x

data is-reachable (M : DFA) : (DFA.Q M) → Set where
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
                   → Data.Product.Σ (DFA.Σ M) (λ t → ((DFA.δ M) (q , t)) ≡ p)
                   → is-reachable M p

-- Returns the sub-DFA that consists of the set of reachable states.
reach : DFA → DFA
reach M@(record { Q = Q ; Σ = Σ ; δ = δ ; q₀ = q₀ ; F = F ; F? = F? }) =
  record { Q = Q' ; Σ = Σ ; δ = δ' ; q₀ = (q₀ , start-reachable) ; F = F' ; F? = {!!} }
    where
      Q' : Set
      Q' = Data.Product.Σ Q (λ p → is-reachable M p)
      δ' : Q' × Σ → Q'
      δ' ((p , p-reachable) , t) = δ (p , t) , further-reachable p p-reachable (t , refl)
      F' : Q' → Set
      F' (p , p-reach) = F p

-- TODO: Brzozowski's algorithm will look something like the following.
-- brzozowski = reach ∘ to-dfa ∘ rev ∘ reach ∘ to-dfa ∘ rev
