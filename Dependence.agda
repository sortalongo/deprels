module Dependence where

open import Base
open import Data.Maybe using (Maybe; just; nothing; maybe)

private
  variable
    ℓ : Level
    C I T U : Type
    D : C → Type
    J : (I → T) → Type

private
  -- Replaces the value mapped by `i₀` with `t₀`.
  substitute : {{_ : Eq I}} → (I → T) → I → T → I → T
  substitute f i₀ t₀ i with i₀ == i
  ...                     | yes _ = t₀
  ...                     | no _  = f i

  -- Readable syntax for `maybe`.
  _map_or_ : ∀ {a b} {A : Set a} {B : Set b} → Maybe A → (A → B) → B → B
  _map_or_ ma f b = maybe f b ma

-- A relation between the input and output indexes of an operation over indexed
-- collections. A pair is in the relation if the given indices are independent.
DepRel : {{_ : Eq I}} → (op : (c : I → T) → J c → U)
               (c : I → T) → I → J c → Type
DepRel {T = T} {J = J} op c i j =
  Σ[ t ∈ T ]
    let c-sub = substitute c i t in
  Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
    (convertⱼ j) map (λ j' → op c j ≢ op c-sub j') or ⊤

-- An operation with input and output indexes of ⊤ is just a function.
-- A DepRel for such an operation is simply whether the function is nonconstant.
-- (Note: `unit` is the only term in the "Unit" singleton type `⊤`.)
Nonconstant : {{_ : Eq I}} (f : T → U) → Type
Nonconstant {T = T} f = (t : T) → DepRel (λ c → f ∘ c) (λ _ → t) unit unit

-- A relation between the input and output indexes of an operation over indexed
-- collections. A pair is in the relation if the given indices are independent.
IndepRel : {{_ : Eq I}} → (op : (c : I → T) → J c → U)
               (c : I → T) → I → J c → Type
IndepRel {T = T} {J = J} op c i j =
  Σ[ t ∈ T ]
    let c-sub = substitute c i t in
  Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
    (convertⱼ j) map (λ j' → op c j ≡ op c-sub j') or ⊥

-- An operation with input and output indexes of ⊤ is just a function.
-- An IndepRel for such an operation is simply whether the function is constant.
-- (Note: `unit` is the only term in the "Unit" singleton type `⊤`.)
Constant : {{_ : Eq I}} (f : T → U) → Type
Constant {T = T} f = (t : T) → IndepRel (λ c → f ∘ c) (λ _ → t) unit unit
