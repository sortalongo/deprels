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

DepRel : {{_ : Eq I}} → (op : (c : I → T) → J c → U)
               (c : I → T) → I → J c → Type
DepRel {T = T} {J = J} op c i j =
  Σ[ t ∈ T ]
    let c-sub = substitute c i t in
  Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
    (convertⱼ j) map (λ j' → op c j ≢ op c-sub j') or ⊤
--

IndepRel : {{_ : Eq I}} → (op : (c : I → T) → J c → U)
               (c : I → T) → I → J c → Type
IndepRel {T = T} {J = J} op c i j =
  Σ[ t ∈ T ]
    let c-sub = substitute c i t in
  Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
    (convertⱼ j) map (λ j' → op c j ≡ op c-sub j') or ⊥
