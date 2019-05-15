module Dependence2 where

open import Agda.Builtin.Equality
open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
open import Data.Maybe
open import Data.Product using (Σ; Σ-syntax; ∃)
open import Data.Unit
open import Function using (_∘_; _$_)
open import Relation.Nullary

Type = Set
Type₁ = Set₁

Type- : (ℓ : Level) → Set (lsuc ℓ)
Type- ℓ = Set ℓ

private
  variable
    ℓ : Level
    C I T U : Type
    D : C → Type
    J : (I → T) → Type

_≢_ : T → T → Type
_≢_ x x' = ¬ (x ≡ x')

record Eq (A : Type- ℓ) : Type- ℓ where
  constructor mkEq
  field
    eq? : (x y : A) → Dec (x ≡ y)

_==_ : {{eq : Eq T}} (t t' : T) → Dec (t ≡ t')
_==_ {{eq}} t t' = Eq.eq? eq t t'

private
  -- Replaces the value mapped at `i₀` with `t₀`.
  substitute : {{_ : Eq I}} → (I → T) → I → T → I → T
  substitute f i₀ t₀ i with i₀ == i
  ...                     | yes _ = t₀
  ...                     | no _  = f i

  -- Readable syntax for `maybe`.
  _map_or_ : ∀ {a b} {A : Set a} {B : Set b} → Maybe A → (A → B) → B → B
  _map_or_ ma f b = maybe f b ma

DepRelMapped : {{_ : Eq I}} → (op : (c : I → T) → J c → U)
               (c : I → T) → I → J c → Type
DepRelMapped {T = T} {J = J} op c i j =
  Σ[ t ∈ T ]
    let c-sub = substitute c i t in
  Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
    (convertⱼ j) map (λ j' → op c j ≢ op c-sub j') or ⊤
--

IndepRelMapped : {{_ : Eq I}} → (op : (c : I → T) → J c → U)
               (c : I → T) → I → J c → Type
IndepRelMapped {T = T} {J = J} op c i j =
  Σ[ t ∈ T ]
    let c-sub = substitute c i t in
  Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
    (convertⱼ j) map (λ j' → op c j ≡ op c-sub j') or ⊥
