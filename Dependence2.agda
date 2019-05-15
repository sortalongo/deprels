module Dependence2 where

open import Agda.Builtin.Equality
open import Agda.Primitive using (Level; lsuc)
open import Data.Unit
open import Data.Product
open import Data.Sum
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

-- Replaces the value mapped at i₀ with t₀.
substitute : {{_ : Eq I}} → (I → T) → I → T → I → T
substitute f i₀ t₀ i with i₀ == i
...                     | yes _ = t₀
...                     | no _  = f i

-- Whether two terms of possibly-distinct types satisfy some property.
-- TODO: this feels vaguely like a functor, except that it uses the equality
--       proof to rewrite types. Could probably be abstracted?
somehowCompare : (T → T → Type) → T → U → Dec (T ≡ U) → Type
somehowCompare _≟_ t u (yes eq) rewrite eq = t ≟ u
somehowCompare _ _ _ (no ¬eq) = ⊤


DepRelAlias : {{_ : Eq I}} → (op : (c : I → T) → J c → U) (c : I → T) → I → J c → Type₁
DepRelAlias {T = T} op c i j = Σ[ t ∈ T ]
    ∃ (somehowCompare (λ d₁ d₂ → d₁ j ≢ d₂ j) (op c) (op (substitute c i t)))

record DepRelRecord {{_ : Eq I}} (op : (c : I → T) → J c → U) (c : I → T) (i : I) (j : J c) : Type₁ where
  field
    t-sub : T
  c-sub = substitute c i t-sub
  field
    J-equal : Dec ((J c → U) ≡ (J c-sub → U)) -- TODO: only require equality between J c and J c-sub
    Depend? : somehowCompare (λ d₁ d₂ → d₁ j ≢ d₂ j) (op c) (op c-sub) J-equal

DepRelMapped : {{_ : Eq I}} → (op : (c : I → T) → J c → U) (c : I → T) → I → J c → Type
DepRelMapped {T = T} {J = J} op c i j = Σ[ t ∈ T ] let
    c-sub = substitute c i t
    -- Jor⊤ = J c-sub ⊎ ⊤
  in Σ[ mapⱼ ∈ (J c → J c-sub) ] op c j ≢ op c-sub (mapⱼ j)
