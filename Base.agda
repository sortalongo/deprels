module Base where

open import Agda.Builtin.Equality public
open import Agda.Primitive using (Level; lsuc) public
open import Data.Unit using (⊤; tt) public
open import Data.Product using (Σ; Σ-syntax; ∃) public
open import Data.Empty using (⊥) public
open import Function using (_∘_; _$_) public
open import Relation.Nullary using (Dec; yes; no; ¬_) public

Type = Set
Type₁ = Set₁

Type- : (ℓ : Level) → Set (lsuc ℓ)
Type- ℓ = Set ℓ

private
  variable
    ℓ  : Level
    T : Type- ℓ
    I K : Type

Fiber : (I → K) → Type
Fiber {I} {K} f = Σ K λ k → Σ I λ i → f i ≡ k

data Squash (A : Type- ℓ) : Type- ℓ where
  squash : .A → Squash A

∣_∣ = Squash

infix 2 _≢_
_≢_ : {A : Type} → A → A → Type
_≢_ a a' = ¬ (a ≡ a')

record Eq (A : Type- ℓ) : Type- ℓ where
  constructor mkEq
  field
    eq? : (x y : A) → Dec (x ≡ y)

_==_ : {{eq : Eq T}} (t t' : T) → Dec (t ≡ t')
_==_ {{eq}} t t' = Eq.eq? eq t t'

instance
  unitEq : Eq ⊤
  unitEq = record { eq? = λ tt tt → yes refl }
