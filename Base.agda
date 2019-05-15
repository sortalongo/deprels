{-# OPTIONS --cubical #-}
module Base where

open import Agda.Builtin.Unit
open import Cubical.Core.Everything hiding (I) public
open import Cubical.Foundations.Prelude hiding (I; J) public
open import Cubical.Data.Empty using (⊥) public
open import Cubical.Relation.Nullary
  using (yes; no; ¬_) renaming (Dec to Decidable) public
open import Function using (_∘_) public

private
  variable
    ℓ  : Level
    T : Type ℓ
    I K : Type₀

Fiber : (I → K) → Type₀
Fiber {I} {K} f = Σ K λ k → Σ I λ i → f i ≡ k

infix 2 _≢_
_≢_ : {A : Type₀} → A → A → Type₀
_≢_ a a' = ¬ (a ≡ a')

record Eq (A : Type ℓ) : Type ℓ where
  constructor mkEq
  field
    eq? : (x y : A) → Decidable (x ≡ y)

_==_ : {{eq : Eq T}} (t t' : T) → Decidable (t ≡ t')
_==_ {{eq}} t t' = Eq.eq? eq t t'

instance
  unitEq : Eq ⊤
  unitEq = record { eq? = λ tt tt → yes refl }
