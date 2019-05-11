{-# OPTIONS --cubical #-}
module Base where

open import Cubical.Core.Everything hiding (I) public
open import Cubical.Data.Empty using (⊥) public
open import Cubical.Relation.Nullary
  using (yes; no; ¬_) renaming (Dec to Decidable) public
open import Function using (_∘_) public

private
  variable
    ℓ  : Level
    T : Set ℓ

infix 2 _≢_
_≢_ : {A : Type₀} → A → A → Type₀
_≢_ a a' = ¬ (a ≡ a')

record Eq (A : Set ℓ) : Set ℓ where
  constructor mkEq
  field
    eq? : (x y : A) → Decidable (x ≡ y)

_==_ : {{eq : Eq T}} (t t' : T) → Decidable (t ≡ t')
_==_ {{eq}} t t' = Eq.eq? eq t t'
