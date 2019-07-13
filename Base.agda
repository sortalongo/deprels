module Base where

open import Agda.Primitive using (Level; lsuc) public
open import Data.Unit using (⊤) renaming (tt to unit) public
open import Data.Maybe using (just; nothing; fromMaybe) renaming (Maybe to ¿_) public
module Maybe = Data.Maybe
open import Data.Nat using (ℕ; _+_) public
module Nat = Data.Nat
open import Data.Product using (Σ; Σ-syntax; ∃; ∃₂; _×_; _,_; proj₁; proj₂) public
open import Data.Empty using (⊥) public
open import Function using (_∘_; _$_; id) public
open import Relation.Binary using (Decidable) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; sym) public
open import Relation.Nullary using (Dec; yes; no; ¬_) public

-- Agda's `Set` sorts are confusingly named. Define new names to reduce that.
Type = Set
Type₁ = Set₁

Type- : (ℓ : Level) → Set (lsuc ℓ)
Type- ℓ = Set ℓ

private
  variable
    ℓ  : Level
    T : Type- ℓ
    I K : Type

-- The pairs of a function's domain and codomain.
FuncPairs : (I → K) → Type
FuncPairs {I} {K} f = ∃₂ λ k i → f i ≡ k

-- Squashes all terms in A into a single term using "irrelevance", roughly as if
-- all terms were made equal to each other. Squashed terms can't be unsquashed.
data Squash (A : Type- ℓ) : Type- ℓ where
  squash : .A → Squash A

∣_∣ = Squash

-- A typeclass for decidable equality.
record Eq (A : Type- ℓ) : Type- ℓ where
  constructor mkEq
  field
    eq? : (x y : A) → Dec (x ≡ y)

-- Syntax for decidable equality.
_==_ : {{eq : Eq T}} (t t' : T) → Dec (t ≡ t')
_==_ {{eq}} t t' = Eq.eq? eq t t'

instance

  unitEq : Eq ⊤
  Eq.eq? unitEq tt tt = yes refl

  open import Data.Nat.Properties as NatProp

  natEq : Eq ℕ
  Eq.eq? natEq = NatProp._≟_

  sigmaEq : {A : Type} {{_ : Eq A}} {B : A → Type} {{_ : {a : A} → Eq (B a)}} → Eq (Σ A B)
  Eq.eq? sigmaEq (a , b) (a' , b') with a == a'
  Eq.eq? sigmaEq (a , b) (a' , b') | yes a=a' with a' | a=a'
  Eq.eq? sigmaEq (a , b) (a' , b') | yes a=a' | .a | refl with b == b'
  Eq.eq? sigmaEq (a , b) (a' , b') | yes a=a' | .a | refl | yes b=b' rewrite b=b' = yes refl
  Eq.eq? sigmaEq (a , b) (a' , b') | yes a=a' | .a | refl | no ¬b=b' = no {!   !}
  Eq.eq? sigmaEq (a , b) (a' , b') | no ¬p = {!   !}

-- Readable syntax for `maybe`.
_map_or_ : ∀ {a b} {A : Set a} {B : Set b} → ¿ A → (A → B) → B → B
_map_or_ ma f b = Maybe.maybe f b ma
