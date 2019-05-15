{-# OPTIONS --cubical #-}
module Beam where

open import Base
open import Dependence

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Data.Nat using (ℕ)
open import Data.Vec as Vec using (Vec)

private
  variable
    I K T U : Type₀
    J : T → Type₀
    n : ℕ

PCollection : {I : Type₀} → Type₀ → Type₀
PCollection {I} T = I → T

fromVec : Vec T n → PCollection T
fromVec = Vec.lookup

DoFn : (T : Type₀) {J : T → Type₀} (U : Type₀) → Type₀
DoFn T {J} U = (t : T) → J t → U

_parDo_ : (c : PCollection {I} T)
        → DoFn T {J} U
        → PCollection {Σ I λ i → J (c i)} U
_parDo_ c fn (i , j) = fn (c i) j

flatten : ∀ {I₁ I₂}
        → PCollection {I₁} T → PCollection {I₂} T
        → PCollection {I₁ ⊎ I₂} T
flatten l r (inl x) = l x
flatten l r (inr x) = r x

groupByKey : (c : PCollection {I} (K × T))
          → PCollection {Fiber (proj₁ ∘ c)} T
groupByKey c (k , i , _)= proj₂ (c i)

combinePerKey : {L : K → Type₀} (c : PCollection {Σ K L} T)
              -- TODO: add a traversal argument.
              → (T → T → T)
              → PCollection {Σ K λ k → ∥ L k ∥} T
combinePerKey c _•_ (k , ∣l∣) = {!   !}

module DepRels where
  open import Dependence
  parDoDepRel : (fn : DoFn T {J} U) {{_ : Eq I}} (c : PCollection {I} T)
                (i : I) (j : Σ I λ i → J (c i)) → DepRel (c parDo fn) i j

module Examples where
  open import Data.Char
  open import Data.String
  open import Data.Vec

  words : PCollection String
  words = fromVec ("foo" ∷ "bar" ∷ "baz" ∷ [])

  toChars : DoFn String Char
  toChars s = lookup (toVec s)

  chars : PCollection Char
  chars = words parDo toChars

  moreChars : PCollection Char
  moreChars = flatten chars (fromVec (toVec "bizzle"))
