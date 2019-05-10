{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything hiding (I)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Data.Nat using (ℕ)
open import Data.Vec as Vec using (Vec)
open import Function

module Beam where
  variable
    I K T U : Set
    J : T → Set
    n : ℕ

  PCollection : {I : Set} → Set → Set
  PCollection {I} T = I → T

  fromVec : Vec T n → PCollection T
  fromVec = Vec.lookup

  DoFn : (T : Set) {J : T → Set} (U : Set) → Set
  DoFn T {J} U = (t : T) → J t → U

  _parDo_ : (ct : PCollection {I} T)
          → DoFn T {J} U
          → PCollection {Σ I λ i → J (ct i)} U
  _parDo_ ct fn (i , j) = fn (ct i) j

  flatten : ∀ {I₁ I₂}
          → PCollection {I₁} T → PCollection {I₂} T
          → PCollection {I₁ ⊎ I₂} T
  flatten l r (inl x) = l x
  flatten l r (inr x) = r x

  Fiber : (I → K) → Set
  Fiber {I} {K} f = Σ K λ k → Σ I λ i → f i ≡ k

  groupByKey : (c : PCollection {I} (K × T))
            → PCollection {Fiber (proj₁ ∘ c)} T
  groupByKey c (k , i , _)= proj₂ (c i)

  combinePerKey : {L : K → Set} (c : PCollection {Σ K L} T)
                -- TODO: add a traversal argument.
                → (T → T → T)
                → PCollection {Σ K λ k → ∥ L k ∥} T
  combinePerKey c _•_ (k , ∣l∣) = {!   !}

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
