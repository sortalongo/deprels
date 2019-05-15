{-# OPTIONS --cubical #-}
module Dependence where

open import Base

open import Agda.Builtin.Unit

private
  variable
    I T U : Type₀
    J : (I → T) → Type₀

substitute : {{_ : Eq I}} → (I → T) → I → T → I → T
substitute f i₀ t₀ i with i₀ == i
...                     | yes _ = t₀
...                     | no _  = f i

-- A Dependence Relation represents the structure of an operation over indexed
-- collections. The pair (i, j) is an element of the relation iff changing the
-- value i maps to could change the value j maps to when applying the operation.
DepRel : {{_ : Eq I}} → (op : (c : I → T) → J c → U) (c : I → T) → I → J c → Type₀
DepRel {I} {T} op c i j =
  Σ T λ t → (op c j) ≢ (op (substitute c i t) j)

-- The DepRel for a function has 0 or 1 elements:
-- • Constant functions have no dependence (0 elements).
-- • Non-constant functions have a dependence (1 element).
Nonconstant : (f : T → U) → Type₀
Nonconstant {T} {U} f = DepRel fnOp tt tt
  where
  fnOp : (⊤ → T) → ⊤ → U
  fnOp point _ = f (point tt)
