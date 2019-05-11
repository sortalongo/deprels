{-# OPTIONS --cubical #-}
module Dependence where

open import Base

private
  variable
    I J T U : Type₀

substitute : {{_ : Eq I}} → (I → T) → I → T → I → T
substitute f i₀ t₀ i with i₀ == i
...                     | yes _ = t₀
...                     | no _  = f i

DepRel : {{_ : Eq I}} → ((I → T) → J → U) → I → J → Type₀
DepRel {I} {T} {J} {{eq}} op i j =
  (c : I → T) → Σ T λ t → (op c j) ≢ op (substitute c i t) j --
