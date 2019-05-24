open import Base

-- Defines dependence relations in terms of operators between partial functions.
--
-- This is an attempt to work around the problems in the Dependence module,
-- where comparing elements across indexes within the output type family
-- (specifically, comparing `J c` with `J c-sub`) is problematic. Using partial
-- functions `I →? T` allows us to define a supertype to all indexes in the
-- output type family (where nonexistent terms are mapped to `nothing`).
module DependenceMaybe where

¿_ : Type → Type -- Can't use `_?` because `?` is reserved.
¿ T = Maybe T

_→?_ : (I T : Type) → Type
I →? T = I → Maybe T

-- DepRel definition.
module _ {I T J U : Type} {{_ : Eq I}}
         (op : (I →? T) → (J →? U)) where
  private
    -- Replaces the value mapped by `i₀` with `t₀`.
    substitute : (I →? T) → I → ¿ T → I →? T
    substitute f i₀ t₀ i with i₀ == i
    ...                     | yes _ = t₀
    ...                     | no _  = f i

  DepRel : I → J → Type
  DepRel i j = (c : I →? T) → Σ[ t ∈ ¿ T ] (op c) j ≢ (op (substitute c i t)) j

-- A function that is not constant can be thought of as an operator with ⊤ as
-- the input and output indexes. We define this property and prove this
-- relationship below.
module _ {T U : Type} (f : T → U) where
  Nonconstant : Type
  Nonconstant = (t : T) → Σ[ t' ∈ T ] f t ≢ f t'

-- Proves that a DepRel for an `op : (⊤ →? T) → (⊤ →? U)` can be converted into
-- a claim of whether a function `T →? U` is constant.
Nonconstant-from-DepRel : {T U : Type} {op : (⊤ →? T) → (⊤ →? U)}
                        → DepRel op unit unit → Nonconstant (λ t → op (λ _ → t))
Nonconstant-from-DepRel deprel t with deprel λ _ → t
Nonconstant-from-DepRel deprel t | (t? , t-neq) = (t? , unit-injective t-neq)
  where
  unit-injective : {A : Type} {f f' : ⊤ → A} → f unit ≢ f' unit → f ≢ f'
  unit-injective f-neq f-eq rewrite f-eq = f-neq refl
