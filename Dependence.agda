open import Base

-- Defines dependence as a relation between input and output elements of a
-- transformation.
module Dependence where

module _ {I T U : Type}
         {{_ : Eq I}} where
  private
    -- Replaces the value mapped by `i₀` with `t₀`.
    substitute : (I → T) → I → T → I → T
    substitute f i₀ t₀ i with i₀ == i
    ...                     | yes _ = t₀
    ...                     | no _  = f i

  module _ {J : (I → T) → Type}
           (op : (c : I → T) → J c → U)
           (c : I → T) where

    -- A relation between `I` and `J`, the indexes of `op`. A pair is in the
    -- relation if the given indices are dependent. Dependence means that
    -- changing the `t` mapped by `i` can change the `u` mapped by `j`.
    --
    -- Defining this concept is tricky because changing `t` can cause the type
    -- of `j` to change. To handle this, we also require a conversion function
    -- `convertⱼ : J c → Maybe (J c-sub)` which allows us to find the new `j'`
    -- corresponding to `j`. If no reasonable conversion exists, the conversion
    -- can return `nothing`, in which case the dependence is assumed. This
    -- conservative assumption leads to dependence being _opt out_: a pair can
    -- only be made independent by providing an example, `t`, and a conversion
    --
    -- Unfortunately, the definition is overly permissive. `convertⱼ` can be
    -- chosen so that dependent indices are made to appear independent. This
    -- must be solved before moving on to analyze the dep-rels of particular
    -- computational models.
    DepRel : I → J c → Type
    DepRel i j =
      Σ[ t ∈ T ]
        let c-sub = substitute c i t in
      Σ[ convertⱼ ∈ (J c → Maybe (J c-sub)) ]
        (convertⱼ j) map (λ j' → op c j ≢ op c-sub j') or ⊤

-- An operation with input and output indexes of ⊤ is just a function.
-- A DepRel for such an operation is simply whether the function is nonconstant.
--
-- This definition has a trick: since the output index (`J` above) is `λ _ → ⊤`,
-- independent of the "collection" `t`, we can move the dependence on `t` from
-- the relation's arguments to its definition. Informally, this changes the
-- meaning of the relation from "given an input collection, the dependence is _"
-- to "for all input collections, the dependence does (not) exist."
--
-- Note: `unit` is the only term in the "Unit" singleton type `⊤`.
Nonconstant : {T U : Type} (f : T → U) → Type
Nonconstant {T} f = (t : T) → DepRel (λ c → f ∘ c) (λ _ → t) unit unit

module Examples where
  open import Data.Nat
  open import Data.Empty

  -- show examples of constant and non-constant functions.
  addOne : ℕ → ℕ
  addOne n = 1 + n

  addOne-nonconstant : Nonconstant addOne
  addOne-nonconstant n = 1 + n , id ∘ just , λ()

  -- Note that, due to the `convertⱼ` function being partial, we can't prove
  -- that functions are constant. The implementer of the dep-rel can simply give
  -- `λ _ → nothing`, essentially claiming ignorance of the mapping between `J c`
  -- and `J c-sub`. See below for an illustration of the issue.
  --
  -- This situation isn't a concern since it merely represents a conservative
  -- assumption: that the provider of the dep-rel may not be able to define good
  -- conversion functions.
  five : ℕ → ℕ
  five _ = 5

  five-not-nonconstant : ¬ Nonconstant five
  five-not-nonconstant is-nonconst with is-nonconst 0
  five-not-nonconstant _ | _ , convertⱼ , _ with convertⱼ unit
  five-not-nonconstant _ | _ , _ , eq | just x = eq refl
  -- Since `convertⱼ` returns `nothing`, we can't prove constancy.
  -- Doing so would require assuming that `convertⱼ` never returns `nothing`.
  five-not-nonconstant _ | _ , _ , eq | nothing = {! {- eq : ⊤ -}  !}
