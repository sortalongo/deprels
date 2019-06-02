open import Base

-- Defines dependence relations in terms of operators between partial functions.
--
-- This is an attempt to work around the problems in the Dependence module,
-- where comparing elements across indexes within the output type family
-- (specifically, comparing `J c` with `J c-sub`) is problematic. Using partial
-- functions `I →? T` allows us to define a supertype to all indexes in the
-- output type family (where nonexistent terms are mapped to `nothing`).
module Dependence where

-- DepRel definition.
module _ {I T : Type} {{_ : Eq I}} where
  -- Replaces the value mapped by `i₀` with `t₀`.
  substitute : (I → T) → I → T → I → T
  substitute f i₀ t₀ i with i₀ == i
  ...                     | yes _ = t₀
  ...                     | no _  = f i

  module _  {J U : Type} (op : (I → T) → (J → U)) where
    -- A DepRel is a heterogeneous binary relation between I and J over some
    -- operation. The pair (i, j) is in the relation iff, for all collections `c`,
    -- there exists a `t` such that substituting it for `c i` produces a different
    -- value at `op c j`.
    DepRel : I → J → Type
    DepRel i j = (c : I → T) → Σ[ t ∈ T ] op c j ≢ (op (substitute c i t)) j


    -- Useful DepRels must be decidable: that is, we must be able to prove that
    -- every `(i, j)` is either in or not in the relation.
    DecidableDepRel = Decidable DepRel

-- A function that is not constant can be thought of as an operator with ⊤ as
-- the input and output indexes. We define this property and prove this
-- relationship below.
module _ {T U : Type} where
  Nonconstant : (f : T → U) → Type
  Nonconstant f = (t : T) → Σ[ t' ∈ T ] f t ≢ f t'

  -- Proves that a DepRel for an `op : (⊤ → T) → (⊤ → U)` can be converted into
  -- a claim of whether a function `T → U` is constant.
  Nonconstant-from-DepRel : {op : (⊤ → T) → (⊤ → U)} → DepRel op unit unit
                          → Nonconstant (λ t → op (λ _ → t) unit)
  Nonconstant-from-DepRel deprel t = deprel λ _ → t

  -- TODO: prove converse claim to make a bijection.

private
  module Examples where
    open import Data.Fin as Fin using (Fin)
    open import Data.Vec as Vec using (Vec; _∷_; [])

    -- An example operation:
    -- Given any collection of natural numbers, add one to each.
    -- We define the operation and provide a decidable dep-rel for it.
    -- Then, we use the operation on a few different collections.
    module AddOneToEach {I : Type} where
      op : (I → ℕ) → I → ℕ
      op c i = 1 + c i

      module _ {{_ : Eq I}} where
        op-DepRel = DepRel {I} op

        -- In AddOneToEach.op, `j` depends on `i` iff `j == i`.
        -- We prove this by splitting on the cases of `j == i`, showing that
        -- `DepRel i j` is inhabited in the affirmative case and that
        -- `¬ DepRel i j` is empty in the negative case.
        op-DecidableDepRel : DecidableDepRel {I} op
        op-DecidableDepRel i j with j == i
        op-DecidableDepRel i j | yes j≡i rewrite j≡i = yes Dependent
          where
          Dependent : DepRel op i i
          Dependent c with c i | i == i
          Dependent c | 0 | yes _ = 1 , λ()
          Dependent c | 0 | no i≢i = 1 , λ _ → i≢i refl
          Dependent c | Nat.suc n | yes _ = 0 , λ ()
          Dependent c | Nat.suc n | no i≢i = 0 , λ _ → i≢i refl
        op-DecidableDepRel i j | no j≢i = no Independent
          where
          c : I → ℕ
          c i = 0
          Independent : ¬ (DepRel op i j)
          Independent deprel with deprel c
          Independent deprel | _ , _ with i == j
          Independent deprel | _ , _ | yes p = j≢i (sym p)
          Independent deprel | _ , 1≡1 | no ¬p = 1≡1 refl

    -- A collection of 3 elements.
    egFin : Fin 3 → ℕ
    egFin = Vec.lookup (2 ∷ 1 ∷ 0 ∷ [])
    egFin+1 = AddOneToEach.op egFin
    -- Prove that each element in the produced collection matches expectations.
    egFin+1-test : (i : _) → egFin+1 i ≡ Nat.suc (egFin i)
    egFin+1-test i = refl

    -- An infinite collection.
    eg∞ : ℕ → ℕ
    eg∞ n = n
    eg∞+1 = AddOneToEach.op eg∞
    -- Prove that each element in the produced collection matches expectations.
    eq∞-test : (i : ℕ) → eg∞+1 i ≡ Nat.suc (eg∞ i)
    eq∞-test i = refl

    -- A sum operator that takes the sum of a finite set of natural numbers.
    module Sum {max : ℕ} where

        I = Fin (1 + max)

        op : (I → ℕ) → ⊤ → ℕ
        op c _ = prefixSum max (Fin.fromℕ max)
          module _ where
          -- Use a counter for termination checker because pattern matching on a
          -- `Fin (suc n)` changes the type to `Fin n`, which isn't what we want.
          prefixSum : (counter : ℕ) → I → ℕ
          prefixSum Nat.zero i = c i
          prefixSum (Nat.suc n) i = c i + prefixSum n (Fin.pred i)

        module _ {{_ : Eq I}} where
          op-DepRel = DepRel {I} op

          -- In Sum.op, `j` always depends on `i` .
          -- We prove this by computing a `yes _` for all `i`.
          op-DecidableDepRel : DecidableDepRel {I} op
          op-DecidableDepRel i unit = yes Dependent
            where
            -- Lemma for recursing on prefixSum.
            substituted-prefixSum-distinct :
                  (i max' : I) (c : I → ℕ) (n n' : ℕ) → n ≢ n' →
                  prefixSum c unit (Fin.toℕ max') max' ≢ prefixSum (substitute c i n') unit (Fin.toℕ max') max'
            substituted-prefixSum-distinct i max' c n n' n≢n' = {!   !}

            import Data.Fin.Properties as Finₚ
            Dependent : DepRel op i unit
            Dependent c with c i
            Dependent c | ℕ.zero with substituted-prefixSum-distinct i (Fin.fromℕ max) c 0 1 λ()
            Dependent _ | _ | distinct rewrite Finₚ.toℕ-fromℕ max = 1 , distinct
            Dependent c | ℕ.suc n with substituted-prefixSum-distinct i (Fin.fromℕ max) c (ℕ.suc n) 0 λ()
            Dependent _ | _ | distinct rewrite Finₚ.toℕ-fromℕ max = 0 , distinct

    egFinSum = Sum.op egFin
    egFinSum-test : egFinSum unit ≡ 3
    egFinSum-test = refl
