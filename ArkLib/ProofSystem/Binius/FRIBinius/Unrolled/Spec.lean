/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.Binius.BinaryBasefold.ProductClaim
public import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch

/-!
# Unrolled FRI-Binius: communication and error budget

The tensor batching head is followed by the Binary Basefold opening of its product claim, whose
sum-check-and-fold loop runs the ring-switching product sum-check itself. No separate
ring-switching sum-check precedes it.

`fullError` assigns the batching loss to the head's challenge and the opening's errors
(`ProductClaim.openingError`) to the remaining challenges. `fullError_sum_le_concreteWithBlockSize`
bounds their sum by `concreteErrorWithBlockSize`, which retains the block-size coefficient
`ϑ / (2^ϑ - 1)` from DP24's concrete soundness bound. `concreteError` replaces this factor by
`1`. At this common choice of factor, `concreteError_add_eq` accounts for the extra sum-check
term `2ℓ'/|L|` in `FRIBinius.RingSwitch.concreteError`.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24], §5.2, equation (42) in the 14 May 2026 full version.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled

open OracleSpec OracleComp ProtocolSpec Module
open RingSwitching RingSwitching.Packing
open scoped NNReal Binius.FRIBinius

variable (κ : ℕ) {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [Field K] [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
variable [Algebra (ZMod 2) L] {r : ℕ} [NeZero r] (b : Basis (Fin r) (ZMod 2) L)
variable {ℓ' R ϑ : ℕ} [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (h_rate : ℓ' + R < r)

/-- The batching head followed by the Binary Basefold opening wire. -/
noncomputable abbrev pSpec (γ : ℕ) :=
  TensorPrefix.headPSpec (biniusProfile κ L K β) ++ₚ
    ((!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec (ZMod 2) b γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

/-- The batching loss on the head's challenge, then the errors of the Binary Basefold opening. -/
noncomputable def fullError (γ : ℕ) :
    (pSpec κ K β b (ϑ := ϑ) h_rate γ).ChallengeIdx → ℝ≥0 :=
  Sum.elim (TensorPrefix.headRbrError (biniusProfile κ L K β))
    (BinaryBasefold.ProductClaim.openingError (ZMod 2) b γ (ϑ := ϑ) (h_rate := h_rate)) ∘
    ChallengeIdx.sumEquiv.symm

/-- The closed-form bound with one sum-check term `2ℓ'/|L|`. -/
noncomputable def concreteError (γ : ℕ) : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * ℓ') / Fintype.card L +
    (2 ^ (ℓ' + R) : ℝ≥0) / Fintype.card L +
    ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ R)) ^ γ

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] in
/-- The closed-form bound is the batching loss plus the Binary Basefold bound. -/
theorem concreteError_eq (γ : ℕ) :
    concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ =
      (κ : ℝ≥0) / Fintype.card L +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ := by
  simp only [concreteError, BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError,
    add_div]
  ring

/-- The closed-form bound with block-size coefficient `ϑ / (2^ϑ - 1)`. -/
noncomputable def concreteErrorWithBlockSize (γ : ℕ) : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * ℓ') / Fintype.card L +
    BinaryBasefold.CoreInteraction.foldingBlockFactor ϑ *
      ((2 ^ (ℓ' + R) : ℝ≥0) / Fintype.card L) +
    ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ R)) ^ γ

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] [NeZero ϑ]
  [Fact (ϑ ∣ ℓ')] in
/-- Retaining the block-size coefficient changes only the Binary Basefold term. -/
theorem concreteErrorWithBlockSize_eq (γ : ℕ) :
    concreteErrorWithBlockSize κ (L := L) (ℓ' := ℓ') (R := R) (ϑ := ϑ) γ =
      (κ : ℝ≥0) / Fintype.card L +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeErrorWithBlockSize
          L ℓ' R ϑ γ := by
  simp only [concreteErrorWithBlockSize,
    BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeErrorWithBlockSize, add_div]
  ring

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] [NeZero ϑ]
  [Fact (ϑ ∣ ℓ')] in
/-- Replacing the block-size coefficient by `1` gives the coarser bound. -/
theorem concreteErrorWithBlockSize_le_concrete (γ : ℕ) :
    concreteErrorWithBlockSize κ (L := L) (ℓ' := ℓ') (R := R) (ϑ := ϑ) γ ≤
      concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ := by
  rw [concreteErrorWithBlockSize_eq, concreteError_eq]
  exact add_le_add le_rfl
    (BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeErrorWithBlockSize_le_concrete
      L ℓ' R ϑ γ)

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] in
/-- Adding one sum-check term `2ℓ'/|L|` to `concreteError` gives the bound of the composition
with a separate ring-switching sum-check (`FRIBinius.RingSwitch.concreteError`). -/
theorem concreteError_add_eq (γ : ℕ) :
    concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ + (ℓ' : ℝ≥0) * (2 / Fintype.card L) =
      FRIBinius.RingSwitch.concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ := by
  rw [concreteError_eq, FRIBinius.RingSwitch.concreteError]
  ring

omit [NeZero R] in
/-- The challenge-error sum is the batching loss plus the opening's sum. -/
theorem fullError_sum (γ : ℕ) :
    (∑ i, fullError κ K β b (ϑ := ϑ) h_rate γ i) =
      (κ : ℝ≥0) / Fintype.card L +
        ∑ i, BinaryBasefold.ProductClaim.openingError (ZMod 2) b γ
          (ϑ := ϑ) (h_rate := h_rate) i := by
  unfold fullError
  refine (Equiv.sum_comp ChallengeIdx.sumEquiv.symm (Sum.elim _ _)).trans ?_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [TensorPrefix.headRbrError_sum]

/-- The challenge-error sum is at most the bound retaining the folding block size. -/
theorem fullError_sum_le_concreteWithBlockSize (γ : ℕ) :
    (∑ i, fullError κ K β b (ϑ := ϑ) h_rate γ i) ≤
      concreteErrorWithBlockSize κ (L := L) (ℓ' := ℓ') (R := R) (ϑ := ϑ) γ := by
  rw [fullError_sum, concreteErrorWithBlockSize_eq]
  exact add_le_add_right
    (BinaryBasefold.ProductClaim.openingError_sum_le_concreteWithBlockSize (ZMod 2) b γ
      (ϑ := ϑ) (h_rate := h_rate)) _

/-- The challenge-error sum is at most `concreteError`. -/
theorem fullError_sum_le_concrete (γ : ℕ) :
    (∑ i, fullError κ K β b (ϑ := ϑ) h_rate γ i) ≤
      concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ :=
  (fullError_sum_le_concreteWithBlockSize κ K β b (ϑ := ϑ) h_rate γ).trans
    (concreteErrorWithBlockSize_le_concrete κ (ϑ := ϑ) γ)

end Binius.FRIBinius.Unrolled
