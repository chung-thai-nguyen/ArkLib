/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/

import ArkLibTest.ProofSystem.RingSwitching.Conformance.BiniusComposition
import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.General
import CompPoly.Fields.Binary.Tower.Concrete.Basis

/-!
# Unrolled FRI-Binius regression checks

The checks use the `GF(16)/GF(2)` instance of the separate-sum-check composition test: two packed
variables, one retained variable, the nonconstant source `X₀ + X₂` and its honest first oracle.

* Both compositions are stated for the same input relation.
* The honest source is accepted with probability one.
* At block size one the unrolled bound is the separate-sum-check bound minus `2ℓ'/|L|`
  and is below one.
* The block-size coefficient is one at block size one. At block size two the sharper bound is
  strictly below the coarser bound and applies to knowledge soundness and soundness.
* The Binary Basefold final check multiplies by the multiplier value: with a zero multiplier it
  still requires a zero target, and at `evalMultiplier` it is the `eq̃` check.
-/

open OracleComp OracleSpec ProtocolSpec Module MvPolynomial
open RingSwitching RingSwitching.Packing Sumcheck.Structured Binius.BinaryBasefold
open scoped NNReal
noncomputable section
namespace ArkLibTest.FRIBinius.Unrolled

open ArkLibTest.RingSwitchingConformance.BiniusComposition BbfGf16Parameters
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fintype Gf16 := Fintype.ofFinite Gf16
local instance : DecidableEq Gf16 := Classical.decEq Gf16
local instance : SampleableType Gf16 := SampleableType.ofFintype Gf16
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩
local instance : Fact (basis 0 = 1) := ⟨betaBasis_zero⟩
local instance : Fact (LinearIndependent (ZMod 2) ⇑basis) := ⟨basis.linearIndependent⟩
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨CharP.prime_ringChar (ZMod 2)⟩

/-- The unrolled composition is secure for the input relation of the separate-sum-check
composition. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((Binius.FRIBinius.Unrolled.fullVerifier 2 (ZMod 2) basis basis
      (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn profile rfl interface) acceptRejectOracleRel
      (Binius.FRIBinius.Unrolled.fullError 2 (ZMod 2) basis basis (ϑ := 1) (by decide) 8) :=
  Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness 2 (ZMod 2) basis basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl

/-- The unrolled composite accepts the nonconstant honest source with probability one. -/
theorem honest_probability {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let R := OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (Binius.FRIBinius.Unrolled.fullReduction 2 (ZMod 2) basis basis
        (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8)
    let pSpec := Binius.FRIBinius.Unrolled.pSpec 2 (ZMod 2) basis basis
      (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) 8
    let pImpl : QueryImpl ([]ₒ + [pSpec.Challenge]ₒ'challengeOracleInterface)
      (StateT σ ProbComp) := QueryImpl.addLift impl challengeQueryImpl
    Pr{let out ← OptionT.mk do
      let st ← init
      (simulateQ pImpl (R.run ((point, aeval point source.val), honestOracle) source).run).run' st}[
        (out.2, out.1.2.2) ∈ acceptRejectOracleRel ∧ out.1.2.1 = out.2] = 1 := by
  have h := Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness 2 (ZMod 2) basis basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl
  change Reduction.perfectCompleteness init impl
    (TensorPrefix.relIn profile rfl interface.strictView)
    acceptRejectOracleRel (OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (Binius.FRIBinius.Unrolled.fullReduction 2 (ZMod 2) basis basis
        (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8)) at h
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  exact h ((point, aeval point source.val), honestOracle) source honest_input_actual

/-- The bound is `8/16 + (3/4)^8 < 1`, and one sum-check term `2/16` below the separate-sum-check
bound. -/
theorem concreteError_lt :
    Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 =
        8 / 16 + (3 / 4 : ℝ≥0) ^ 8 ∧
      Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 < 1 ∧
      Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 <
        Binius.FRIBinius.RingSwitch.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 := by
  have hadd := Binius.FRIBinius.Unrolled.concreteError_add_eq 2 (L := Gf16) (ℓ' := 1) (R := 1) 8
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Binius.FRIBinius.Unrolled.concreteError, card_gf16]
  · norm_num [Binius.FRIBinius.Unrolled.concreteError, card_gf16]
  · have hpos : 0 < ((1 : ℕ) : ℝ≥0) * (2 / Fintype.card Gf16) := by
      rw [card_gf16]
      norm_num
    have h := lt_add_of_pos_right
      (Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8) hpos
    rw [hadd] at h
    exact_mod_cast h

example :
    Binius.FRIBinius.Unrolled.concreteErrorWithBlockSize 2
        (L := Gf16) (ℓ' := 1) (R := 1) (ϑ := 1) 8 =
      Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 := by
  have hsub : (2 : ℝ≥0) - 1 = 1 := tsub_eq_of_eq_add (by norm_num)
  norm_num [Binius.FRIBinius.Unrolled.concreteErrorWithBlockSize,
    Binius.FRIBinius.Unrolled.concreteError, CoreInteraction.foldingBlockFactor, hsub]

/-! ### The Binary Basefold final check -/

section FinalCheck
variable (mult : Multiplier Unit Gf16 1)

private theorem one_add_one_lt_two_pow_two : 1 + 1 < 2 ^ 2 := by decide

/-- A zero multiplier value does not make the final check vacuous: it requires a zero target. -/
example (h0 : ∀ r', mult.evaluate () r' = 0)
    (s : Statement (L := Gf16) Unit (Fin.last 1) × ∀ j, OracleStatement (ZMod 2) basis
      (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) 1 (Fin.last 1) j)
    (tr : (pSpecFinalSumcheckStep (L := Gf16)).FullTranscript) :
    (CoreInteraction.finalSumcheckVerifierGuardedForm (ZMod 2) basis mult (ϑ := 1)
      (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) (𝓑 := boolEmbedding Gf16)).check s tr =
      decide (s.1.sumcheck_target = 0) := by
  rw [CoreInteraction.finalSumcheckVerifierGuardedForm_check, h0]
  exact decide_eq_decide.mpr ⟨fun h => h.trans (zero_mul _), fun h => h.trans (zero_mul _).symm⟩

/-- At `evalMultiplier`, the final check is the evaluation-claim check `s = eq̃(r, r') · c`. -/
example (s : Statement (L := Gf16) (SumcheckBaseContext Gf16 1) (Fin.last 1) ×
      ∀ j, OracleStatement (ZMod 2) basis
        (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) 1 (Fin.last 1) j)
    (tr : (pSpecFinalSumcheckStep (L := Gf16)).FullTranscript) :
    (CoreInteraction.finalSumcheckVerifierGuardedForm (ZMod 2) basis evalMultiplier (ϑ := 1)
      (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) (𝓑 := boolEmbedding Gf16)).check s tr =
      decide (s.1.sumcheck_target =
        eqTilde s.1.ctx.t_eval_point s.1.challenges * (show Gf16 from tr.messages ⟨0, rfl⟩)) :=
  CoreInteraction.finalSumcheckVerifierGuardedForm_check (ZMod 2) basis evalMultiplier s tr

end FinalCheck

end ArkLibTest.FRIBinius.Unrolled

/-! ### A ground field larger than the prime field -/

namespace ArkLibTest.FRIBinius.NonBitGroundField

open ConcreteBinaryTower
open scoped Binius.FRIBinius

private abbrev K := ConcreteBTField 1
private abbrev L := ConcreteBTField 3

local instance : Algebra K L := ConcreteBTFieldAlgebra (h_le := by decide)
local instance : Fintype L := (getBTFResult 3).instFintype
local instance : SampleableType L := SampleableType.ofFintype L

private def basis : Basis (Fin (2 ^ 2)) K L := multilinearBasis 1 3 (by decide)

private theorem card_extension : Fintype.card L = 256 :=
  (getBTFResult 3).fieldFintypeCard.trans (by norm_num)

private def rawDomainBasis : Basis (Fin 8) (ZMod 2) L :=
  Module.finBasisOfFinrankEq (ZMod 2) L (by
    apply Nat.pow_right_injective (show 2 ≤ (2 : ℕ) by decide)
    simpa [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := L)).symm.trans card_extension)

private def domainBasis : Basis (Fin 8) (ZMod 2) L :=
  rawDomainBasis.map ((Units.mk0 (rawDomainBasis 0) (rawDomainBasis.ne_zero 0)).mulLeftLinearEquiv
    (ZMod 2) L).symm

local instance : Fact (domainBasis 0 = 1) := ⟨by
  change ((Units.mk0 (rawDomainBasis 0) (rawDomainBasis.ne_zero 0)).mulLeftLinearEquiv
    (ZMod 2) L).symm (rawDomainBasis 0) = 1
  rw [Units.symm_mulLeftLinearEquiv_apply]
  simp [rawDomainBasis.ne_zero]⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨dvd_refl 1⟩

private theorem hrate : 1 + 1 < 8 := by decide
private theorem hdim : 3 = 1 + 2 := rfl
private abbrev profile := Binius.FRIBinius.biniusProfile 2 L K basis
private abbrev interface :=
  Binius.FRIBinius.RingSwitch.inputInterface domainBasis (ℓ' := 1) (R := 1) (ϑ := 1) hrate
private abbrev modularVerifier :=
  Binius.FRIBinius.RingSwitch.fullVerifier 2 K basis domainBasis
    (ℓ' := 1) (R := 1) (ϑ := 1) hrate hdim 8
private abbrev unrolledVerifier :=
  Binius.FRIBinius.Unrolled.fullVerifier 2 K basis domainBasis
    (ℓ' := 1) (R := 1) (ϑ := 1) hrate hdim 8

example : Fintype.card K = 4 := (getBTFResult 1).fieldFintypeCard

/-- Both verifiers have round-by-round knowledge soundness for the same input relation over
the four-element ground field. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (modularVerifier.toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn profile hdim interface) acceptRejectOracleRel
      (Binius.FRIBinius.RingSwitch.fullError 2 K basis domainBasis
        (ℓ' := 1) (R := 1) (ϑ := 1) hrate 8) ∧
    (unrolledVerifier.toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn profile hdim interface) acceptRejectOracleRel
      (Binius.FRIBinius.Unrolled.fullError 2 K basis domainBasis
        (ℓ' := 1) (R := 1) (ϑ := 1) hrate 8) :=
  ⟨Binius.FRIBinius.RingSwitch.fullVerifier_rbrKnowledgeSoundness 2 K basis domainBasis
      (ℓ' := 1) (R := 1) (ϑ := 1) hrate hdim 8 init impl,
    Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness 2 K basis domainBasis
      (ℓ' := 1) (R := 1) (ϑ := 1) hrate hdim 8 init impl⟩

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
      (oracleProof := Binius.FRIBinius.Unrolled.fullReduction 2 K basis domainBasis
        (ℓ' := 1) (R := 1) (ϑ := 1) hrate hdim 8)
      (relation := TensorPrefix.relIn profile hdim interface.strictView)
      (init := init) (impl := impl) ∧
    OracleProof.knowledgeSoundness init impl (TensorPrefix.relIn profile hdim interface)
      unrolledVerifier
      (Binius.FRIBinius.Unrolled.concreteError 2 (L := L) (ℓ' := 1) (R := 1) 8) :=
  Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness_and_knowledgeSoundness
    2 K basis domainBasis (ℓ' := 1) (R := 1) (ϑ := 1) hrate hdim 8 init impl

example :
    Binius.FRIBinius.RingSwitch.concreteError 2 (L := L) (ℓ' := 1) (R := 1) 8 < 1 ∧
    Binius.FRIBinius.Unrolled.concreteError 2 (L := L) (ℓ' := 1) (R := 1) 8 < 1 := by
  constructor
  · norm_num [Binius.FRIBinius.RingSwitch.concreteError,
      Binius.BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError, card_extension]
  · norm_num [Binius.FRIBinius.Unrolled.concreteError, card_extension]

/-! ### Two folds per block with more domain vectors than packing vectors -/

local instance : Fact ((2 : ℕ) ∣ 2) := ⟨dvd_refl 2⟩

private theorem twoFoldsRate : 2 + 2 < 8 := by decide
private theorem twoFoldsDim : 4 = 2 + 2 := rfl
private abbrev twoFoldsRelation :=
  TensorPrefix.relIn profile twoFoldsDim
    (Binius.FRIBinius.binaryBasefoldInput L domainBasis 2 2 2 twoFoldsRate)
private abbrev twoFoldsVerifier :=
  Binius.FRIBinius.Unrolled.fullVerifier 2 K basis domainBasis
    (ℓ' := 2) (R := 2) (ϑ := 2) twoFoldsRate twoFoldsDim 8

/-- The modular opening also accepts this choice, which violates the old
requirement `ℓ' + R < 2 ^ κ`. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness 2 K basis domainBasis
    (ϑ := 2) twoFoldsRate twoFoldsDim 8 init impl

/-- Ordinary security at the sharper bound for two folds per block over a non-bit ground field. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let err := Binius.FRIBinius.Unrolled.concreteErrorWithBlockSize 2
      (L := L) (ℓ' := 2) (R := 2) (ϑ := 2) 8
    OracleProof.knowledgeSoundness init impl twoFoldsRelation twoFoldsVerifier err ∧
      OracleProof.soundness init impl twoFoldsRelation.language twoFoldsVerifier err :=
  ⟨Binius.FRIBinius.Unrolled.fullVerifier_knowledgeSoundness_withBlockSize 2 K basis domainBasis
      twoFoldsRate twoFoldsDim 8 init impl,
    Binius.FRIBinius.Unrolled.fullVerifier_soundness_withBlockSize 2 K basis domainBasis
      twoFoldsRate twoFoldsDim 8 init impl⟩

example :
    let err := Binius.FRIBinius.Unrolled.concreteErrorWithBlockSize 2
      (L := L) (ℓ' := 2) (R := 2) (ϑ := 2) 8
    err = 6 / 256 + (2 / 3 : ℝ≥0) * (16 / 256) + (5 / 8 : ℝ≥0) ^ 8 ∧
      err < Binius.FRIBinius.Unrolled.concreteError 2 (L := L) (ℓ' := 2) (R := 2) 8 ∧
      err < 1 := by
  have hsub : (4 : ℝ≥0) - 1 = 3 := tsub_eq_of_eq_add (by norm_num)
  norm_num [Binius.FRIBinius.Unrolled.concreteErrorWithBlockSize,
    Binius.FRIBinius.Unrolled.concreteError, CoreInteraction.foldingBlockFactor, card_extension,
    hsub]

end ArkLibTest.FRIBinius.NonBitGroundField

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness_and_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness_and_knowledgeSoundness

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullVerifier_soundness

/--
info: 'Binius.FRIBinius.Unrolled.fullError_sum_le_concrete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullError_sum_le_concrete

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_knowledgeSoundness_withBlockSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullVerifier_knowledgeSoundness_withBlockSize

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_soundness_withBlockSize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullVerifier_soundness_withBlockSize
