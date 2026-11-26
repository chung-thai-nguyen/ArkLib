/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Security
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# Binary Basefold: the core interaction

The core interaction of the Binary Basefold evaluation IOP. Both parties hold the oracle `[f]`,
the claimed sum `s` and the evaluation point `r = (r₀, …, r_{ℓ-1})`; the prover also holds the
multilinear `t` with `f` its encoding. For a public multilinear multiplier `A` from the context,
the prover writes `h(X) := A(X) · t(X)`; an evaluation claim uses `A(X) = eq̃(r, X)`. Starting from
`f⁽⁰⁾ := f` and `s₀ := s`, for each `i < ℓ` the prover sends the round polynomial `hᵢ(X)`, the
verifier checks `sᵢ = hᵢ(0) + hᵢ(1)`, samples `r'ᵢ` and sets `sᵢ₊₁ := hᵢ(r'ᵢ)`, and the prover
folds `f⁽ⁱ⁾` along `r'ᵢ`, committing the folded word whenever `ϑ ∣ i + 1 < ℓ`. Finally the prover
sends the constant `c := f⁽ˡ⁾(0, …, 0)` and the verifier checks `s_ℓ = A(r') · c`, computing
`A(r')` with the multiplier's evaluator.

## Main definitions and statements

* `coreInteractionOracleVerifier`, `coreInteractionOracleReduction`: the sum-check-and-fold rounds
  (`sumcheckFoldOracleVerifier`) followed by the final sum-check step, for a `Multiplier` over an
  arbitrary context. `Opening` instantiates it with `evalMultiplier`; the unrolled FRI-Binius
  protocol with the ring-switching multiplier.
* `coreInteractionOracleReduction_perfectCompleteness`: perfect completeness from the strict round
  relation at round `0` to the strict final sum-check output relation.
* `coreInteractionOracleVerifier_rbrKnowledgeSoundness`: round-by-round
  knowledge soundness from the round relation at round `0` to the final sum-check output
  relation, with error `coreInteractionOracleRbrKnowledgeError`; guarded by the checks of the
  sum-check-and-fold rounds (`sumcheckFoldOracleVerifierGuardedForm`).
* `sumcheckFoldKnowledgeError_le_geometric`: the challenge errors sum to at most
  `2ℓ / |L| + (ϑ / (2^ϑ - 1)) · 2^(ℓ + 𝓡) / |L|`. Each challenge pays `2 / |L|`
  for sumcheck and `|S⁽ᵏ⁾| / |L|` for folding, where `k` is the end of its block.
  `sumcheckFoldKnowledgeError_le` uses the simpler coefficient `1` for the folding term.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The core interaction is steps 1–3 of the evaluation IOP of Construction 4.12. The bad-event part
  of `sumcheckFoldKnowledgeError_le_geometric` uses the geometric sum in Proposition 4.23.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

omit [Fintype 𝔽q] in
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩

variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section CoreInteractionPhaseReduction
variable {Context : Type} (multiplier : Multiplier Context L ℓ)

/-- The oracle verifier of the core interaction: the sum-check-and-fold rounds, then the final
sum-check step. -/
@[reducible]
def coreInteractionOracleVerifier :
    OracleVerifier []ₒ
      (Statement (L := L) (ℓ := ℓ) Context 0)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append
    (sumcheckFoldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multiplier.polynomial))
    (finalSumcheckVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑))

/-- The oracle reduction of the core interaction. -/
@[reducible]
def coreInteractionOracleReduction :
    OracleReduction []ₒ
      (Statement (L := L) (ℓ := ℓ) Context 0)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
      (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      Unit
      (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append
    (sumcheckFoldOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multiplier.polynomial))
    (finalSumcheckOracleReduction 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] in
/-- Perfect completeness of the core interaction, from the strict round relation at round `0` to
the strict final sum-check output relation. -/
theorem coreInteractionOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (multpoly := multiplier.polynomial) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction 𝔽q β multiplier (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (init := init) (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (sumcheckFoldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial))
    (finalSumcheckVerifierGuardedForm 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (fun _ => Or.inl inferInstance)
    (sumcheckFoldOracleReduction_perfectCompleteness 𝔽q β)
    (fun s => finalSumcheckOracleReduction_perfectCompleteness 𝔽q β multiplier (pure s) impl)

/-- The round-by-round knowledge error of the core interaction: that of the sum-check-and-fold
rounds. The final sum-check step has no challenge. -/
def coreInteractionOracleRbrKnowledgeError :
    (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx →
      ℝ≥0 :=
  Sum.elim (sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (finalSumcheckKnowledgeError (L := L)) ∘ ChallengeIdx.sumEquiv.symm

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the core interaction, from the round relation
at round `0` to the final sum-check output relation, with error
`coreInteractionOracleRbrKnowledgeError`. -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundness init impl
      (roundRelation (multpoly := multiplier.polynomial) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first _ _
    (sumcheckFoldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial))
    (sumcheckFoldOracleVerifier_rbrKnowledgeSoundness 𝔽q β)
    (finalSumcheckOracleVerifier_rbrKnowledgeSoundness 𝔽q β multiplier init impl)

/-! ### The total round-by-round knowledge error of the sum-check-and-fold rounds -/

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The fold step's error at round `i`, through the end `⌊i / ϑ⌋ · ϑ + ϑ` of its block: the
Schwartz–Zippel term plus `2^(ℓ + 𝓡 - (⌊i / ϑ⌋ · ϑ + ϑ)) / |L|`. -/
private lemma foldKnowledgeError_eq (i : Fin ℓ) (k : (pSpecFold (L := L)).ChallengeIdx) :
    foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i k =
      2 / (Fintype.card L : ℝ≥0) +
        (2 ^ (ℓ + 𝓡 - (i / ϑ * ϑ + ϑ)) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  have hidx : (getLastOracleDomainIndex ℓ ϑ i.castSucc).val = i / ϑ * ϑ :=
    getLastOracleDomainIndex_castSucc_val ℓ ϑ i
  have hlt : (getLastOracleDomainIndex ℓ ϑ i.castSucc).val + ϑ < ℓ + 𝓡 :=
    lt_of_le_of_lt (getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc)
      (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))
  have hcard : Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate
      ⟨(getLastOracleDomainIndex ℓ ϑ i.castSucc).val + ϑ, by omega⟩) =
        2 ^ (ℓ + 𝓡 - (i / ϑ * ϑ + ϑ)) :=
    (sDomain_card 𝔽q β h_ℓ_add_R_rate _ hlt).trans (by rw [hF₂.out, Fin.val_mk, hidx])
  unfold foldKnowledgeError
  dsimp only
  rw [(Fintype.card_congr' rfl).trans hcard]
  push_cast
  rfl

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [SampleableType L] [NeZero 𝓡] in
/-- The fold step has a single challenge. -/
private lemma sum_foldKnowledgeError (i : Fin ℓ) :
    ∑ k, foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i k =
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, rfl⟩ :=
  Fintype.sum_eq_single ⟨1, rfl⟩ fun ⟨k, hk⟩ hne => (hne (by
    fin_cases k
    · simp at hk
    · rfl)).elim

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [SampleableType L] [NeZero 𝓡] in
private lemma sum_foldRelayKnowledgeError (i : Fin ℓ) :
    ∑ k, foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i k =
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, rfl⟩ := by
  rw [foldRelayKnowledgeError, ChallengeIdx.sum_sumElim_comp_sumEquiv_symm, sum_foldKnowledgeError,
    Fintype.sum_empty, add_zero]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [SampleableType L] [NeZero 𝓡] in
private lemma sum_foldCommitKnowledgeError (i : Fin ℓ) :
    ∑ k, foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i k =
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, rfl⟩ := by
  rw [foldCommitKnowledgeError, ChallengeIdx.sum_sumElim_comp_sumEquiv_symm, sum_foldKnowledgeError,
    Fintype.sum_empty, add_zero]

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The challenges of the `bIdx`-th non-last block carry, in total, `ϑ` times the fold step's
error at the block's end `bIdx · ϑ + ϑ`. -/
private lemma sum_nonLastSingleBlockRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1)) :
    ∑ k, nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx k =
      ϑ * (2 / (Fintype.card L : ℝ≥0) +
        (2 ^ (ℓ + 𝓡 - (bIdx * ϑ + ϑ)) : ℝ≥0) / (Fintype.card L : ℝ≥0)) := by
  have hdiv_eq (x : ℕ) (hx : x < ϑ) : (bIdx.val * ϑ + x) / ϑ = bIdx := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_neZero ϑ), Nat.div_eq_of_lt hx,
      zero_add]
  have hrelay : ∑ k, nonLastSingleBlockFoldRelayRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx k =
      ∑ x : Fin (ϑ - 1), ∑ k, foldRelayKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + x, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx x⟩ k :=
    sum_seqComposeChallengeIdxToSigma (pSpec := fun _ => pSpecFoldRelay (L := L))
      (fun x k => foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + x, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx x⟩ k)
  rw [nonLastSingleBlockRbrKnowledgeError, ChallengeIdx.sum_sumElim_comp_sumEquiv_symm, hrelay]
  refine (congrArg₂ (· + ·) (Finset.sum_congr rfl fun x _ => sum_foldRelayKnowledgeError 𝔽q β _)
    (sum_foldCommitKnowledgeError 𝔽q β _)).trans ?_
  simp only [foldKnowledgeError_eq,
    hdiv_eq _ (Nat.sub_one_lt (NeZero.ne ϑ)),
    hdiv_eq _ (lt_of_lt_of_le (Fin.is_lt _) (Nat.sub_le ϑ 1)), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← add_one_mul, ← Nat.cast_add_one, Nat.sub_add_cancel NeZero.one_le]

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The challenges of the last block carry, in total, `ϑ` times the fold step's error at round
`ℓ`, the end of the block. -/
private lemma sum_lastBlockRbrKnowledgeError :
    ∑ k, lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k =
      ϑ * (2 / (Fintype.card L : ℝ≥0) +
        (2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) : ℝ≥0) / (Fintype.card L : ℝ≥0)) := by
  have hdiv_eq (x : Fin ϑ) : ((ℓ / ϑ - 1) * ϑ + x) / ϑ = ℓ / ϑ - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_neZero ϑ), Nat.div_eq_of_lt x.isLt,
      zero_add]
  refine ((sum_seqComposeChallengeIdxToSigma (pSpec := fun _ => pSpecFoldRelay (L := L))
    (fun x k => foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨(ℓ / ϑ - 1) * ϑ + x, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ x⟩ k)).trans
    (Finset.sum_congr rfl fun x _ => sum_foldRelayKnowledgeError 𝔽q β _)).trans ?_
  simp only [foldKnowledgeError_eq, hdiv_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The challenges of the non-last blocks carry, in total, `ϑ` times the fold step's error at
each block's end. -/
private lemma sum_nonLastBlocksRbrKnowledgeError :
    ∑ k, nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k =
      ∑ bIdx : Fin (ℓ / ϑ - 1), ϑ * (2 / (Fintype.card L : ℝ≥0) +
        (2 ^ (ℓ + 𝓡 - (bIdx * ϑ + ϑ)) : ℝ≥0) / (Fintype.card L : ℝ≥0)) :=
  (sum_seqComposeChallengeIdxToSigma
    (pSpec := fun bIdx => pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))).trans
    (Finset.sum_congr rfl fun bIdx _ => sum_nonLastSingleBlockRbrKnowledgeError 𝔽q β bIdx)

/-- The geometric-series coefficient `ϑ / (2^ϑ - 1)` in the aggregate folding bound. -/
def foldingBlockFactor (ϑ : ℕ) : ℝ≥0 :=
  (ϑ : ℝ≥0) / ((2 : ℝ≥0) ^ ϑ - 1)

theorem foldingBlockFactor_le_one (ϑ : ℕ) : foldingBlockFactor ϑ ≤ 1 := by
  have h : (ϑ : ℝ≥0) + 1 ≤ 2 ^ ϑ := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := ϑ))
  exact div_le_one_of_le₀ (le_tsub_of_add_le_right h) zero_le

/-- The sizes of the block-end domains form a geometric series with ratio `2^ϑ` in reverse order. -/
private lemma sum_two_pow_sub_le (B ϑ R : ℕ) [NeZero ϑ] :
    (∑ b ∈ range B, (2 : ℝ≥0) ^ (B * ϑ + R - (b * ϑ + ϑ))) ≤
      (2 : ℝ≥0) ^ (B * ϑ + R) / ((2 : ℝ≥0) ^ ϑ - 1) := by
  have hterm (b : ℕ) (hb : b ∈ range B) :
      (2 : ℝ≥0) ^ (B * ϑ + R - (b * ϑ + ϑ)) = 2 ^ R * (2 ^ ϑ) ^ (B - 1 - b) := by
    rw [mem_range] at hb
    rw [← pow_mul, ← pow_add]
    congr 1
    have h2 : (B - 1 - b) * ϑ + (b * ϑ + ϑ) = B * ϑ := by
      rw [← Nat.succ_mul, ← Nat.add_mul]
      congr 1
      omega
    rw [mul_comm ϑ]
    omega
  rw [sum_congr rfl hterm, ← mul_sum, sum_range_reflect (fun u => (2 ^ ϑ) ^ u) B]
  have hbase : (1 : ℝ≥0) < 2 ^ ϑ := one_lt_pow₀ (by norm_num) (NeZero.ne ϑ)
  have hgeom := geom_sum_mul_add ((2 : ℝ≥0) ^ ϑ - 1) B
  rw [tsub_add_cancel_of_le hbase.le, ← pow_mul, mul_comm ϑ B] at hgeom
  rw [le_div_iff₀ (tsub_pos_of_lt hbase), mul_assoc, add_comm (B * ϑ) R, pow_add]
  gcongr
  rw [← hgeom]
  exact le_self_add

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The challenge-error sum retains the geometric-series coefficient `ϑ / (2^ϑ - 1)`
on the folding term. -/
theorem sumcheckFoldKnowledgeError_le_geometric :
    (∑ j : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        sumcheckFoldKnowledgeError (L := L) 𝔽q β j)
      ≤ 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
        + foldingBlockFactor ϑ * ((2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)) := by
  have hB : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have hB1 : 1 ≤ ℓ / ϑ :=
    Nat.div_pos (blockSize_le_rounds ℓ ϑ) (Nat.pos_of_neZero ϑ)
  set f : ℕ → ℝ≥0 := fun b => ϑ * (2 / (Fintype.card L : ℝ≥0) +
    (2 ^ (ℓ + 𝓡 - (b * ϑ + ϑ)) : ℝ≥0) / (Fintype.card L : ℝ≥0))
  have hsplit : ∑ j : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
      sumcheckFoldKnowledgeError (L := L) 𝔽q β j = ∑ b ∈ range (ℓ / ϑ), f b := by
    rw [sumcheckFoldKnowledgeError, ChallengeIdx.sum_sumElim_comp_sumEquiv_symm,
      sum_nonLastBlocksRbrKnowledgeError, sum_lastBlockRbrKnowledgeError,
      Fin.sum_univ_eq_sum_range (fun b => f b), ← Finset.sum_range_succ,
      Nat.sub_add_cancel hB1]
  rw [hsplit]
  have hnum : ∑ b ∈ range (ℓ / ϑ), f b =
      ((∑ b ∈ range (ℓ / ϑ), (2 * ϑ + ϑ * 2 ^ (ℓ + 𝓡 - (b * ϑ + ϑ))) : ℕ) : ℝ≥0) /
        (Fintype.card L : ℝ≥0) := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hrounds : (↑(ℓ / ϑ) : ℝ≥0) * ϑ = ℓ := by exact_mod_cast hB
  have hfold := sum_two_pow_sub_le (ℓ / ϑ) ϑ 𝓡
  rw [hB] at hfold
  rw [hnum, ← mul_div_assoc, ← add_div]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ zero_le
  refine add_le_add ?_ ?_
  · rw [mul_left_comm, hrounds]
  · simpa only [foldingBlockFactor, div_mul_eq_mul_div, ← mul_div_assoc] using
      mul_le_mul_of_nonneg_left hfold (show 0 ≤ (ϑ : ℝ≥0) from zero_le)

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The challenge-error sum is at most `2ℓ / |L| + 2^(ℓ + 𝓡) / |L|`. -/
theorem sumcheckFoldKnowledgeError_le :
    (∑ j : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        sumcheckFoldKnowledgeError (L := L) 𝔽q β j)
      ≤ 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
        + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) :=
  (sumcheckFoldKnowledgeError_le_geometric 𝔽q β).trans <|
    add_le_add le_rfl (mul_le_of_le_one_left zero_le (foldingBlockFactor_le_one ϑ))

omit [DecidableEq 𝔽q] in
/-- Ordinary knowledge soundness of the core interaction, with the sum of its challenge errors. -/
theorem coreInteractionOracleVerifier_knowledgeSoundness :
    (coreInteractionOracleVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).knowledgeSoundness init impl
      (roundRelation (multpoly := multiplier.polynomial) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (∑ i, coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleVerifier.knowledgeSoundness_of_rbrKnowledgeSoundness_of_guarded
    (Verifier.GuardedForm.ofEmpty _ (fun _ =>
      (⟨0, fun _ => 0, 0⟩, fun _ _ => 0)))
    (coreInteractionOracleVerifier_rbrKnowledgeSoundness 𝔽q β multiplier)

omit [DecidableEq 𝔽q] in
/-- The core interaction is perfectly complete on exact encodings and ordinarily
knowledge sound for unique-radius compatibility. -/
theorem coreInteractionOracleReduction_perfectCompleteness_and_knowledgeSoundness :
    OracleReduction.perfectCompleteness
      (oracleReduction := coreInteractionOracleReduction 𝔽q β multiplier (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (relIn := strictRoundRelation (multpoly := multiplier.polynomial) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (init := init) (impl := impl) ∧
    (coreInteractionOracleVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).knowledgeSoundness init impl
      (roundRelation (multpoly := multiplier.polynomial) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (∑ i, coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  ⟨coreInteractionOracleReduction_perfectCompleteness 𝔽q β multiplier,
    coreInteractionOracleVerifier_knowledgeSoundness 𝔽q β multiplier⟩

end CoreInteractionPhaseReduction

end
end Binius.BinaryBasefold.CoreInteraction
