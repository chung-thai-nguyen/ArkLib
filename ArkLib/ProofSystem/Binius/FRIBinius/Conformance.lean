/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch
public import ArkLib.ProofSystem.RingSwitching.Packing.Conformance

/-!
# Binius source and oracle conformance

The shared prefix frontend uses the source polynomial's basis packing and the original
first-codeword oracle. Every source polynomial has an honest input with exact first encoding;
the relaxed input relation uses the same packed polynomial with unique-radius compatibility.
-/

@[expose] public section

noncomputable section
namespace Binius.FRIBinius.Conformance
open Module MvPolynomial RingSwitching RingSwitching.Packing Sumcheck.Structured
open scoped Binius.FRIBinius

variable (κ : ℕ) {L : Type} [Field L] [Fintype L] [DecidableEq L]
  (K : Type) [Field K] [Algebra K L] (β : Basis (Fin (2 ^ κ)) K L)
variable [Algebra (ZMod 2) L] {r : ℕ} [NeZero r] (b : Basis (Fin r) (ZMod 2) L)
variable {ℓ ℓ' R ϑ : ℕ} [NeZero ℓ'] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
  (h_rate : ℓ' + R < r) (h_dim : ℓ = ℓ' + κ)

/-- The scalar source claim and the packed first oracle are the shared input relation. -/
theorem mem_relIn_iff (z : Fin ℓ → L) (s : L)
    (ost : ∀ j, (binaryBasefoldInput L b ℓ' R ϑ h_rate).OStmtIn j)
    (t : MultilinearPoly K ℓ) :
    (((z, s), ost), t) ∈ TensorPrefix.relIn (biniusProfile κ L K β) h_dim
        (binaryBasefoldInput L b ℓ' R ϑ h_rate) ↔
      s = aeval z t.val ∧ BinaryBasefold.FirstOracleWitnessConsistent (ZMod 2) b
        (packMLE κ L K ℓ ℓ' h_dim (biniusProfile κ L K β).basis t)
        (BinaryBasefold.getFirstOracle (ZMod 2) b ost) := by
  change (s = aeval z t.val ∧ _ ) ↔ _
  rw [TensorPrefix.packedMLE_components_eq_packMLE]
  rfl

/-- Every source polynomial and query give an honest input with the exact packed encoding. -/
theorem mem_relIn_strictView_honestPackedOracle (t : MultilinearPoly K ℓ) (z : Fin ℓ → L) :
    (((z, aeval z t.val), honestPackedOracle L b ℓ' R ϑ h_rate
        (packMLE κ L K ℓ ℓ' h_dim (biniusProfile κ L K β).basis t)), t) ∈
      TensorPrefix.relIn (biniusProfile κ L K β) h_dim
        (binaryBasefoldInput L b ℓ' R ϑ h_rate).strictView := by
  constructor
  · rfl
  · change (binaryBasefoldInput L b ℓ' R ϑ h_rate).strictInitialCompatibility
      ((PackingData.ofBasis (biniusProfile κ L K β).basis).packedMLE
        ((TensorPrefix.layout (biniusProfile κ L K β) h_dim).components t), _)
    rw [TensorPrefix.packedMLE_components_eq_packMLE]
    exact honestPackedOracle_strictCompatible L b ℓ' R ϑ h_rate _

end Binius.FRIBinius.Conformance
