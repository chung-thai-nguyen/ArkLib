/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra

/-!
# FRI-Binius IOPCS Prelude
Packing uses a `K`-basis. Binary Basefold uses a separately chosen basis over `ZMod 2`.
Hypercube indices use least-significant-bit-first order.
Relaxed compatibility permits unique-radius closeness; strict compatibility requires
an exact first-codeword encoding. Functionality and honest coverage certify this oracle relation
separately from the later opening protocol.
-/

@[expose] public section

noncomputable section

namespace Binius.FRIBinius

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Sumcheck.Structured
open scoped NNReal

scoped instance instZModTwoAlgebra {L : Type} [Ring L] [CharP L 2] :
    Algebra (ZMod 2) L := ZMod.algebra L 2

scoped instance instCardZModTwo : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩

scoped instance instPrimeRingCharZModTwo : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨CharP.prime_ringChar (ZMod 2)⟩

/-- An additive-domain basis supplies the independent vectors for Binary Basefold. -/
scoped instance instBinaryBasefoldVectorsIndependent {L ι : Type} [Field L] [Algebra (ZMod 2) L]
    (b : Basis ι (ZMod 2) L) : Fact (LinearIndependent (ZMod 2) (b : ι → L)) :=
  ⟨b.linearIndependent⟩

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [Field K] [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)

/-- The canonical radix-two enumeration of the Boolean hypercube. -/
def hypercubeEquivFin : (Fin κ → Fin 2) ≃ Fin (2 ^ κ) :=
  finFunctionFinEquiv

/-- The basis reindexed by Boolean-hypercube coordinates. -/
def booleanHypercubeBasis : Basis (Fin κ → Fin 2) K L :=
  β.reindex (e := (hypercubeEquivFin κ).symm)

/-- The Binius ring-switching profile: the tensor-product profile at the Boolean-hypercube
reindexing `booleanHypercubeBasis` of `β`. -/
def biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  RingSwitching.tensorProductProfile κ K L (booleanHypercubeBasis κ L K β)

variable [Algebra (ZMod 2) L]
variable {r : ℕ} [NeZero r] (b : Basis (Fin r) (ZMod 2) L)
variable (ℓ' 𝓡 ϑ : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < r)

/-- The first-oracle interface for the chosen additive-domain basis. -/
def binaryBasefoldInput : RingSwitching.AbstractOStmtIn L ℓ' :=
  BinaryBasefold.firstOracleInterface (ZMod 2) b (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

omit [SampleableType L] [NeZero 𝓡] in
/-- Unique-radius compatibility determines the initial committed polynomial. -/
theorem binaryBasefold_initialCompatibility_functional :
    (binaryBasefoldInput L b ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Functional :=
  BinaryBasefold.firstOracleInterface_functional (ZMod 2) b ϑ

/-- Honest first-codeword oracles cover every packed polynomial. -/
def honestPackedOracle (t : MultilinearPoly L ℓ') :
    ∀ j, (binaryBasefoldInput L b ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j :=
  BinaryBasefold.honestInitialOracleStatement (ZMod 2) b ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t

omit [SampleableType L] [NeZero 𝓡] in
/-- Honest families also meet the exact encoding premise used for completeness. -/
theorem honestPackedOracle_strictCompatible (t : MultilinearPoly L ℓ') :
    (binaryBasefoldInput L b ℓ' 𝓡 ϑ h_ℓ_add_R_rate).strictInitialCompatibility
      (t, honestPackedOracle L b ℓ' 𝓡 ϑ h_ℓ_add_R_rate t) := by
  classical
  exact BinaryBasefold.firstOracleInterface_strictInitialCompatibility_honest (ZMod 2) b ϑ t

end Binius.FRIBinius
