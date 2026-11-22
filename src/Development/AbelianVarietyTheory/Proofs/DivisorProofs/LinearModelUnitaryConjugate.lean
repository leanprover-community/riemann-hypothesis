module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinWShape

theorem frob_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m m K) (Y : Matrix m n K) (B : Matrix n n K) (P : Matrix m n K) :
    ∑ k, ∑ l, (A * Y * B) k l * P k l = ∑ k, ∑ l, Y k l * (Aᵀ * P * Bᵀ) k l := by
  have e : ∀ M Q : Matrix m n K, ∑ k, ∑ l, M k l * Q k l = Matrix.trace (M * Qᵀ) := by
    intro M Q
    simp [Matrix.trace, Matrix.mul_apply]
  rw [e, e, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    show A * Y * B * Pᵀ = A * (Y * B * Pᵀ) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Matrix.transpose_transpose]

theorem linForm_eq {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) :
    l Y = ∑ k, ∑ j, Y k j * l (Matrix.single k j 1) := by
  conv_lhs => rw [Y.matrix_eq_sum_single]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single k j (Y k j) = Y k j • Matrix.single k j (1 : K) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

end GlobalTheory.LinWShape

namespace GlobalTheory.LinWShape

end GlobalTheory.LinWShape
