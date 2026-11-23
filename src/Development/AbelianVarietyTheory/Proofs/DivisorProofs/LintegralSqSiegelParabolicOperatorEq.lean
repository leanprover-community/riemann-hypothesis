module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_lintegral_sq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ _ hψ1 _ χ _ hres _ _ μ _ p hp φ
  obtain ⟨h1, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  obtain ⟨-, htop, -, -, -, -, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, -, -, hnorm, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have h1' := mul_eq_one_comm.mp h1
  let A : GL ν E := ⟨(mat c p).toBlocks₁₁, _, h1, h1'⟩
  have hA : ((A : GL ν E) : Matrix ν ν E) = (mat c p).toBlocks₁₁ := rfl
  set D : NNReal := distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) with hD
  have hD0 : D ≠ 0 := distribHaarChar_pos.ne'
  have hsc : ‖sc F χ (Fintype.card α) (mat c p).toBlocks₁₁.det‖ₑ ^ 2 = ((D ^ Fintype.card α : NNReal) : ENNReal) := by
    have := hnorm (Matrix.GeneralLinearGroup.det A)
    have hd : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = (mat c p).toBlocks₁₁.det := rfl
    rw [hd] at this
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.eq
    push_cast
    rw [this]
    rfl
  have hpt : ∀ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 =
      ((D ^ Fintype.card α : NNReal) : ENNReal) * ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 := by
    intro x
    have hψe : ∀ t, ‖ψ t‖ₑ = 1 := fun t => by
      rw [enorm_eq_nnnorm]; simp [← NNReal.coe_eq_one, coe_nnnorm, hψ1 t]
    simp only [parFun, enorm_mul, hψe, one_mul, mul_pow, hsc, hA]
  haveI := htop
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * (A : Matrix ν ν E)
      invFun := fun x => x * ((A⁻¹ : GL ν E) : Matrix ν ν E)
      left_inv := fun x => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  have hmap : μ.map (e.toMeasurableEquiv) = ((D ^ Fintype.card α)⁻¹ : NNReal) • μ := by
    have := GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ 1 A
    have hf : (fun x : Matrix α ν E => ((1 : GL α E) : Matrix α α E) * x * (A : Matrix ν ν E)) = e.toMeasurableEquiv := by
      funext x; simp [e]
    rw [hf] at this
    rw [this, ← hD]
    simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hl := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) e.toMeasurableEquiv (μ := μ)
  have hl' : ∫⁻ x, ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(μ.map e.toMeasurableEquiv) := hl.symm
  rw [hl', hmap, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hD0), ENNReal.coe_one, one_mul]

end GlobalTheory.KSp
