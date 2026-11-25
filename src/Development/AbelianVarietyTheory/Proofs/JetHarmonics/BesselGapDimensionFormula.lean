module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
public import Formalism.PeriodIntegrals.BesselPeriodGGP
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNorm

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

theorem fdegHC_pos {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hab.ne (hlam h))
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

theorem quot_ae {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (hG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r)
    (hS : ∀ᵐ x ∂μS, Matrix.of x ∈ GG k r) (h0 : μS ≠ 0) : ∀ᵐ x ∂νq, Matrix.of x ∈ GG k r := by
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r} :=
    (isClosed_UH.preimage hof).measurableSet
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ).indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hm.compl
  have h1 : ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (mulMt s x) ∂μS ∂νq := hq f hfm
  have h2 : ∫⁻ x, f x ∂μG = 0 := by
    rw [hf, lintegral_indicator_one hm.compl]; exact hG
  have h3 : Measurable (fun x => ∫⁻ s, f (mulMt s x) ∂μS) :=
    (hfm.comp measurable_mulMt).lintegral_prod_left'
  rw [h2, eq_comm, lintegral_eq_zero_iff h3] at h1
  filter_upwards [h1] with x hx
  by_contra hxG
  have h4 : ∫⁻ s, f (mulMt s x) ∂μS = ∫⁻ _s, 1 ∂μS := by
    apply lintegral_congr_ae
    filter_upwards [hS] with s hs
    have : mulMt s x ∈ ({y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ GG k r}ᶜ) := by
      intro hsx
      apply hxG
      have hsx' : Matrix.of s * Matrix.of x ∈ GG k r := hsx
      have := DDSmoothness.uh_mul (uh_inv hs).1 hsx'
      rwa [← Matrix.mul_assoc, (uh_inv hs).2.2, Matrix.one_mul] at this
    rw [hf, Set.indicator_of_mem this]; rfl
  rw [h4] at hx
  simp only [lintegral_const, one_mul, Pi.zero_apply, Measure.measure_univ_eq_zero] at hx
  exact h0 hx

def kern {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (v w : R.H) (ξ : Wp)
    (y : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) : ℂ :=
  ⟪v, R.σ (Matrix.of y.1) w⟫_ℂ * star ⟪v, R.σ (Matrix.of y.2.1 * Matrix.of y.2.2 * Matrix.of y.1) w⟫_ℂ *
    (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of y.2.2) * ⟪π (Matrix.of y.2.1)⁻¹ ξ, ξ⟫_ℂ)

def good (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) :=
  {y | Matrix.of y.1 ∈ GG k r ∧ Matrix.of y.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of y.2.2 ∈ GG k r}

end GlobalTheory.BesselNorm
