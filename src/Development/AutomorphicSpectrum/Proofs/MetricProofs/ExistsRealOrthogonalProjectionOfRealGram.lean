module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.ProjReal

theorem orthogonal_projection_real_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      (∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0) →
      (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∀ z : Fin g → ℂ, (∀ j, (z ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∃ c : Fin k → ℝ, ∀ j, (z - ∑ i, (c i : ℂ) • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm _ u _ hproj hu z hz
  obtain ⟨c, hc⟩ := hproj z
  refine ⟨fun i => (c i).re, fun j => ?_⟩
  have h := hc j
  simp only [sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul] at h ⊢
  apply Complex.ext
  · have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu, mul_zero, sub_zero, Complex.zero_re] at h'
    simpa [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu] using h'
  · simp [Complex.sub_im, Complex.im_sum, Complex.mul_im, hu, hz]

end GlobalTheory.CompanionTheory.Ar.ProjReal
