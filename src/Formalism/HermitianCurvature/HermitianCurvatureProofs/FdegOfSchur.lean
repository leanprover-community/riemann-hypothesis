module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem one_mem_uh : (1 : Mx k r) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_DD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {t : Mx k r} (ht : t ∈ UH (Hpk k r)) : σ t w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨t, ht, rfl⟩

theorem fdeg_of_schur {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} {w0 : H} (hw : w0 ≠ 0) {d : ℝ} (hd : 0 < d)
    (hS : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪w0, w0⟫_ℂ * ⟪w0, w0⟫_ℂ / (d : ℂ)) :
    PI.BesselPeriodGGP.fdegH μG σ w0 = d := by

  have hpt : ∀ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ =
      ((‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [show star ⟪w0, σ (Matrix.of x) w0⟫_ℂ = (starRingEnd ℂ) ⟪w0, σ (Matrix.of x) w0⟫_ℂ from rfl,
      RCLike.mul_conj]
    norm_cast
  simp_rw [hpt] at hS
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hS
  have hI : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have h2 : ((‖w0‖ ^ 4 / d : ℝ) : ℂ) = (‖w0‖ : ℂ) ^ 2 * (‖w0‖ : ℂ) ^ 2 / (d : ℂ) := by
      push_cast; ring
    exact_mod_cast hS.trans h2.symm
  have hw' : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [PI.BesselPeriodGGP.fdegH]
  rw [hI]
  field_simp

end Formalism.FourierDecayAlt.P.S3dx6
