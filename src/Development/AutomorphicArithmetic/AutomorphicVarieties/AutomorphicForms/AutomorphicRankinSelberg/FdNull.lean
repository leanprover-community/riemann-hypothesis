module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory Set in
private theorem UpperTheory.V.Af.Rs.line_null (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]
  simp

open MeasureTheory Set in
theorem UpperTheory.V.Af.Rs.fdNull :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdNull := by
  intro _
  unfold UpperTheory.V.Af.Rs.FdNull
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  have h0 : volume (Metric.sphere (0 : ℂ) 1 ∪ ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)})) = 0 :=
    measure_union_null (Measure.addHaar_sphere _ _ _)
      (measure_union_null (UpperTheory.V.Af.Rs.line_null _) (UpperTheory.V.Af.Rs.line_null _))
  refine measure_mono_null ?_ h0
  rintro _ ⟨z, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
  by_cases hs : 1 < Complex.normSq (z : ℂ)
  · right
    have h4 : ¬ |z.re| < 1 / 2 := fun h => h3 ⟨hs, h⟩
    have h5 : |z.re| = 1 / 2 := le_antisymm h2 (not_lt.mp h4)
    exact (abs_eq (by norm_num)).mp h5
  · left
    have h5 : Complex.normSq (z : ℂ) = 1 := le_antisymm (not_lt.mp hs) h1
    rw [Complex.normSq_eq_norm_sq] at h5
    rw [mem_sphere_zero_iff_norm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5
