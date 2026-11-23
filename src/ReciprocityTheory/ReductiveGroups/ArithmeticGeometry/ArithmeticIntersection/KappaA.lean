module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace ReciprocityTheory.ChartRestriction.G.AI

theorem cone_preimage (L : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((fun n : S2 => (⟨L n, by simp⟩ : S2)) ⁻¹' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E3)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, _, ⟨_, hn, rfl⟩, by simp⟩
  · rintro ⟨r, hr, _, ⟨m, hm, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨L.symm m, by simp⟩, ?_, rfl⟩, ?_⟩
    · convert hm using 1
      ext
      simp
    · apply L.injective
      rw [← hx]
      simp

theorem measurable_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable

theorem toSphere_measurePreserving (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2))
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by
  refine ⟨measurable_sphereMap L, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_sphereMap L) hs, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ (measurable_sphereMap L hs), cone_preimage]
  congr 1
  have hmp : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E3) volume :=
    L.measurePreserving
  exact hmp.measure_preimage_equiv _

theorem sphereInv_thm : SphereInvStatement := by
  refine ⟨?_, fun L => ?_⟩
  · have h1 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
      rw [Measure.toSphere_apply_univ]
      refine mul_ne_zero (by simp) ?_
      exact (Metric.measure_ball_pos _ _ one_pos).ne'
    have h2 : (volume : Measure E3).toSphere Set.univ ≠ ⊤ := measure_ne_top _ _
    constructor
    rw [sphereMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h1 h2]
  · have hL := toSphere_measurePreserving L
    refine ⟨hL.measurable, ?_⟩
    rw [sphereMeasure, Measure.map_smul _ hL.measurable.aemeasurable, hL.map_eq]

end ReciprocityTheory.ChartRestriction.G.AI
