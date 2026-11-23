module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.SameOrbitOneSpecZ
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalClosedPoints.proof (hE : regularityEmbedding_holds.Statement) (hV : VerticalEmbedding.Statement) : VerticalClosedPoints.Statement := by
  intro K _ ι _ P f g a R hP hf hg hfP hgP hR hRu
  have : P.IsPrime := hP.2.1.1
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hf hg hgP
  obtain ⟨e, he⟩ := hE K ι P R hP hR hRu
  rw [hV K ι P f g a x hP hf hg hfP hgP hx]
  have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) g :=
    ⟨a, fun _ => rfl, hg, hgP⟩
  have key : ∀ t : R, Real.log ‖e t x‖ =
      Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖) := by
    intro t
    have hg0 := eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)
    rw [← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ /
    ‖eval t (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
