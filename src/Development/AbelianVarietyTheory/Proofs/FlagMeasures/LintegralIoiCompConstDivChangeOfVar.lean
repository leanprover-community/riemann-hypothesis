module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory

theorem lintegral_Ioi_comp_const_div_mul_div :
    ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w →
      ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t =
        ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro κ hκ w _hw
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have himg : (fun u : ℝ => κ / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hκ hu
    · intro ht
      have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
      refine ⟨κ / t, div_pos hκ ht, ?_⟩
      show κ / (κ / t) = t
      field_simp
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => κ / u) (-(κ / u ^ 2)) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hu)
    have h := ((hasDerivAt_inv hu0).const_mul κ).hasDerivWithinAt (s := Set.Ioi (0 : ℝ))
    have hfun : (fun u : ℝ => κ / u) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [hfun]
    exact h.congr_deriv (by ring)
  have hinj : Set.InjOn (fun u : ℝ => κ / u) (Set.Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hab' : κ / a = κ / b := hab
    field_simp at hab'
    exact hab'.symm
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj,
    himg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun u hu => ?_))
  have hu : 0 < u := Set.mem_Ioi.mp hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hκu : 0 < κ / u := div_pos hκ hu
  have hsq : 0 < u ^ 2 := by positivity
  have hinv : κ / (κ / u) = u := by field_simp
  have habs : |(-(κ / u ^ 2))| = κ / u ^ 2 := by
    rw [abs_neg, abs_of_pos (div_pos hκ hsq)]
  have hne : ENNReal.ofReal (κ / u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hκu
  simp only [hinv, habs]
  rw [ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos hsq]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory
