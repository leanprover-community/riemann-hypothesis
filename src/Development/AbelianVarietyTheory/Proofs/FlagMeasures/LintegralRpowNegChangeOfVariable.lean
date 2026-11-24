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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem lintegral_rpow_neg_change_of_variable :
    ∀ (N s : ℝ), 0 < N → 0 < s → ∀ F : ℝ → ENNReal, Measurable F →
      ∫⁻ t in Set.Ioi (0 : ℝ), F ((t / s) ^ (-(1 / N))) / ENNReal.ofReal t =
        ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ENNReal.ofReal (N / τ) := by
  intro N s hN hs F _
  set a : ℝ := -(1 / N) with ha_def
  have ha : a ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero hN.ne')

  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => (t / s) ^ a) (1 / s * a * (t / s) ^ (a - 1))
        (Set.Ioi 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => y / s) (1 / s) t := (hasDerivAt_id' t).div_const s
    exact (h1.rpow_const (Or.inl (div_pos ht hs).ne')).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => (t / s) ^ a) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hxy' : (x / s) ^ a = (y / s) ^ a := hxy
    have hdiv : x / s = y / s := by
      rw [← Real.rpow_rpow_inv (div_pos hx hs).le ha, ← Real.rpow_rpow_inv (div_pos hy hs).le ha,
        hxy']
    exact (div_left_inj' hs.ne').mp hdiv
  have himage : (fun t : ℝ => (t / s) ^ a) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.rpow_pos_of_pos (div_pos ht hs) a
    · intro hτ
      refine ⟨s * τ ^ a⁻¹, mul_pos hs (Real.rpow_pos_of_pos hτ _), ?_⟩
      show (s * τ ^ a⁻¹ / s) ^ a = τ
      rw [mul_div_cancel_left₀ _ hs.ne', Real.rpow_inv_rpow (le_of_lt hτ) ha]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun τ => F τ * ENNReal.ofReal (N / τ))
  rw [himage] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := ht
  have hu : 0 < t / s := div_pos ht' hs
  have hua : 0 < (t / s) ^ a := Real.rpow_pos_of_pos hu a

  have hreal : |1 / s * a * (t / s) ^ (a - 1)| * (N / (t / s) ^ a) = t⁻¹ := by
    have hneg : 1 / s * a * (t / s) ^ (a - 1) = -(1 / s * (1 / N) * ((t / s) ^ a / (t / s))) := by
      rw [Real.rpow_sub hu, Real.rpow_one, ha_def]
      ring
    have hpos : 0 < 1 / s * (1 / N) * ((t / s) ^ a / (t / s)) :=
      mul_pos (mul_pos (one_div_pos.mpr hs) (one_div_pos.mpr hN)) (div_pos hua hu)
    rw [hneg, abs_neg, abs_of_pos hpos]
    field_simp
  dsimp only
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos ht', ← hreal,
    ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end GlobalTheory.FlagMeas
