module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.AutomorphicForms.ReductionMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.WhitCont

open GroundTheory.Automorphic.FourierWhittaker

theorem continuous_whit : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  intro E _ _ a F hF ⟨C, hC⟩
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hψ : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hj : Continuous fun p : GA E a × (Pos a → Ad E) =>
      F (uGL p.2 * p.1) * (GroundTheory.Global.adelicChar E (-supSum 0 p.2) : ℂ) :=
    (hF.comp ((continuous_uGL.comp continuous_snd).mul continuous_fst)).mul (hψ.comp continuous_snd)
  have e : GlobalTheory.JSW.whit F = fun g => ∫ X, F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂μ := rfl
  rw [e]

  refine continuous_of_dominated (bound := fun _ => C) (fun g => ?_) (fun g => ?_) (integrable_const C) ?_
  · have h1 : Continuous fun X : Pos a → Ad E => (g, X) := continuous_const.prodMk continuous_id
    exact (hj.comp h1).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact hC _
  · refine Filter.Eventually.of_forall fun X => ?_
    exact (hF.comp (continuous_const.mul continuous_id)).mul continuous_const

end GlobalTheory.JSW.WhitCont
