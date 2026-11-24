module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem integral_count_Xi (f : Xi F → ℂ) : ∫ ξ, f ξ ∂(Measure.count : Measure (Xi F)) = ∑' ξ, f ξ := by
  by_cases hf : Summable f
  · have hi : Integrable f (Measure.count : Measure (Xi F)) := by
      rw [integrable_count_iff]
      exact summable_norm_iff.mpr hf
    rw [integral_countable hi]
    simp
  · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
    intro hi
    rw [integrable_count_iff] at hi
    exact hf (summable_norm_iff.mp hi)

theorem integral_iter_eq (S : Set {r : ℝ // 0 < r}) (hS : MeasurableSet S) {h : Pp F × Xi F → ℂ}
    (hh : Integrable h (μS F S)) :
    IntegrableOn (fun t => ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F)
        S posRealMeasure ∧
      ∫ t in S, ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F
          ∂posRealMeasure = ∫ q, h q ∂μS F S := by
  have e1 : ∀ p : Pp F, ∫ ξ, h (p, ξ) ∂(Measure.count : Measure (Xi F)) = ∑' ξ : Xi F, h (p, ξ) :=
    fun p => integral_count_Xi _
  have hG : Integrable (fun p : Pp F => ∑' ξ : Xi F, h (p, ξ))
      ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) := by
    have := hh.integral_prod_left
    simp only [e1] at this
    exact this
  refine ⟨?_, ?_⟩
  · have := hG.integral_prod_left
    exact this
  · rw [μS, integral_prod _ hh]
    simp only [e1]
    rw [integral_prod _ hG]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
