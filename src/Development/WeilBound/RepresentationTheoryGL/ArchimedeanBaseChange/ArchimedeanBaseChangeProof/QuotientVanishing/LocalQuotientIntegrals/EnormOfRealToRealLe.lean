module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le' (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

theorem integrable_mul {G : Type*} [MeasurableSpace G] {μ : Measure G} {F : G → ℂ}
    {ρ : G → ℝ≥0∞} (hF : Measurable F) (hρ : Measurable ρ) (h : ∫⁻ g, ‖F g‖ₑ * ρ g ∂μ ≠ ⊤) :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ := by
  refine ⟨(hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) h.lt_top
  rw [enorm_mul]
  gcongr
  exact enorm_ofReal_toReal_le' _

end QuotientIntegral

theorem pf_QAdd : QAdd := by
  intro G _ _ μ T ν
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have hL : ∀ F : G → ℂ, quotLIntegral μ T ν (fun x => ‖F x‖ₑ) =
        ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ := fun F => by rw [quotLIntegral, dite_eq_left hex]
    have hI : ∀ F : G → ℂ, quotIntegral μ T ν F =
        ∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ := fun F => by rw [quotIntegral, dite_eq_left hex]
    have hint : ∀ F : G → ℂ, Measurable F → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ →
        Integrable (fun g => F g * ((hex.choose g).toReal : ℂ)) μ := fun F hF h =>
      QuotientIntegral.integrable_mul hF hex.choose_spec.1 (by rwa [hL] at h)
    refine ⟨fun ι s F hF => ?_, fun F F' hF hF' h h' => ?_, fun c F => ?_⟩
    · simp only [hI, Finset.sum_mul]
      exact integral_finsetSum s fun i hi => hint _ (hF i hi).1 (hF i hi).2
    · simp only [hI, sub_mul]
      exact integral_sub (hint _ hF h) (hint _ hF' h')
    · simp only [hI, mul_assoc]
      exact integral_const_mul c _
  · refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ => ?_⟩ <;>
      simp [quotIntegral, hex]

end PositivityTheory.Rg.BcB.CV
