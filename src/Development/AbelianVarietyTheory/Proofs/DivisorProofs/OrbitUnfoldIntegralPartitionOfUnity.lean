module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory.OrbitUnfold

theorem hasSum_integral_translate {I : Type} [Fintype I] {U : Type} [Countable U]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : U → I → ℝ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hsum : ∀ y, HasSum (fun u => p (y - t u)) 1) (h : (I → ℝ) → E) (hh : Integrable h) :
    HasSum (fun u => ∫ y, p y • h (y + t u)) (∫ y, h y) := by
  have key : ∀ u, ∫ y, p y • h (y + t u) = ∫ y, p (y - t u) • h y := by
    intro u
    have := integral_add_right_eq_self (μ := (volume : Measure (I → ℝ)))
      (fun y => p (y - t u) • h y) (t u)
    simpa using this
  simp_rw [key]
  refine hasSum_integral_of_dominated_convergence (fun u y => p (y - t u) * ‖h y‖) ?_ ?_ ?_ ?_ ?_
  · intro u
    exact ((hp.comp (measurable_sub_const (t u))).aestronglyMeasurable).smul
      hh.aestronglyMeasurable
  · intro u
    refine ae_of_all _ (fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hp0 _)]
  · exact ae_of_all _ (fun y => ((hsum y).mul_right ‖h y‖).summable)
  · refine hh.norm.congr (ae_of_all _ (fun y => ?_))
    simp only [((hsum y).mul_right ‖h y‖).tsum_eq, one_mul]
  · refine ae_of_all _ (fun y => ?_)
    simpa using (hsum y).smul_const (h y)

theorem orbit_unfold : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ)
    (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) →
    ∀ g : (I → ℝ) → ℂ, Integrable g →
      HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧
      HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  intro I _ U _ t p hp hp0 hsum g hg
  refine ⟨?_, ?_⟩
  · have := hasSum_integral_translate t p hp hp0 hsum g hg
    simpa [Complex.real_smul] using this
  · have := hasSum_integral_translate t p hp hp0 hsum (fun y => ‖g y‖) hg.norm
    simpa [smul_eq_mul] using this

end GlobalTheory.OrbitUnfold
