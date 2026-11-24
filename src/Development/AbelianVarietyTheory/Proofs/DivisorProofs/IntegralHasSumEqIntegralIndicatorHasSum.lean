module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem integral_hasSum_eq_integral_indicator_hasSum :
    ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ),
      (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite →
      ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) →
      (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) →
      (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  intro X ι _ _ μ k hk hfin p K Kp hK hKp h0
  classical
  set s := hfin.toFinset with hs
  have hnull : ∀ i ∉ s, k i =ᵐ[μ] 0 := by
    intro i hi
    have hi' : ∫ x, ‖k i x‖ ∂μ = 0 := by
      by_contra h
      exact hi (by simpa [hs] using h)
    have := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (k i x)) (hk i).norm).1 hi'
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂μ, ∀ i, i ∉ s → k i x = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall (fun x h => absurd hi h)
    · filter_upwards [hnull i hi] with x hx _
      exact hx
  have hKae : K =ᵐ[μ] fun x => ∑ i ∈ s, k i x := by
    filter_upwards [hall] with x hx
    exact (hK x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => hx i hi))
  have hKpae : Kp =ᵐ[μ] fun x => ∑ i ∈ s, p.indicator (fun i => k i x) i := by
    filter_upwards [hall] with x hx
    refine (hKp x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => ?_))
    by_cases hp : i ∈ p
    · simp [Set.indicator_of_mem hp, hx i hi]
    · simp [Set.indicator_of_notMem hp]
  have hind : ∀ i, (fun x => p.indicator (fun i => k i x) i) =
      if i ∈ p then k i else fun _ => 0 := by
    intro i
    by_cases hp : i ∈ p
    · funext x; simp [Set.indicator_of_mem hp, hp]
    · funext x; simp [Set.indicator_of_notMem hp, hp]
  rw [integral_congr_ae hKae, integral_congr_ae hKpae,
    MeasureTheory.integral_finsetSum s (fun i _ => hk i),
    MeasureTheory.integral_finsetSum s (fun i _ => by
      rw [hind i]; split_ifs
      · exact hk i
      · exact integrable_zero _ _ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hind i]
  split_ifs with hp
  · rfl
  · simp [h0 i hp]

end GlobalTheory
