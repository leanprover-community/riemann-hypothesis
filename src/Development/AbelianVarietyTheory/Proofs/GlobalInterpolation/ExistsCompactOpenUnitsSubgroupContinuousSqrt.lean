module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem exists_local_sqrt_near_one (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : ∃ (N : Set K) (g : K → K), IsOpen N ∧ (1 : K) ∈ N ∧ ContinuousOn g N ∧
      ∀ u ∈ N, g u ^ 2 = u := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  refine ⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, fun u hu => ?_⟩
  · simpa using hf.image_mem_toOpenPartialHomeomorph_target
  · have := e.right_inv hu
    rwa [he] at this

theorem exists_isSqrtOn (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by
  classical
  obtain ⟨N, g, hN, h1, hg, hsq⟩ := exists_local_sqrt_near_one K h2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hN 1 h1
  set r : ℝ := min (ε / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.closedBall (1 : K) r ⊆ N :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hclopen : IsClopen (Metric.closedBall (1 : K) r) := ⟨Metric.isClosed_closedBall, hopen⟩
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  refine ⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen,
    isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩
  · intro a ha b hb
    have hna := hnorm a ha
    rw [mem_closedBall_iff_norm] at ha hb ⊢
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rwa [norm_mul, hna, one_mul]
  · intro a ha
    have hna := hnorm a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hna
    rw [mem_closedBall_iff_norm] at ha ⊢
    have : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by field_simp; ring
    rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]
  · refine continuous_piecewise ?_ ?_ continuousOn_const
    · simp [hclopen.frontier_eq]
    · rw [Metric.isClosed_closedBall.closure_eq]
      exact hg.mono hsub
  · intro a ha
    rw [Set.piecewise_eq_of_mem _ _ _ ha]
    exact hsq a (hsub ha)

end GlobalTheory.QuadFibre
