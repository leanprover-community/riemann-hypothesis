module

public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_int_comb_norm_sub_sq_le (k : ℕ) (v : Fin k → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  induction k generalizing x with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ih =>
    set U : Submodule ℝ E := span ℝ (Set.range (Fin.init v)) with hU
    have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℝ).1 hx
    set a := c (Fin.last k)
    set u := v (Fin.last k)
    set y := ∑ i : Fin k, c i.castSucc • v i.castSucc with hy
    have hyU : y ∈ U := sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
    set p := U.starProjection u
    have hpU : p ∈ U := U.starProjection_apply_mem u
    have hq : u - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal u
    set t : ℝ := a - round a
    have ht : |t| ≤ 1 / 2 := abs_sub_round a
    obtain ⟨w, hw, hle⟩ := ih (Fin.init v) (x := y + t • p) (add_mem hyU (smul_mem _ _ hpU))
    have hwU : w ∈ U := span_subset_span ℤ ℝ _ hw
    refine ⟨w + round a • u, add_mem (span_mono ?_ hw) (smul_mem _ _ (subset_span ⟨_, rfl⟩)), ?_⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩
    have e : ∑ i, c i • v i - (w + round a • u) = (y + t • p - w) + t • (u - p) := by
      rw [Fin.sum_univ_castSucc, ← Int.cast_smul_eq_zsmul ℝ]
      simp only [t]; module
    have hz : y + t • p - w ∈ U := sub_mem (add_mem hyU (smul_mem _ _ hpU)) hwU
    have horth : ⟪y + t • p - w, t • (u - p)⟫_ℝ = 0 :=
      U.inner_right_of_mem_orthogonal hz (smul_mem _ _ hq)
    have hup : ‖u - p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have h1 : ⟪p, u - p⟫_ℝ = 0 := U.inner_right_of_mem_orthogonal hpU hq
      have h2 := norm_add_sq_real p (u - p)
      rw [add_sub_cancel, h1] at h2
      nlinarith [sq_nonneg ‖p‖]
    have ht2 : t ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    rw [e, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Fin.sum_univ_castSucc]
    have : t ^ 2 * ‖u - p‖ ^ 2 ≤ 1 / 4 * ‖u‖ ^ 2 :=
      mul_le_mul ht2 hup (sq_nonneg _) (by norm_num)
    have hle' : ‖y + t • p - w‖ ^ 2 ≤ (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) / 4 := hle
    linarith

variable {L : Submodule ℤ E}

end GlobalTheory
