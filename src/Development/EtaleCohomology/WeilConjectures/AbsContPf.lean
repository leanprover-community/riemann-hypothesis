module

public import Development.EtaleCohomology.WeilConjectures.ContinCut
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace LateralTheory.EWeil.AbsContPf

universe u v

open LateralTheory.EWeil.ContinCut

namespace AbsoluteContinuitySecondLemma

theorem goal1 (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]; rfl

end AbsoluteContinuitySecondLemma

theorem norm_smul_le (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ = ‖a‖ * ‖q‖ :=
  AbsoluteContinuitySecondLemma.goal1 l a q

namespace AbsoluteContinuityFirstLemma

namespace AbsoluteContinuitySmulBound

private lemma smul_bound (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) (q : ℚ_[l]) : ‖a • q‖ ≤ ‖q‖ := by
  rw [Algebra.smul_def, norm_mul]
  have h : ‖(algebraMap ℤ_[l] ℚ_[l] a)‖ ≤ 1 := by
    have e : algebraMap ℤ_[l] ℚ_[l] a = (a : ℚ_[l]) := rfl
    rw [e, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one a
  calc ‖algebraMap ℤ_[l] ℚ_[l] a‖ * ‖q‖ ≤ 1 * ‖q‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖q‖ := one_mul _

end AbsoluteContinuitySmulBound

theorem goal1 (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] M).FG)
  refine ⟨∑ x ∈ s, ‖φ x‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro m
  have hm : m ∈ Submodule.span ℤ_[l] (s : Set M) := by rw [hs]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
      exact Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) hx
  | zero => simpa using Finset.sum_nonneg (fun (x : M) (_ : x ∈ s) => norm_nonneg (φ x))
  | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
  | smul a x _ hx =>
      rw [map_smul]
      exact (AbsoluteContinuitySmulBound.smul_bound l a (φ x)).trans hx

end AbsoluteContinuityFirstLemma

theorem bdd (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
    (φ : M →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖φ m‖ ≤ C :=
  AbsoluteContinuityFirstLemma.goal1 l M φ

theorem AbsCont_of (hC : Chev.{u}) : AbsCont.{u, v} := by
  intro l _ G _ _ _ M _ _ _ ρ K hK h0 hopen φ x
  obtain ⟨C, hC0, hCb⟩ := bdd l M φ
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0:ℝ) < C + 1))
    (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨k, hk⟩ := hC l M K hK h0 N
  set y := ρ g₀ x
  have hU : IsOpen {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} :=
    (hopen y k).preimage (continuous_id.mul continuous_const)
  have hmem : g₀ ∈ {g : G | g * g₀⁻¹ ∈ {h : G | ρ h y - y ∈ K k}} := by
    simp [y]
  filter_upwards [hU.mem_nhds hmem] with g hg
  change ρ (g * g₀⁻¹) y - y ∈ K k at hg
  have hd : ρ g x - ρ g₀ x ∈ K k := by
    have : ρ (g * g₀⁻¹) y = ρ g x := by
      simp only [y]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [this] at hg; exact hg
  obtain ⟨z, hz⟩ := hk _ hd
  rw [dist_eq_norm, ← map_sub, hz, map_smul, norm_smul_le, PadicInt.norm_p_pow]
  have hzC := hCb z
  have hpow : (l : ℝ) ^ (-(N : ℤ)) = (l : ℝ)⁻¹ ^ N := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hpow]
  have hp0 : 0 ≤ (l : ℝ)⁻¹ ^ N := by positivity
  calc (l : ℝ)⁻¹ ^ N * ‖φ z‖ ≤ (l : ℝ)⁻¹ ^ N * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hp0
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_right hN (by linarith)
    _ = ε := div_mul_cancel₀ _ (by linarith)

end LateralTheory.EWeil.AbsContPf
