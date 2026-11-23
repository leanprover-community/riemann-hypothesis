module

public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.PadicNatCastNorm

variable {p : ℕ} [Fact p.Prime]

private lemma norm_natCast_padicAlgCl_of_not_dvd' {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : PadicAlgCl p)‖ = 1 := by
  have h1 : ((m : ℚ_[p]) : PadicAlgCl p) = (m : PadicAlgCl p) := map_natCast _ m
  rw [← h1, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm

theorem goal1 {m : ℕ} (hm : ¬ p ∣ m) {η : PadicAlgCl p} (hη : η ^ m = 1) (h : η ≠ 1) :
    ‖η - 1‖ = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hn : ‖η‖ = 1 := by
    have h2 : ‖η‖ ^ m = 1 := by rw [← norm_pow, hη, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg η) hm0).1 h2
  have hup : ‖η - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max η (-1)
    rw [hn, norm_neg, norm_one, max_self, ← sub_eq_add_neg] at this
    exact this
  refine le_antisymm hup (not_lt.1 fun hlt => ?_)
  have hsub : η - 1 ≠ 0 := sub_ne_zero.2 h
  have hgeom : ∀ n : ℕ, ‖∑ j ∈ Finset.range n, η ^ j‖ ≤ 1 := fun n =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun j _ => by rw [norm_pow, hn, one_pow])
  have hpow : ∀ i : ℕ, ‖η ^ i - 1‖ ≤ ‖η - 1‖ := fun i => by
    rw [← geom_sum_mul, norm_mul]
    calc ‖∑ j ∈ Finset.range i, η ^ j‖ * ‖η - 1‖ ≤ 1 * ‖η - 1‖ :=
          mul_le_mul_of_nonneg_right (hgeom i) (norm_nonneg _)
      _ = ‖η - 1‖ := one_mul _
  have hsum0 : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have h3 := geom_sum_mul η m
    rw [hη, sub_self] at h3
    exact (mul_eq_zero.1 h3).resolve_right hsub
  have hmeq : (m : PadicAlgCl p) = -∑ i ∈ Finset.range m, (η ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum0, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, zero_sub, neg_neg]
  have hle : ‖(m : PadicAlgCl p)‖ ≤ ‖η - 1‖ := by
    rw [hmeq, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      (fun i _ => hpow i)
  rw [norm_natCast_padicAlgCl_of_not_dvd' hm] at hle
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl 1)

end Bl.PadicNatCastNorm
