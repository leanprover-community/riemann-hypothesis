module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem exists_nat_mul_mem_adjoin_int {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ S) : ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := by exact_mod_cast r.den_pos.ne'
      rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [h]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x + y) = (m : ℤ) • ((n : Ω) * x) + (n : ℤ) • ((m : Ω) * y) := by
      simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
    rw [h]
    exact add_mem (zsmul_mem hnx _) (zsmul_mem hmy _)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [h]
    exact mul_mem hnx hmy

theorem ChartDenominator.proof : ChartDenominator.Statement := by
  intro K _ ι _ Ω _ _ y b τ s hs
  classical
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, 1 ≤ n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose N hN1 hN using key
  refine ⟨∏ c, N c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => by
    have := hN1 c; omega), ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have h : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)) =
      (m : ℤ) • ((N c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)))) := by
    rw [hm]; simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
  rw [h]
  exact zsmul_mem (hN c hc) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
