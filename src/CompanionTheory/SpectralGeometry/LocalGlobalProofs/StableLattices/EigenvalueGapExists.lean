module

public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace GlobalTheory.CompanionTheory.UGeoGap

theorem exists_gap_of_mem_Icc_top :
    ∀ (n : ℕ) (l : Fin n → ℝ) (L : ℝ), 0 < L → (∀ i, 0 ≤ l i ∧ l i ≤ L) → (∃ i, l i = L) →
      ∃ r : ℕ, r < n ∧ ∀ i, l i < r * (L / (n + 1)) ∨ (r + 1) * (L / (n + 1)) ≤ l i := by
  intro n l L hL _ hex
  obtain ⟨i₀, hi₀⟩ := hex
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδpos : 0 < L / (n + 1) := div_pos hL hn
  choose f hf using fun r : Fin n => hcon r r.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have h1 := hf r
    have h2 := hf s
    rw [hrs] at h1
    have a1 : ((r : ℕ) : ℝ) < (s : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h1.1 h2.2) hδpos.le
    have a2 : ((s : ℕ) : ℝ) < (r : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h2.1 h1.2) hδpos.le
    have b1 : (r : ℕ) < (s : ℕ) + 1 := by exact_mod_cast a1
    have b2 : (s : ℕ) < (r : ℕ) + 1 := by exact_mod_cast a2
    exact Fin.ext (by omega)
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) i₀
  have h1 := (hf r).2
  rw [hr, hi₀] at h1
  have hr1 : ((r : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast r.2
  have h2 : (((r : ℕ) : ℝ) + 1) * (L / (n + 1)) ≤ n * (L / (n + 1)) :=
    mul_le_mul_of_nonneg_right hr1 hδpos.le
  have h3 : (n : ℝ) * (L / (n + 1)) < (n + 1) * (L / (n + 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hδpos
  have h4 : ((n : ℝ) + 1) * (L / (n + 1)) = L := by
    field_simp
  linarith

end GlobalTheory.CompanionTheory.UGeoGap
