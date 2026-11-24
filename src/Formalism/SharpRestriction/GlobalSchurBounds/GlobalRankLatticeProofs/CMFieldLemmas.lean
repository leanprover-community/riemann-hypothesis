module

public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.GenericFramesLetters
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs, Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds, Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas

-- ===== clump member: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs =====
-- clump-header: {"m": "Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Finset

namespace BernoulliSums

variable {α : Type*} [Fintype α]

theorem bern_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) : 0 ≤ bern δ T := by
  unfold bern
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

theorem sum_bern_card (δ : ℝ) (f : ℕ → ℝ) :
    ∑ T : Finset α, bern δ T * f T.card =
      ∑ ν ∈ range (Fintype.card α + 1),
        (bernsteinPolynomial ℝ (Fintype.card α) ν).eval δ * f ν := by
  classical
  simp only [bern]
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun k => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * f k),
    Finset.card_univ]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp [bernsteinPolynomial, nsmul_eq_mul]
  ring

theorem sum_bern (δ : ℝ) : ∑ T : Finset α, bern δ T = 1 := by
  have h := sum_bern_card (α := α) δ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]

theorem sum_bern_var (δ : ℝ) :
    ∑ T : Finset α, bern δ T * (((Fintype.card α : ℕ) : ℝ) * δ - T.card) ^ 2 =
      (Fintype.card α : ℝ) * δ * (1 - δ) := by
  rw [sum_bern_card δ (fun ν => (((Fintype.card α : ℕ) : ℝ) * δ - ν) ^ 2)]
  have h := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance ℝ (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    nsmul_eq_mul, Polynomial.eval_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

end BernoulliSums

open BernoulliSums

open Classical in
theorem branching_interlacing_pairs (D : D7) (sc : Scale) : Conclusion6 D sc := by
  intro δ hδ0 hδ1 hδn β BAD _ hbad P hp ω hP hω
  set n : ℕ := Fintype.card (HH D) with hndef
  have hn : ((n : ℕ) : ℝ) = (D.R.n : ℝ) := by
    rw [hndef]
    first
      | exact_mod_cast Formalism.HC.Frame.card_A (φ := D.R.toFrame)
  rw [← hn] at hδn ⊢
  have hnpos : (0 : ℝ) < n := by nlinarith
  have hbern0 : ∀ T : Finset (HH D), 0 ≤ bern δ T := fun T => bern_nonneg hδ0.le hδ1 T
  have hsum1 : ∑ T : Finset (HH D), bern δ T = 1 := sum_bern δ
  have hvar := sum_bern_var (α := HH D) δ
  rw [← hndef] at hvar
  set B : ℝ := 4 * β * δ * n * ∑ p ∈ P, ω p with hB
  by_contra hcon
  push_neg at hcon

  have hper : ∀ p ∈ P, ∑ T : Finset (HH D),
      bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) ≤ n * (β * δ) := by
    intro p hpP
    have hc : ∀ T : Finset (HH D), bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) =
        ∑ t : HH D, if t ∈ T ∧ BAD (hp p) t T then bern δ T else 0 := by
      intro T
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter fun t => t ∈ T ∧ BAD (hp p) t T) = T.filter (fun t => BAD (hp p) t T) := by
        ext t; simp
      rw [this, mul_comm]
    calc ∑ T : Finset (HH D), bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ)
        = ∑ T : Finset (HH D), ∑ t : HH D, (if t ∈ T ∧ BAD (hp p) t T then bern δ T else 0) :=
          Finset.sum_congr rfl fun T _ => hc T
      _ = ∑ t : HH D, ∑ T : Finset (HH D), (if t ∈ T ∧ BAD (hp p) t T then bern δ T else 0) :=
          Finset.sum_comm
      _ ≤ ∑ _t : HH D, β * δ :=
          Finset.sum_le_sum fun t _ => by convert hbad (hp p) (hP p hpP) t
      _ = n * (β * δ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set Y : Finset (HH D) → ℝ := fun T =>
    ∑ p ∈ P, ω p * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) with hY
  have hY0 : ∀ T, 0 ≤ Y T := fun T =>
    Finset.sum_nonneg fun p hpP => mul_nonneg (hω p hpP) (Nat.cast_nonneg _)
  have hEY : ∑ T : Finset (HH D), bern δ T * Y T ≤ n * (β * δ) * ∑ p ∈ P, ω p := by
    calc ∑ T : Finset (HH D), bern δ T * Y T
        = ∑ p ∈ P, ω p * ∑ T : Finset (HH D),
            bern δ T * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) := by
          simp only [hY, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun T _ => by ring
      _ ≤ ∑ p ∈ P, ω p * (n * (β * δ)) :=
          Finset.sum_le_sum fun p hpP => mul_le_mul_of_nonneg_left (hper p hpP) (hω p hpP)
      _ = n * (β * δ) * ∑ p ∈ P, ω p := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
  have hEY0 : 0 ≤ ∑ T : Finset (HH D), bern δ T * Y T :=
    Finset.sum_nonneg fun T _ => mul_nonneg (hbern0 T) (hY0 T)

  let good : Finset (HH D) → Prop := fun T => δ * n / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * n
  have hq : 0 < (δ * n) ^ 2 := by positivity
  have hcheb : ∀ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T) ≤
      bern δ T * ((n * δ - T.card) ^ 2 * (4 / (δ * n) ^ 2)) := by
    intro T
    split_ifs with hg
    · exact mul_nonneg (hbern0 T) (mul_nonneg (sq_nonneg _) (by positivity))
    · have h1 : (δ * n) ^ 2 ≤ 4 * (n * δ - T.card) ^ 2 := by
        simp only [good, not_and_or, not_le] at hg
        rcases hg with h | h
        · nlinarith
        · nlinarith
      calc bern δ T = bern δ T * 1 := (mul_one _).symm
        _ ≤ bern δ T * ((n * δ - T.card) ^ 2 * (4 / (δ * n) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (hbern0 T)
          rw [mul_div_assoc', le_div_iff₀ hq]
          linarith
  have hbad_le : ∑ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T) ≤ 1 / 4 := by
    calc ∑ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T)
        ≤ ∑ T : Finset (HH D), bern δ T * ((n * δ - T.card) ^ 2 * (4 / (δ * n) ^ 2)) :=
          Finset.sum_le_sum fun T _ => hcheb T
      _ = (n * δ * (1 - δ)) * (4 / (δ * n) ^ 2) := by
          rw [← hvar, Finset.sum_mul]
          exact Finset.sum_congr rfl fun T _ => by ring
      _ ≤ 1 / 4 := by
          rw [mul_div_assoc', div_le_iff₀ hq]
          nlinarith [mul_le_mul_of_nonneg_left hδn (by positivity : (0 : ℝ) ≤ δ * n),
            mul_nonneg (mul_nonneg hδ0.le hδ0.le) hnpos.le]
  have hsplit : ∑ T : Finset (HH D), (if good T then bern δ T else 0) +
      ∑ T : Finset (HH D), (if good T then (0 : ℝ) else bern δ T) = 1 := by
    rw [← Finset.sum_add_distrib, ← hsum1]
    exact Finset.sum_congr rfl fun T _ => by split_ifs <;> ring
  obtain ⟨T0, -, hT0⟩ : ∃ T0 ∈ (Finset.univ : Finset (Finset (HH D))),
      (0 : ℝ) < (if good T0 then bern δ T0 else 0) := by
    by_contra hne
    push_neg at hne
    have : ∑ T : Finset (HH D), (if good T then bern δ T else 0) ≤ 0 := Finset.sum_nonpos hne
    linarith
  have hgood0 : good T0 := by
    by_contra hg
    rw [if_neg hg] at hT0
    exact lt_irrefl _ hT0
  rw [if_pos hgood0] at hT0
  have hlow : B * ∑ T : Finset (HH D), (if good T then bern δ T else 0) <
      ∑ T : Finset (HH D), bern δ T * Y T := by
    calc B * ∑ T : Finset (HH D), (if good T then bern δ T else 0)
        = ∑ T : Finset (HH D), (if good T then bern δ T * B else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun T _ => by split_ifs <;> ring
      _ < ∑ T : Finset (HH D), (if good T then bern δ T * Y T else 0) := by
          apply Finset.sum_lt_sum
          · intro T _
            split_ifs with hg
            · exact mul_le_mul_of_nonneg_left (hcon T hg.1 hg.2).le (hbern0 T)
            · exact le_refl _
          · refine ⟨T0, Finset.mem_univ _, ?_⟩
            rw [if_pos hgood0, if_pos hgood0]
            exact mul_lt_mul_of_pos_left (hcon T0 hgood0.1 hgood0.2) hT0
      _ ≤ ∑ T : Finset (HH D), bern δ T * Y T := by
          apply Finset.sum_le_sum
          intro T _
          split_ifs
          · exact le_refl _
          · exact mul_nonneg (hbern0 T) (hY0 T)
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  nlinarith [mul_le_mul_of_nonneg_left (show (3 : ℝ) / 4 ≤ ∑ T : Finset (HH D), (if good T then bern δ T else 0) by linarith) hB0]

end Formalism.MainNotions.UnusedSlot33

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs =====

-- ===== clump member: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds =====
-- clump-header: {"m": "Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas\npublic import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

private theorem eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf {G : Type*} [AddCommGroup G] (a : G) (k : ℤ)
    (hk : k • a = 0) (hlt : |k| < (addOrderOf a : ℤ)) : k = 0 :=
  Int.eq_zero_of_abs_lt_dvd (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk) hlt

private theorem sub_zsmul_eq_of_two_eqs {G : Type*} [AddCommGroup G] (a h t u₀ : G) (i j : ℤ) (s s' : ℕ)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) :
    (j - i) • h = ((s' : ℤ) - s) • a := by
  rw [sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  calc j • h - i • h = (t + j • h) - (t + i • h) := by abel
    _ = (s' • a + u₀) - (s • a + u₀) := by rw [e, e']
    _ = s' • a - s • a := by abel

private theorem false_of_three_distinct_in_window {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hR : Formalism.FrobeniusOrbits.NoRel T L)
    (hh : 4 * L < addOrderOf h) (i₀ i1 i2 i3 : ℤ) (s1 s2 s3 : ℕ)
    (a1 : i₀ ≤ i1) (b1 : i1 < i₀ + L) (a2 : i₀ ≤ i2) (b2 : i2 < i₀ + L)
    (a3 : i₀ ≤ i3) (b3 : i3 < i₀ + L)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) (hs1 : s1 ∈ T) (hs2 : s2 ∈ T) (hs3 : s3 ∈ T)
    (e1 : t + i1 • h = s1 • a + u₀) (e2 : t + i2 • h = s2 • a + u₀)
    (e3 : t + i3 • h = s3 • a + u₀) : False := by
  have hL : (4 * L : ℤ) < addOrderOf h := by exact_mod_cast hh
  have hdist : ∀ (i j : ℤ) (s s' : ℕ), i₀ ≤ i → i < i₀ + L → i₀ ≤ j → j < i₀ + L → i ≠ j →
      (j - i) • h = ((s' : ℤ) - s) • a → s ≠ s' := by
    intro i j s s' hi hi' hj hj' hij e hss
    subst hss
    rw [sub_self, zero_zsmul] at e
    have h0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf h (j - i) e (by rw [abs_lt]; constructor <;> omega)
    omega
  have k2 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i2 s1 s2 e1 e2
  have k3 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i3 s1 s3 e1 e3
  have k23 := sub_zsmul_eq_of_two_eqs a h t u₀ i2 i3 s2 s3 e2 e3
  have n12 := hdist i1 i2 s1 s2 a1 b1 a2 b2 h12 k2
  have n13 := hdist i1 i3 s1 s3 a1 b1 a3 b3 h13 k3
  have n23 := hdist i2 i3 s2 s3 a2 b2 a3 b3 h23 k23
  have hD : ((i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)) • a = 0 := by
    rw [sub_zsmul, ← sub_eq_add_neg, ← smul_smul, ← smul_smul, ← k2, ← k3, smul_smul, smul_smul,
      mul_comm (i3 - i1), sub_self]
  have hN : ∀ s ∈ T, 4 * (L : ℤ) * s < addOrderOf a := fun s hs => by exact_mod_cast hT s hs
  have hb1 := hN s1 hs1
  have hb2 := hN s2 hs2
  have hb3 := hN s3 hs3
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hs1n : (0 : ℤ) ≤ s1 := by positivity
  have hs2n : (0 : ℤ) ≤ s2 := by positivity
  have hs3n : (0 : ℤ) ≤ s3 := by positivity
  have hy2 : 4 * (L : ℤ) * |(s2 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s2 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs2n]
  have hy3 : 4 * (L : ℤ) * |(s3 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s3 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs3n]
  have hx : |i3 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hu : |i2 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hxy : 4 * |(i3 - i1) * ((s2 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg ((s2 : ℤ) - s1))]
  have huv : 4 * |(i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hu (abs_nonneg ((s3 : ℤ) - s1))]
  have hDb : |(i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_lt]
    constructor <;>
      linarith [le_abs_self ((i3 - i1) * ((s2 : ℤ) - s1)), neg_abs_le ((i3 - i1) * ((s2 : ℤ) - s1)),
        le_abs_self ((i2 - i1) * ((s3 : ℤ) - s1)), neg_abs_le ((i2 - i1) * ((s3 : ℤ) - s1)),
        abs_nonneg ((i3 - i1) * ((s2 : ℤ) - s1)), abs_nonneg ((i2 - i1) * ((s3 : ℤ) - s1))]
  have hD0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hD hDb
  exact hR s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 (i2 - i1) (i3 - i1)
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h12))) hu
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h13))) hx
    (fun hc => h23 (by omega)) (sub_eq_zero.mp hD0)

private theorem eq_of_zsmul_eqs_of_small_orders {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hpos : 0 < addOrderOf h)
    (hh : addOrderOf h ≤ 4 * L) (i j : ℤ) (s s' : ℕ) (hs : s ∈ T) (hs' : s' ∈ T)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) : s = s' := by
  have k := sub_zsmul_eq_of_two_eqs a h t u₀ i j s s' e e'
  have hm : ((addOrderOf h : ℤ) * ((s' : ℤ) - s)) • a = 0 := by
    rw [← smul_smul, ← k, smul_smul, mul_comm, ← smul_smul, natCast_zsmul,
      addOrderOf_nsmul_eq_zero, zsmul_zero]
  have hm0 : (0 : ℤ) ≤ (addOrderOf h : ℤ) := by positivity
  have hmL : (addOrderOf h : ℤ) ≤ 4 * L := by exact_mod_cast hh
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hsn : (0 : ℤ) ≤ s := by positivity
  have hsn' : (0 : ℤ) ≤ s' := by positivity
  have hb := (show 4 * (L : ℤ) * s < addOrderOf a by exact_mod_cast hT s hs)
  have hb' := (show 4 * (L : ℤ) * s' < addOrderOf a by exact_mod_cast hT s' hs')
  have hy : 4 * (L : ℤ) * |(s' : ℤ) - s| < addOrderOf a := by
    rcases abs_cases ((s' : ℤ) - s) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hsn, mul_nonneg hLn hsn']
  have hz := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hm (by
    rw [abs_mul, abs_of_nonneg hm0]
    nlinarith [mul_le_mul_of_nonneg_right hmL (abs_nonneg ((s' : ℤ) - s))])
  rcases mul_eq_zero.mp hz with h0 | h0 <;> omega

theorem dropping_proposition_holds : ∃ C : ℝ, ∀ D : D7, Conclusion5 D C := by
  obtain ⟨C, -, hT⟩ := Formalism.FrobeniusOrbits.hostThickExists
  refine ⟨C, fun D Lw hLw => ?_⟩
  obtain ⟨T, hTs, hTR, hTc⟩ := hT D.R.n0 Lw hLw
  refine ⟨T, ?_, hTc, hTR, ?_⟩
  · intro s hs
    have h1 : ((4 * Lw * s : ℕ) : ℝ) < (D.R.n0 : ℝ) := by exact_mod_cast hTs s hs
    have hL : (2 : ℝ) ≤ Lw := by exact_mod_cast hLw
    rw [lt_div_iff₀ (by linarith)]
    push_cast at h1
    linarith
  · intro u₀ t h
    refine ⟨fun hh i₀ => ?_, fun hh => ?_⟩
    · by_contra hc
      push_neg at hc
      obtain ⟨i1, hi1, i2, hi2, i3, hi3, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
      simp only [Finset.mem_filter, Finset.mem_Ico, transl, Set.mem_setOf_eq] at hi1 hi2 hi3
      obtain ⟨⟨a1, b1⟩, s1, hs1, e1⟩ := hi1
      obtain ⟨⟨a2, b2⟩, s2, hs2, e2⟩ := hi2
      obtain ⟨⟨a3, b3⟩, s3, hs3, e3⟩ := hi3
      exact false_of_three_distinct_in_window _ t h u₀ T Lw hTs hTR hh i₀ i1 i2 i3 s1 s2 s3 a1 b1 a2 b2 a3 b3
        h12 h13 h23 hs1 hs2 hs3 e1 e2 e3
    · haveI hfin : Finite (HH D) := by
        show Finite (Fin _)
        infer_instance
      have hpos : 0 < addOrderOf h := addOrderOf_pos h
      have hsub : (coset t h ∩ transl T u₀).Subsingleton := by
        rintro x ⟨⟨i, rfl⟩, s, hs, ex⟩ y ⟨⟨j, rfl⟩, s', hs', ey⟩
        have hss := eq_of_zsmul_eqs_of_small_orders _ t h u₀ T Lw hTs hpos hh i j s s' hs hs' ex ey
        subst hss
        rw [ex, ey]
      rcases hsub.eq_empty_or_singleton with hE | ⟨x, hx⟩
      · rw [hE, Set.ncard_empty]
        omega
      · rw [hx, Set.ncard_singleton]

end Formalism.MainNotions.UnusedSlot33

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds =====

-- ===== clump member: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas =====
-- clump-header: {"m": "Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.GenericFramesLetters\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD\nimport Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

theorem field_lemmas_two_to_six (D : D7) (sc : Scale) :
    Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc :=
  ⟨second_proposition_every_localisation D, points_property_of_d7 D, generic_frames_letters D, no_three_consecutive_thick_places D, branching_interlacing_pairs D sc⟩

theorem field_lemmas_except_seven : ∃ C₅ : ℝ, ∀ (D : D7) (sc : Scale),
    Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ Conclusion5 D C₅ ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc ∧ Conclusion8 D := by
  obtain ⟨C, hC⟩ := dropping_proposition_holds
  refine ⟨C, fun D sc => ?_⟩
  obtain ⟨h2, h3, h4, h5c, h6⟩ := field_lemmas_two_to_six D sc
  exact ⟨ramification_two_and_conjugation_at_q_and_d D, h2, h3, h4, hC D, h5c, h6, lemma_one_eight_holds D⟩

end Formalism.MainNotions.UnusedSlot33
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas =====
