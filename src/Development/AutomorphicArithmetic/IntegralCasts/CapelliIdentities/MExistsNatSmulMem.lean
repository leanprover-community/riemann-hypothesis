module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

private theorem UpperTheory.Reformulated.B.Qh47.exists_nat_mul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * a) := by
  have hq : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hz : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨y, hy, hi⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with h | h
  · have h2 : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      exact (Int.cast_natCast _).symm
    rw [h2]; exact hi
  · have h2 : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      rw [Int.cast_neg, neg_neg, Int.cast_natCast]
    rw [h2, neg_mul]; exact hi.neg

theorem UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : Formalism.BasicNotions.HSpace E}
      (M : Submodule (NumberField.RingOfIntegers E) S.V) {x : S.V},
      x ∈ Submodule.span E (↑M : Set S.V) → ∃ (n : ℕ), (0 : ℕ) < n ∧ n • x ∈ M := by
  intro E _ _ _ S M x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_pos, by rw [one_smul]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hmx n
    · rw [mul_smul]; exact nsmul_mem hny m
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hi⟩ := UpperTheory.Reformulated.B.Qh47.exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E, algebraMap _ E b = (n : E) * a :=
      ⟨⟨(n : E) * a, hi⟩, rfl⟩
    have e : (n * m) • a • x = b • m • x := by
      rw [mul_smul n m, smul_comm m a x, ← algebraMap_smul E b, hb, mul_smul,
        Nat.cast_smul_eq_nsmul]
    rw [e]
    exact M.smul_mem b hmx
