module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumClsLeEncard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TotalWeight

theorem natCast_pow_le_pow_of_exponent_le (q m a e e' : ℕ) (he : e ≤ e') (h1 : (1 : ℝ) ≤ (q : ℝ) ^ (m + a)) :
    (q : ℝ) ^ (e * m) ≤ ((q : ℝ) ^ (m + a)) ^ e' := by
  have h2 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + a) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa using h1
      · simp [hm.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (Nat.le_add_right _ _)
  calc (q : ℝ) ^ (e * m) = ((q : ℝ) ^ m) ^ e := by rw [mul_comm, pow_mul]
    _ ≤ ((q : ℝ) ^ (m + a)) ^ e := pow_le_pow_left₀ (by positivity) h2 e
    _ ≤ _ := pow_le_pow_right₀ h1 he

theorem sumCls_one_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k)
    (h : ∃ d Λ, S.IsTerm d Λ) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  obtain ⟨d, Λ, hT⟩ := h
  obtain ⟨ha, hD, -, -, h1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : 0 ≤ S.vth := by
    unfold Frames.vth
    split_ifs <;> norm_num
  have hHp : S.Hp = (S.q : ℝ) ^ ((S.vth + S.vD).toNat + S.a.toNat) := by
    unfold Frames.Hp
    rw [← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (add_nonneg hth hD)]
    ring
  refine (GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans
    ((GlobalTheory.IntClsCount.main L r k S hD).trans ?_)
  have he : r * (r + 1) ≤ 3 * (r + 1) ^ 2 := by nlinarith
  rw [hHp] at h1 ⊢
  have key := ENNReal.ofReal_le_ofReal (natCast_pow_le_pow_of_exponent_le S.q _ _ _ _ he h1)
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at key
  exact key

end GlobalTheory.HL.TotalWeight
