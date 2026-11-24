module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
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
import Mathlib.Tactic.Linter.Style
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

private theorem UpperTheory.pow_sub_eq_one_of_condLE_valuation_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ)
    (hν : CondLE ϖ e ν) (x : kˣ) (hx : valuation k (x : k) = 1) (a b : ℕ) (hab : a < b)
    (h : valuation k ((x : k) ^ b - (x : k) ^ a) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    ν x ^ (b - a) = 1 := by
  have hmem : x ^ (b - a) ∈ unitCong (ϖ ^ e) := by
    show valuation k ((x ^ (b - a) : kˣ) : k) = 1 ∧
      valuation k (((x ^ (b - a) : kˣ) : k) - 1) ≤ valuation k ((ϖ ^ e : kˣ) : k)
    have hfac : (x : k) ^ b - (x : k) ^ a = (x : k) ^ a * ((x : k) ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    rw [hfac, map_mul, map_pow, hx, one_pow, one_mul] at h
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
    · rw [Units.val_pow_eq_pow_val]
      exact h
  rw [← map_pow]
  exact hν _ hmem

theorem UpperTheory.isIntegral_unitChar_of_conductor_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ), IsUnif ϖ → CondLE ϖ e ν → ∀ x : kˣ, valuation k (x : k) = 1 → IsIntegral ℤ (ν x : ℂ) := by
  intro k _ _ _ _ ϖ e ν hϖ hν x hx
  have hpow : ∀ n : ℕ, (x : k) ^ n ∈ 𝒪[k] := fun n =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_pow, hx, one_pow])
  let g : ℕ → Res (k := k) e := fun n => Ideal.Quotient.mk _ ⟨(x : k) ^ n, hpow n⟩
  obtain ⟨i, j, hne, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ a b : ℕ, a < b → g a = g b → IsIntegral ℤ (ν x : ℂ) := by
    intro a b hab h
    have h1 := Ideal.Quotient.eq.1 h.symm
    have h2 := (Model.val_le_iff_mem hϖ e _).1 h1
    have h3 : ν x ^ (b - a) = 1 := UpperTheory.pow_sub_eq_one_of_condLE_valuation_le ϖ e ν hν x hx a b hab (by simpa using h2)
    refine IsIntegral.of_pow (Nat.sub_pos_of_lt hab) ?_
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    exact isIntegral_one
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hg
  · exact key j i h hg.symm
