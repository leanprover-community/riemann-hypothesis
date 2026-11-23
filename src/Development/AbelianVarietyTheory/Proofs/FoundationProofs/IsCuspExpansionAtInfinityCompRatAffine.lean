module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isExp_comp_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l →
    (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) →
    (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) →
    IsExp ε f h → IsExp ε f' h' := by
  intro Ω _ ε f f' l m h h' hl hf hc hexp
  obtain ⟨⟨N, hN, hden⟩, C, hC⟩ := hexp
  have hl0 : l ≠ 0 := hl.ne'
  refine ⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩
  · intro s hs
    have hr : h.coeff (s / l) ≠ 0 := by
      intro h0
      apply hs
      have := hc (s / l)
      rw [div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero] at this
      exact (map_eq_zero ε).1 this
    obtain ⟨n, hn⟩ := hden _ hr
    refine ⟨n * l.num, ?_⟩
    have hs' : s = s / l * l := by field_simp
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hd0 : (l.den : ℚ) ≠ 0 := by exact_mod_cast l.den_pos.ne'
    rw [hs', hn]
    push_cast
    rw [← Rat.mul_den_eq_num l]
    field_simp
  · intro z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hlz : C < ((l : ℂ) * z + (m : ℂ)).im := by
      have h1 : C / l < z.im := lt_of_le_of_lt (le_max_left _ _) hz
      have h2 : C < z.im * l := (div_lt_iff₀ (by exact_mod_cast hl)).1 h1
      simpa [mul_comm] using h2
    rw [hf z hz0]
    have key := hC _ hlz
    rw [← (Equiv.mulRight₀ l hl0).hasSum_iff]
    convert key using 1
    funext r
    have he : (Equiv.mulRight₀ l hl0) r = r * l := rfl
    simp only [Function.comp, he, hc r]
    rw [mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end GlobalTheory.FN
