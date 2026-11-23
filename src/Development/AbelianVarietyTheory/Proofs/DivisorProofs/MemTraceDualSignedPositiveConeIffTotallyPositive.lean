module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
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

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Div.LipschitzCone

theorem sign_cone_iff (x y w : ℝ) (hx : x ≠ 0) (hw : 0 < w) :
    0 < (SignType.sign (x * w) : ℝ) * y ↔ 0 < y * x := by
  rw [sign_mul, sign_pos hw, mul_one]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_neg h]
    simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, Left.neg_pos_iff]
    constructor
    · intro hy; exact mul_pos_of_neg_of_neg hy h
    · intro hyx
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hc h.le
      linarith
  · rw [sign_pos h]
    simp only [SignType.coe_one, one_mul]
    constructor
    · intro hy; exact mul_pos hy h
    · intro hyx; exact pos_of_mul_pos_left hyx h.le

theorem cone_iff : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  intro F _ _ 𝔞 b hb z hz ν
  have ha : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔞.ne_zero
  have hM : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 ≠ 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ ha
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone
  simp only [Set.mem_setOf_eq]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff hM, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.dual_dual]
  refine and_congr Iff.rfl (forall_congr' fun τ => ?_)
  rw [Complex.im_ofReal_mul, map_mul τ ν b]
  exact sign_cone_iff _ _ _ ((map_ne_zero τ).2 hb) (hz τ)

end GlobalTheory.Div.LipschitzCone
