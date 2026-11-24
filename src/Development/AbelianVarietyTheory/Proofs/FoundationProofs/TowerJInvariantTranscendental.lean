module

import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem hahnSeries_order_eq_neg_one_of_coeff {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (h0 : ∀ r : ℚ, r < -1 → h.coeff r = 0) : h.order = -1 := by
  have h1' : h.coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_
  exact le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

theorem hahnSeries_pow_order_of_order_neg_one {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (ho : h.order = -1) (n : ℕ) :
    (h ^ n).order = -(n : ℚ) ∧ (h ^ n).coeff (-(n : ℚ)) = 1 := by
  have hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ) := fun k => by
    rw [HahnSeries.order_pow, ho]
    simp
  refine ⟨hord n, ?_⟩
  induction n with
  | zero => simp
  | succ k ih =>

    have hm := HahnSeries.coeff_mul_order_add_order (h ^ k) h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one] at hm
    have e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1 := by push_cast; ring
    rw [pow_succ, e, hm]

private theorem hahnSeries_coeff_algebra_smul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (r : Ω) (y : HahnSeries ℚ Ω) (a : ℚ) :
    (@HSMul.hSMul Ω (HahnSeries ℚ Ω) (HahnSeries ℚ Ω) (@instHSMul _ _ Algebra.toSMul) r y).coeff a =
      r * y.coeff a := by
  rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

theorem Tower.jK_transcendental {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  apply GlobalTheory.K4.jK_transcendental <;> assumption

end GlobalTheory.KZ
