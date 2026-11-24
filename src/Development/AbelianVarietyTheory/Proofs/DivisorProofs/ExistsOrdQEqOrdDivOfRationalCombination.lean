module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_ordQ_eq_ord_div : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ),
    φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  intro k K _ _ c φ
  induction φ using Finsupp.induction with
  | zero => intro _; exact ⟨1, 1, one_pos, fun E => by simp⟩
  | single_add a b f ha hb ih =>
    intro h0
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h0
      exact hb h0
    have hf0 : f 0 = 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm ha0), zero_add] at h0
      exact h0
    obtain ⟨m, g, hm, hg⟩ := ih hf0
    refine ⟨m * b.den, g ^ b.den * (Units.mk0 a ha0) ^ (b.num * m), ?_, fun E => ?_⟩
    · exact Nat.mul_pos hm b.pos
    · have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.pos.ne'
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [map_add (f := _), Place.ordQ_single, hg E, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, E.ord_mul (pow_ne_zero _ g.ne_zero)
          (zpow_ne_zero _ (Units.mk0 a ha0).ne_zero), E.ord_pow, E.ord_zpow, Units.val_mk0]
      push_cast
      rw [← Rat.mul_den_eq_num b]
      field_simp
      ring

end GlobalTheory.FieldPair
