module

import ReciprocityTheory.SemistableReduction.SemiContractC
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.MulEqIntegerExists

open NumberField

theorem exists_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ a b : RingOfIntegers E, b ≠ 0 ∧ (algebraMap (RingOfIntegers E) E b) * c
      = algebraMap (RingOfIntegers E) E a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  have : algebraMap (RingOfIntegers E) E b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))
  rw [mul_div_assoc', mul_div_cancel_left₀ _ this]

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.MulEqIntegerExists
