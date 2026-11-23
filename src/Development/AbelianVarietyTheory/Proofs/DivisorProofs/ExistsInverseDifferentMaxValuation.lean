module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem invDifferent_exists_max_valuation :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧
      (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
      ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
        w.valuation E f ≤ w.valuation E e := by
  intro E _ _ w
  classical

  have hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      IsIntegral ℤ ((NumberField.discr E : E) * f) := by
    intro f hf
    have hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
      have h := hf y
      rw [IsIntegrallyClosed.isIntegral_iff] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply, hk, mul_comm]
    have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
      (1 : Submodule (𝓞 E) E) hb h1 hmem
    rw [← coe_discr, Algebra.smul_def, mul_one] at this
    simpa using this
  have hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      w.valuation E ((NumberField.discr E : E) * f) ≤ 1 := by
    intro f hf
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)
    rw [← hy]
    exact w.valuation_le_one y
  have hd0 : (NumberField.discr E : E) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hvd : w.valuation E (NumberField.discr E : E) ≠ 0 := by simpa using hd0
  have hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1)) := fun o => by
    rw [mul_one]; exact Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  let S : ℤ → Prop := fun k => ∃ f : E, f ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧
      WithZero.log (w.valuation E f) = k
  have hbdd : ∃ b, ∀ z, S z → z ≤ b := by
    refine ⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩
    rintro z ⟨f, hf0, hf, rfl⟩
    have hvf : w.valuation E f ≠ 0 := by simpa using hf0
    have h := hle f hf
    rw [map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hne : ∃ z, S z := ⟨_, 1, one_ne_zero, hP1, rfl⟩
  obtain ⟨k, ⟨e, he0, he, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨e, he0, he, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hvf : w.valuation E f ≠ 0 := by simpa using hf0
  have hve : w.valuation E e ≠ 0 := by simpa using he0
  have h := hmax _ ⟨f, hf0, hf, rfl⟩
  rw [← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]
  exact h

end GlobalTheory
