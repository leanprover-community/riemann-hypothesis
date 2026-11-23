module

public import Formalism.EisensteinCokernelLengths.RationalTailBound
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Basic.ENNReal.Real

@[expose] public section

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

private theorem le_addVal_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (hc : c ∈ Ideal.span {ϖ ^ e}) : (e : ℕ∞) ≤ IsDiscreteValuationRing.addVal O c := by
  rw [Ideal.mem_span_singleton] at hc
  have h := (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).2 hc
  rwa [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one] at h

private theorem addVal_eq_of_mem_span_pow_not_mem_succ {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (h1 : c ∈ Ideal.span {ϖ ^ e}) (h2 : c ∉ Ideal.span {ϖ ^ (e + 1)}) :
    IsDiscreteValuationRing.addVal O c = e := by
  refine le_antisymm ?_ (le_addVal_of_mem_span_pow hϖ h1)
  by_contra h
  rw [not_le] at h
  apply h2
  rw [Ideal.mem_span_singleton]
  apply (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).1
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one, Nat.cast_succ]
  exact Order.add_one_le_of_lt h

theorem gaussValEisenstein : GaussEisRam := by
  intro O _ _ _ ϖ hϖ e he x hx E N hN hE
  obtain ⟨hmon, hdeg, hcoef, h0⟩ := hE
  have hc0 : IsDiscreteValuationRing.addVal O (E.coeff 0) = e :=
    addVal_eq_of_mem_span_pow_not_mem_succ hϖ (hcoef 0 (by omega)) h0
  have hcN : E.coeff N = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  unfold Formalism.NOK.gaussV
  simp only [Polynomial.coeff_coe]
  apply le_antisymm
  · have h1 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) 0
    have h2 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) N
    simp only [hc0, hcN, AddValuation.map_one, ENat.toENNReal_zero, ENat.toENNReal_coe,
      Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero, zero_add] at h1 h2
    rcases le_total (e : ℝ) (x * N) with h | h
    · rw [min_eq_left h, ENNReal.ofReal_natCast]
      exact h1
    · rw [min_eq_right h]
      exact h2
  · apply le_iInf
    intro n
    rcases lt_trichotomy n N with h | h | h
    · have hv := le_addVal_of_mem_span_pow hϖ (hcoef n h)
      calc ENNReal.ofReal (min (e : ℝ) (x * N)) ≤ ENNReal.ofReal (e : ℝ) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ((e : ℕ∞) : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
        _ ≤ ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.2 hv
        _ ≤ _ := le_self_add
    · subst h
      rw [hcN, AddValuation.map_one, ENat.toENNReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h)]
      simp

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
