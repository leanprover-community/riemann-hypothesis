module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsExactIdeal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Counts

variable {K : Type} [Field K] [NumberField K]

theorem count_span_mul (P : HeightOneSpectrum (𝓞 K)) {y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (y * z)) =
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y) +
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) z) := by
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have hz' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) z ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hz
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K P hy' hz']

theorem count_span_inv (P : HeightOneSpectrum (𝓞 K)) (y : K) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y⁻¹) =
      - FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y) := by
  by_cases hy : y = 0
  · simp [hy, FractionalIdeal.count_zero]
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have hyi : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y⁻¹ ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have h := FractionalIdeal.count_mul K P hyi hy'
  rw [FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hy,
    FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one] at h
  omega

theorem count_span_prod {ι : Type} (P : HeightOneSpectrum (𝓞 K)) (s : Finset ι) (z : ι → K)
    (hz : ∀ i, z i ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (∏ i ∈ s, z i)) =
      ∑ i ∈ s, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (z i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FractionalIdeal.count_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, count_span_mul P (hz a)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hz i), ih]

theorem count_le_of_integral {ι : Type} [Fintype ι] (P : HeightOneSpectrum (𝓞 K)) (c : K) (s : 𝓞 K)
    (z : ι → K) (hc : c ≠ 0) (hs : s ∉ P.asIdeal) (hz : ∀ i, z i ≠ 0)
    (hw : c⁻¹ * (s : K) * ∏ i, z i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c) ≤
      ∑ i, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (z i)) := by
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact P.asIdeal.zero_mem
  have hprod : ∏ i, z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hz i
  have hw0 : c⁻¹ * (s : K) * ∏ i, z i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (inv_ne_zero hc) hs0) hprod
  have h1 := count_le_of_mem (K := K) P hw hw0
  rw [FractionalIdeal.count_one, count_span_mul P (mul_ne_zero (inv_ne_zero hc) hs0) hprod,
    count_span_mul P (inv_ne_zero hc) hs0, count_span_inv, count_span_prod P _ _ hz] at h1
  have h2 : FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (s : K)) = 0 :=
    count_span_unit (K := K) P s hs
  rw [h2] at h1
  linarith

end Counts

end PI.UnitaryGroupMassFormula.CntFormula.R6
