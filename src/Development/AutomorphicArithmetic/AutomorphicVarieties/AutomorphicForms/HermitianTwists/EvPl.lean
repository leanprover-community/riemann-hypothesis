module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Rn.evPl :
    UpperTheory.V.Af.Rn.EvPl := by
  have hinj : Function.Injective fun w : HeightOneSpectrum (𝓞 ℚ) => normV w := fun v w h =>
    HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])
  refine ⟨fun P => ⟨fun h => ?_, fun h => ?_⟩, fun M hM => ?_⟩
  · refine Filter.eventually_cofinite.2
      (((Filter.eventually_cofinite.1 h).image fun w => normV w).subset fun p hp => ?_)
    obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
    have hex : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
      have hprime : Prime (p : 𝓞 ℚ) := by
        have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
        rw [e]
        exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
          (Nat.prime_iff_prime_int.mp hp)
      let w : HeightOneSpectrum (𝓞 ℚ) :=
        ⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime,
          by rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero⟩
      refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
      change Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
      rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
      simp
    obtain ⟨w, rfl⟩ := hex
    exact ⟨w, hne, rfl⟩
  · filter_upwards [hinj.tendsto_cofinite.eventually h] with w hw
    exact hw (places w).1
  · filter_upwards [hinj.tendsto_cofinite.eventually (Set.finite_le_nat M).eventually_cofinite_notMem] with w hw
    exact fun h => hw (Nat.le_of_dvd hM h)
