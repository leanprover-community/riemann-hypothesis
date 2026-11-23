module

public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RayPrimeSpan
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem rayPrime_span (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime)
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
  _root_.UpperTheory.Reformulated.B.Qi16.rayPrime_span v p hp hv

theorem UpperTheory.V.CF.rayPrime :
    ∀ (𝔪 : GroundTheory.Global.Modulus ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → p ≡ 1 [MOD Ideal.absNorm 𝔪.ideal] → ∃ hv : ¬ v.asIdeal ∣ 𝔪.ideal, 𝔪.primeClass hv = 1 := by
  intro 𝔪 v p hp hpv hmod
  have hm : (p : 𝓞 ℚ) - 1 ∈ 𝔪.ideal := by
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hp.one_le).1 hmod.symm
    have : (p : 𝓞 ℚ) - 1 = (Ideal.absNorm 𝔪.ideal : 𝓞 ℚ) * c := by
      rw [← Nat.cast_mul, ← hc, Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hv : ¬ v.asIdeal ∣ 𝔪.ideal := by
    intro h
    have h1 := (Ideal.dvd_iff_le.1 h) hm
    have h2 := v.asIdeal.sub_mem hpv h1
    rw [sub_sub_cancel] at h2
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  refine ⟨hv, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  unfold GroundTheory.Global.Modulus.primeClass
  rw [QuotientGroup.eq_one_iff, GroundTheory.Global.Modulus.mem_principalRay]
  refine ⟨Units.mk0 (p : ℚ) hp0, 𝔪.mem_rayUnits.2 ⟨fun w hw => ?_, fun w _ => ?_⟩, ?_⟩
  · have e : ((Units.mk0 (p : ℚ) hp0 : ℚˣ) : ℚ) - 1 = algebraMap (𝓞 ℚ) ℚ ((p : 𝓞 ℚ) - 1) := by simp
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.dvd_iff_le.1 (𝔪.asIdeal_pow_exponent_dvd w) hm
  · simpa using hp.pos
  · apply Units.ext
    rw [coe_toPrincipalIdeal]
    change _ = ((v.asIdeal : Ideal (𝓞 ℚ)) : FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ)
    rw [rayPrime_span v p hp hpv, FractionalIdeal.coeIdeal_span_singleton]
    simp
