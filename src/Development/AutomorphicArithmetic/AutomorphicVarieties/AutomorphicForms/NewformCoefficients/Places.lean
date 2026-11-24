module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

theorem UpperTheory.V.Af.Nf.places :
    UpperTheory.V.Af.Nf.Places := by
  intro w
  have hq := Rat.HeightOneSpectrum.prime_natGenerator w
  have hspan := Rat.HeightOneSpectrum.span_natGenerator w
  have hN : normV w = Rat.HeightOneSpectrum.natGenerator w := by
    unfold normV
    rw [Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hspan).toEquiv,
      Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]
  have hP : w.asIdeal =
      Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
    ext x
    rw [Ideal.mem_span_singleton,
      ← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), ← hspan,
      Ideal.mem_span_singleton,
      ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]
  refine ⟨by rw [hN]; exact hq, by rw [hN]; exact hP, ?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · intro M hM hndvd
    unfold UpperTheory.V.Af.Nf.lev ordI
    have hne : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : M ≠ 0)
    by_contra hc
    rw [← Ne, Associates.count_ne_zero_iff_dvd hne w.irreducible, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem] at hc
    apply hndvd
    rw [hN, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) M, Ideal.apply_mem_of_equiv_iff]
    exact hc
