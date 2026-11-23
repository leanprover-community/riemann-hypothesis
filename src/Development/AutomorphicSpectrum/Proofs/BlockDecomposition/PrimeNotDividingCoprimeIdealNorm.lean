module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.DeligneRibet

theorem absNorm_not_dvd_of_sup_span_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F),
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  intro F _ _ l hl 𝔟 h hdvd
  have h1 : (1 : 𝓞 F) ∈ 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  by_cases h𝔟 : 𝔟 = ⊥
  · subst h𝔟
    rw [bot_sup_eq] at h
    have hnorm := Ideal.absNorm_span_singleton (l : 𝓞 F)
    rw [h, Ideal.absNorm_top] at hnorm
    have hcast : (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hnorm
    have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp hnorm.symm with h' | h'
    · exact hl.one_lt.ne' h'
    · omega
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔟 h𝔟
    haveI := Fact.mk hl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
    have hlx : (l : 𝓞 F ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : Ideal.Quotient.mk 𝔟 a * (l : 𝓞 F ⧸ 𝔟) = 1 := by
      have key := congrArg (Ideal.Quotient.mk 𝔟) hbc
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, map_natCast,
        map_one] at key
      exact key
    have hx0 : x = 0 := by
      rw [← one_mul x, ← hunit, mul_assoc, hlx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hl.one_lt.ne hx

end GlobalTheory.CompanionTheory.DeligneRibet
