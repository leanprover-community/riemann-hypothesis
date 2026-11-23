module

public import Formalism.MirabolicMackeyTheory.StatementT
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsPowLocKMulInfEqOneOfLevelLeTwo
public import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralCmTypeUnitaryPartMulAbsNormPow
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.DivisionValues (vw)

namespace UpperTheory.FlipVal

theorem vw_ge {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {q : ℕ} (hq : q ≠ 0)
    (n : ℕ) (h : IsIntegral ℤ ((q : K) ^ n * y)) : -((n : ℤ) * vw w (q : K)) ≤ vw w y := by
  have hq' : (q : K) ≠ 0 := by exact_mod_cast hq
  have h0 : 0 ≤ vw w ((q : K) ^ n * y) := by
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (q : K) ^ n * y := ⟨⟨_, h⟩, rfl⟩
    rw [← ha, vw, ← FractionalIdeal.coeIdeal_span_singleton]
    exact FractionalIdeal.count_coe_nonneg K w _
  rw [vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
    FractionalIdeal.count_mul K w (pow_ne_zero _ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hq'))
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy), FractionalIdeal.count_pow] at h0
  unfold vw
  linarith

theorem vw_nat_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (q : ℕ) : 0 ≤ vw w (q : K) := by
  rw [← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_absNorm {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (h : ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    vw w ((Ideal.absNorm P.asIdeal : ℕ) : K) = 0 := by
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hmax := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))
  have h1 : Ideal.absNorm P.asIdeal = Formalism.EigenvalueLevelCeiling.plc P ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]; rfl
  have h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    rw [h1, Nat.cast_pow]; exact fun h' => h (w.isPrime.mem_of_pow_mem _ h')
  have h3 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 K) ≠ 0 := fun h' => h2 (h' ▸ zero_mem _)
  rw [← map_natCast (algebraMap (𝓞 K) K), vw, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w (by simpa using h3)]
  by_contra h4
  refine h2 ((Ideal.dvd_span_singleton).1 ?_)
  exact (Associates.count_ne_zero_iff_dvd (by simpa using h3) w.irreducible).1 (by exact_mod_cast h4)

theorem val_int {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ v, v ∉ S → χ.UnrAt v) (hl : ∀ v, χ.LevelLe v 2) {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i))) (n : I → ℤ) (hn : χ.HasInf φ n)
    (M : ℕ) (hM : ∀ i, (n i).natAbs ≤ M) (P : HeightOneSpectrum (𝓞 E)) :
    IsIntegral ℤ (((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ M * (χ.val P : ℂ)) ∧
      IsIntegral ℤ (((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ M * (χ.val P : ℂ)⁻¹) := by
  obtain ⟨h, z, h0, hP, hQ, H⟩ := UpperTheory.exists_pow_locK_mul_inf_eq_one_of_levelLe_two E χ S hS hl P (Formalism.L2.Host.unif P)
  have hu : P.valuation E (Formalism.L2.Host.unif P : E) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm.trans (Formalism.L2.Host.unif_spec P)
  rw [hu, ← WithZero.exp_nsmul, show h • (-1 : ℤ) = -(h : ℤ) by simp] at hP
  have H' : (χ.val P : ℂ) ^ h * ∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i = 1 := by
    rw [← hn z]; exact congrArg Units.val H
  constructor
  · refine IsIntegral.of_pow h0 ?_
    have := UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ (fun i => -n i) M (fun i => by simpa using hM i) P h z hP hQ
    simp only [zpow_neg, Finset.prod_inv_distrib] at this
    rwa [← eq_inv_of_mul_eq_one_left H', mul_comm, mul_comm h, pow_mul, ← mul_pow] at this
  · refine IsIntegral.of_pow h0 ?_
    have := UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow E I φ hφ n M hM P h z hP hQ
    rwa [eq_inv_of_mul_eq_one_right H', mul_comm, mul_comm h, pow_mul, ← inv_pow, ← mul_pow] at this

end UpperTheory.FlipVal
