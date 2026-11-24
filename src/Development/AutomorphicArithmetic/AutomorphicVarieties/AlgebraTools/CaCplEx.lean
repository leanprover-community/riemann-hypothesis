module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, ← ha, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply]
  simp

theorem UpperTheory.V.AlgebraTools.isCplAt_cplAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime], IsCplAt R p (CplAt R p) := by
  intro R _ _ p _
  let L := Localization.AtPrime p
  have hRB : ∀ r : R, algebraMap R (CplAt R p) r =
      algebraMap L (CplAt R p) (algebraMap R L r) := fun r =>
    IsScalarTower.algebraMap_apply R L (CplAt R p) r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion L (maximalIdeal L), inferInstance, ?_, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R L (CplAt R p), ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal
  · intro n b
    obtain ⟨a', ha'⟩ := dense_loc L n b
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
    refine ⟨r, s, s.2, ?_⟩
    have e : algebraMap R (CplAt R p) s * b - algebraMap R (CplAt R p) r =
        algebraMap R (CplAt R p) s *
          (b - algebraMap L (CplAt R p) (IsLocalization.mk' L r s)) := by
      rw [mul_sub, hRB, hRB, ← map_mul, mul_comm (algebraMap R L s), IsLocalization.mk'_spec]
    rw [e]
    exact Ideal.mul_mem_left _ _ ha'
  · intro n a ha
    rw [hRB] at ha
    have h1 := strict_loc L n _ ha
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff p.primeCompl] at h1
    obtain ⟨⟨⟨b, hb⟩, s⟩, hx⟩ := h1
    simp only [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl L).1 hx
    refine ⟨c * s, ?_, ?_⟩
    · exact p.primeCompl.mul_mem c.2 s.2
    · have : (c : R) * s * a = c * b := by
        rw [mul_assoc, mul_comm (s : R) a]
        exact hc
      rw [this]
      exact Ideal.mul_mem_left _ _ hb
