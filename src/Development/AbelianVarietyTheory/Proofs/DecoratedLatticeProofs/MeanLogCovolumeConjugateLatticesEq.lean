module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.MeanLogArea

theorem mean_log_area : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hn : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  have hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) =
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) +
        (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Real.log_div (hpos ρ).ne' Real.pi_pos.ne']
    ring
  rw [hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]
  unfold ClassMeanPeriods.classMeanValue
  rw [hmean]
  ring

end GlobalTheory.MeanLogArea
