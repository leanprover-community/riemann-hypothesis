module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapCommStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongrStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrobStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
