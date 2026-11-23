module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst_poly : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ g : MvPolynomial τ Q, HasVal p z (subst (up Q u) (g : MvPowerSeries τ Q)) (MvPolynomial.eval (fun j => algebraMap B Q (E (u j))) g) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u hu g
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  induction g using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [MvPolynomial.coe_monomial, subst_monomial ha, MvPolynomial.eval_monomial]
    have hprod : α.prod (fun s n => (up Q u s) ^ n) = map (algebraMap B Q) (α.prod fun s n => (u s) ^ n) := by
      simp [up, Finsupp.prod, map_prod, map_pow]
    have hEp : E (α.prod fun s n => (u s) ^ n) = α.prod fun s n => (E (u s)) ^ n := by
      simp [Finsupp.prod, map_prod, map_pow]
    have hv := GlobalTheory.T.hasPAdicPowerSeriesValue_map_of_continuousEvaluation p B O Q θ hF σ z hz E hE (α.prod fun s n => (u s) ^ n)
    have hs := (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ 0 _ 0 hv).2.1 c
    rw [hprod]
    convert hs using 1
    · rw [MvPowerSeries.smul_eq_C_mul]; rfl
    · rw [hEp]; simp [Finsupp.prod, map_prod, map_pow]
  | add f g hf hg =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add (f := _)]
    exact (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ _ _ _ hf).1 hg

end GlobalTheory.QLog
