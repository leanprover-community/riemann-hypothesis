module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) := by
  first | exact @GlobalTheory.MomOne.MulSeries.mulS_laws | exact GlobalTheory.MomOne.MulSeries.mulS_laws | (intros; apply GlobalTheory.MomOne.MulSeries.mulS_laws <;> assumption)
