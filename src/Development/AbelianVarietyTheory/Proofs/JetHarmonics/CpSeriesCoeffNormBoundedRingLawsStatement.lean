module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
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

theorem _root_.GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  first | exact @GlobalTheory.MomOne.sup_norm_laws | exact GlobalTheory.MomOne.sup_norm_laws | (intros; apply GlobalTheory.MomOne.sup_norm_laws <;> assumption)
