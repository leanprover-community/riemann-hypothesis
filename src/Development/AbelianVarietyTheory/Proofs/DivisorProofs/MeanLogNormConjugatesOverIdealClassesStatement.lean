module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormConjugatesOverIdealClasses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mean_log_norm_conjugates_over_ideal_classes : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (β : ℂ) (F : (ℂ ≃+* ℂ) → ℝ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Equidistributed φK j₀ 𝔞 → IsAlgebraic ℚ β → β ≠ 0 → (∀ σ σ' : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ' → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → F σ = F σ') → (∀ σ : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → Real.log ‖σ β‖ ≤ F σ) → ∃ rep : ClassGroup (𝓞 K) → (ℂ ≃+* ℂ), (∀ c, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK (rep c) ∧ ClassGroup.mk K (𝔞 (rep c)) = c) ∧ Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ (minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (NumberField.classNumber K : ℝ)) := by
  first | exact @GlobalTheory.GalMean.galmean | exact GlobalTheory.GalMean.galmean | (intros; apply GlobalTheory.GalMean.galmean <;> assumption)
