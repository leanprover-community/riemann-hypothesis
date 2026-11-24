module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideDescendsFinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.number_field_approximate_identity : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf <;> assumption)
