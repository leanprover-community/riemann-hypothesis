module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLeviPshRegularization
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

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.local_levi_psh_regularization : ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (q ph : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) (2)) → ContDiffOn ℝ ∞ ph (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) (fun z => q z + ph z) → (∀ z ∈ ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ ph z ∧ ph z ≤ C₅) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ ph z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ (C t₀ : ℝ) (phT : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ (∀ t, 0 < t → t ≤ t₀ → ContDiffOn ℝ ∞ (phT t) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (fun z => q z + phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ C ∧ -C * Real.log (Real.log (1 / t)) ≤ phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, ph z ≤ phT t z ∧ (rLoc S m z ≤ Real.log (1 / t) + K → phT t z ≤ ph z + t ^ ((1 : ℝ) / 3))) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), polyMaxOff S (fun x => q x + ph x) z t - epsT C t ≤ q z + phT t z ∧ q z + phT t z ≤ polyMaxOff S (fun x => q x + ph x) z t) ∧ ∀ t', t ≤ t' → t' ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ phT t' z + epsT C t') ∧ ∀ K' ⊆ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, IsCompact K' → TendstoUniformlyOn (fun t => phT t) (ph) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (phT t)) (fderiv ℝ (ph)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t))) (fderiv ℝ (fderiv ℝ (ph))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (phT t) z - fderiv ℝ (ph) z‖ ≤ M * t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart | exact GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart <;> assumption)
