module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_cover_and_cone : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package <;> assumption)
