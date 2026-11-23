module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomial
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

theorem _root_.GlobalTheory.T.snc_resolution_transition_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → (∀ p : (k : K) → ι k, SncRes.coord P p '' SncRes.src P p = {t | ∀ h ∈ SncRes.ideal P p, eval t h = 0}) ∧ ∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), eval (SncRes.coord P p x) q ≠ 0 ∧ ∀ y ∈ SncRes.src P p ∩ SncRes.src P p', eval (SncRes.coord P p y) q ≠ 0 → ∀ l, SncRes.coord P p' y l * eval (SncRes.coord P p y) q = eval (SncRes.coord P p y) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans <;> assumption)
