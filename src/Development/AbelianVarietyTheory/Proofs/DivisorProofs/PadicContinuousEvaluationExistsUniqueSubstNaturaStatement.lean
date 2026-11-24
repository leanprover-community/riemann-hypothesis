module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural : ∀ (p : ℕ) (R A σ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype σ] [IsAdicComplete (Ideal.span {(p : A)}) A] (x : σ → A), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∃! E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E) ∧ ∀ E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E → (∀ (τ : Type) [Fintype τ] (u : τ → MvPowerSeries σ R) (E' : MvPowerSeries τ R →ₐ[R] A), (∀ j, constantCoeff (u j) = 0) → IsEval p (fun j => E (u j)) E' → ∀ f, E (subst u f) = E' f) ∧ (∀ f, constantCoeff f = 0 → ∃ N : ℕ, (p : A) ∣ E f ^ N) ∧ ∀ (R' A' : Type) [CommRing R'] [CommRing A'] [Algebra R' A'] [IsHausdorff (Ideal.span {(p : A')}) A'] (r : R →+* R') (g : A →+* A') (E' : MvPowerSeries σ R' →ₐ[R'] A'), (∀ c, g (algebraMap R A c) = algebraMap R' A' (r c)) → IsEval p (fun i => g (x i)) E' → ∀ f, g (E f) = E' (map r f) := by
  first | exact @GlobalTheory.CEval.continuous_eval | exact GlobalTheory.CEval.continuous_eval | (intros; apply GlobalTheory.CEval.continuous_eval <;> assumption)
