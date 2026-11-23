module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerCoeffEqOfIsometricAnalyticModules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.inner_coeff_eq_of_isometric_analytic_modules : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (π₁ π₂ : URep T) (M : GKMod p q) (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ) → (∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) → ∀ g x y, inner ℂ (j₁ x) (π₁.π g (j₁ y)) = inner ℂ (j₂ x) (π₂.π g (j₂ y)) := by
  first | exact @GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic | exact GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic | (intros; apply GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic <;> assumption)
