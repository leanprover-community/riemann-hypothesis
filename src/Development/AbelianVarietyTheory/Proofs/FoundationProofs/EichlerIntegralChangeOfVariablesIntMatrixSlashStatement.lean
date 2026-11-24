module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralChangeOfVariablesIntMatrixSlash
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerIntegral_changeOfVariables_intMatrix_slash : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ (β : Matrix (Fin 2) (Fin 2) ℤ), 0 < β.det → ∀ τ : ℍ, slP (k - 2) β (eichler (k - 2) f (toGL β • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] toGL β) τ + slP (k - 2) β (eichler (k - 2) f (toGL β • UpperHalfPlane.I)) := by
  first | exact @GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul | exact GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul | (intros; apply GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul <;> assumption)
