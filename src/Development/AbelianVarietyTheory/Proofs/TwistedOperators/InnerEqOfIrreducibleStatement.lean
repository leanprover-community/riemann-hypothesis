module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducible
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

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y))) → Function.Injective j₂ → IrrGK M → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → Module.finrank ℂ ↥(hwSub M.act μ) = 1 → inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v) → ∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  first | exact @GlobalTheory.InvFormUnique.inner_eq_of_irreducible | exact GlobalTheory.InvFormUnique.inner_eq_of_irreducible | (intros; apply GlobalTheory.InvFormUnique.inner_eq_of_irreducible <;> assumption)
