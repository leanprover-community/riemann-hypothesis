module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  first | exact @GlobalTheory.EnvelopingExtension.exists_algHom_unitary | exact GlobalTheory.EnvelopingExtension.exists_algHom_unitary | (intros; apply GlobalTheory.EnvelopingExtension.exists_algHom_unitary <;> assumption)
