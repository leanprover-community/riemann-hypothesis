module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEquivariantTensorMapOfCyclicCommuting
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  first | exact @GlobalTheory.FockBilin.exists_bilin | exact GlobalTheory.FockBilin.exists_bilin | (intros; apply GlobalTheory.FockBilin.exists_bilin <;> assumption)
