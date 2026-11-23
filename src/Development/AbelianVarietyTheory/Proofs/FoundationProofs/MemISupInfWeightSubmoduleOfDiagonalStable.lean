module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightComponentMem
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.WeightDecomp

lemma comp_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) (S : Finset (Ix p q → ℚ)) :
    ∀ f : (Ix p q → ℚ) → V, (∀ ν, f ν ∈ wtSub act ν) → ∑ ν ∈ S, f ν ∈ N → ∀ ν ∈ S, f ν ∈ N := by
  first
  | exact @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | (apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem ..)

theorem mem_iSup_inf_wtSub : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V),
    (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) →
      x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  intro p q V _ _ act N hN x hx hx'
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have h := comp_mem act N hN f.support f hf hx
  refine Submodule.sum_mem _ fun ν hν => ?_
  exact Submodule.mem_iSup_of_mem ν ⟨h ν hν, hf ν⟩

end GlobalTheory.WeightDecomp
