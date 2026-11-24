module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimple
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

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.invariant_subspace_not_semisimple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  first | exact @GlobalTheory.ClassFin.exists_socle_radical_of_not_ss | exact GlobalTheory.ClassFin.exists_socle_radical_of_not_ss | (intros; apply GlobalTheory.ClassFin.exists_socle_radical_of_not_ss <;> assumption)
