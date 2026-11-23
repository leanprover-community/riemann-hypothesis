module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducible
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_reynolds_of_completelyReducible' : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Set (V →ₗ[ℂ] V)), (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', s v ∈ U') ∧ IsCompl U U') → ∃ Rey : V →ₗ[ℂ] V, (∀ v, ∀ s ∈ S, s (Rey v) = Rey v) ∧ (∀ v, (∀ s ∈ S, s v = v) → Rey v = v) ∧ (∀ v, ∀ s ∈ S, Rey (s v) = Rey v) ∧ (∀ v, v - Rey v ∈ Submodule.span ℂ {x | ∃ s ∈ S, ∃ w, x = s w - w}) ∧ (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, Rey (T v) = T (Rey v)) ∧ ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∀ v ∈ U, Rey v ∈ U := by
  first | exact @GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | exact GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | (intros; apply GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible <;> assumption)
