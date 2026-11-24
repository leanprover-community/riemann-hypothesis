module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasisSubsetOfSaturatedSubmodule
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.exists_basis_subset_of_saturated_submodule : ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ), (∀ (v : Λ) (n : ℤ), n ≠ 0 → n • v ∈ N → v ∈ N) → ∃ (k n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n), Function.Injective f ∧ Submodule.span ℤ (Set.range fun i => b (f i)) = N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated | exact GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.Lattice.exists_basis_span_eq_of_saturated <;> assumption)
