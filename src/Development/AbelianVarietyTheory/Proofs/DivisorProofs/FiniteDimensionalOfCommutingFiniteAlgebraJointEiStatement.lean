module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → FiniteDimensional ℂ (Algebra.adjoin ℂ S) → (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | exact GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen <;> assumption)
