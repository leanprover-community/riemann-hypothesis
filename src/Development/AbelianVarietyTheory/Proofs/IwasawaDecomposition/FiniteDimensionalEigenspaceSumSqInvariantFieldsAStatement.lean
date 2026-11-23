module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalEigenspaceSumSqInvariantFieldsA
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

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  first | exact @GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | exact GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields | (intros; apply GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields <;> assumption)
