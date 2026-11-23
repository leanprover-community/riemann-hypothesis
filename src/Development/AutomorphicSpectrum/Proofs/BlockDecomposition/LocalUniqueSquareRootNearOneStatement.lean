module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUniqueSquareRootNearOne
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

open MeasureTheory
open scoped ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.local_unique_square_root_near_one : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V), Continuous ψ → Continuous ψ.symm → ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧ (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  first | exact @GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | exact GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | (intros; apply GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt <;> assumption)
