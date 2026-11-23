module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section


theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
