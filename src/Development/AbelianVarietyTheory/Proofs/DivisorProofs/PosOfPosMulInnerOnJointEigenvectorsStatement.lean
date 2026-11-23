module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosOfPosMulInnerOnJointEigenvectors
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


theorem _root_.GlobalTheory.T.inner_pos_of_pos_on_joint_eigenvectors : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  first | exact @GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | exact GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | (intros; apply GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors <;> assumption)
