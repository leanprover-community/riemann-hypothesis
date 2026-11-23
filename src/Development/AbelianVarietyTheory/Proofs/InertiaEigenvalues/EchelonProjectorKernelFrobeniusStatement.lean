module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EchelonProjectorKernelFrobenius
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

open scoped NNReal

theorem _root_.GlobalTheory.T.echelon_projector_kernel_frobenius : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l] (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C), A.det ≠ 0 → Y.map (frobenius C l) = Y * A → ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧ (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧ (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧ Q = A * Q.map (frobenius C l) * Λ := by
  first | exact @GlobalTheory.echelon_projector_frobenius | exact GlobalTheory.echelon_projector_frobenius | (intros; apply GlobalTheory.echelon_projector_frobenius <;> assumption)
