module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero
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

open scoped Matrix

theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)), (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | exact GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | (intros; apply GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero <;> assumption)
