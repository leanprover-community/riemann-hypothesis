module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  first | exact @GlobalTheory.HoweR.re_diag_le_of_eigen_bound | exact GlobalTheory.HoweR.re_diag_le_of_eigen_bound | (intros; apply GlobalTheory.HoweR.re_diag_le_of_eigen_bound <;> assumption)
