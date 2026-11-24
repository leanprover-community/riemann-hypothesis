module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin

theorem _root_.GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  first | exact @GlobalTheory.unipotent_upper_inv_bounded | exact GlobalTheory.unipotent_upper_inv_bounded | (intros; apply GlobalTheory.unipotent_upper_inv_bounded <;> assumption)
