module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IwasawaDecompositionRealMatrix
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
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.iwasawa_decomposition_real_matrix : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ g = k * diagonal a * n := by
  first | exact @GlobalTheory.ClassFin.iwasawa_real | exact GlobalTheory.ClassFin.iwasawa_real | (intros; apply GlobalTheory.ClassFin.iwasawa_real <;> assumption)
