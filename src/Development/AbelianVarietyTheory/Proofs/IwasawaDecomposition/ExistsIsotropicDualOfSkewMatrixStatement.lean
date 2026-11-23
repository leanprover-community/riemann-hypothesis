module

public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualOfSkewMatrix
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

open Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_dual_of_skew_matrix' : ∀ (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε ψ : Fin g → Fin r → ℚ), Mqᵀ = -Mq → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧ (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧ ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  first | exact @GlobalTheory.exists_isotropic_dual_of_skew_matrix | exact GlobalTheory.exists_isotropic_dual_of_skew_matrix | (intros; apply GlobalTheory.exists_isotropic_dual_of_skew_matrix <;> assumption)
