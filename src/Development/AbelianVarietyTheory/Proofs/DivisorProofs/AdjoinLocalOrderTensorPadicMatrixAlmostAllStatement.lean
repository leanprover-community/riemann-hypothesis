module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Mathlib.Algebra.Central.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAll
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

open scoped TensorProduct
open GlobalTheory.LKInvGood

theorem _root_.GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  first | (exact @GlobalTheory.LocMatrix.locOrder_matrix) | (exact GlobalTheory.LocMatrix.locOrder_matrix) | (intros; apply GlobalTheory.LocMatrix.locOrder_matrix  <;> assumption)
