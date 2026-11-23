module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotent
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

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e = c • e) → (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (exact GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (intros; apply GlobalTheory.azumaya_algEquiv_matrix_of_idempotent  <;> assumption)
