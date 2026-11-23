module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPattern
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.normaliser_unipSym_char_pattern : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → 2 ≤ κ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ M : GL (Fin n) k, (∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ ∧ ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h)) → (∀ h ∈ unipSym k n ρ κ, M⁻¹ * h * M ∈ unipSym k n ρ κ) → ∃ s c : kˣ, ∃ h ∈ unipSym k n ρ κ, (M : Matrix (Fin n) (Fin n) k) = midDiag n ρ κ (s : k) (c : k) * (h : Matrix (Fin n) (Fin n) k) := by
  first | exact @GlobalTheory.SymNorm.normaliser_unipSym_char | exact GlobalTheory.SymNorm.normaliser_unipSym_char | (intros; apply GlobalTheory.SymNorm.normaliser_unipSym_char <;> assumption)
