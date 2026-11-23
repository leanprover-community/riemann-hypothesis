module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn
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

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  first | exact @GlobalTheory.AdaptedExp.exists_adapted_exponent | exact GlobalTheory.AdaptedExp.exists_adapted_exponent | (intros; apply GlobalTheory.AdaptedExp.exists_adapted_exponent <;> assumption)
