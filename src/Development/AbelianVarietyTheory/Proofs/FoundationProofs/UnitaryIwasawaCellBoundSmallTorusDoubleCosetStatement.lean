module

public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCoset
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  first | exact @GlobalTheory.LFun.CellBound.cell_bound | exact GlobalTheory.LFun.CellBound.cell_bound | (intros; apply GlobalTheory.LFun.CellBound.cell_bound <;> assumption)
