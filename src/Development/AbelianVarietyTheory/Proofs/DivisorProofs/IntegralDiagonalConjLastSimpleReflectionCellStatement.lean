module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalConjLastSimpleReflectionCell
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.integral_diagonal_conj_lastSimpleReflectionCell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) * ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        ‖(q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)))‖ₑ * ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last | exact GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last <;> assumption)
