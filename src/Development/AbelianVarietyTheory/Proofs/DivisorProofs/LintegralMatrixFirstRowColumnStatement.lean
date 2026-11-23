module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn
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
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_matrix_first_row_column : ∀ (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞),
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  first | exact @GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | exact GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | (intros; apply GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner <;> assumption)
