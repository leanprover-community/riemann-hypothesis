module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  first | exact @GlobalTheory.JSW.norm_fderiv_chart_le | exact GlobalTheory.JSW.norm_fderiv_chart_le | (intros; apply GlobalTheory.JSW.norm_fderiv_chart_le <;> assumption)
