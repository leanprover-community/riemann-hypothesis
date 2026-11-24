module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CellDec
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 E))) (𝓕 : Set (GA E n)), IsFundamentalDomain (NE E n) 𝓕 μ → ∀ B : ℝ → GA E n → ℝ, Continuous (Function.uncurry B) → (∀ x g, 0 ≤ B x g) → (∀ x, 0 < B x 1) → (∀ x, ∀ u ∈ NA E n, ∀ g, B x (u * g) = B x g) → (∃ K : Set (GA E n), IsCompact K ∧ ∀ x g, g ∈ C0 E n S → B x g ≠ 0 → ∃ u ∈ NA E n, u * g ∈ K) → (∀ x, 0 < ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ ∧ ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ < ⊤) ∧ Continuous fun x => (∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ).toReal := by
  first | exact @GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | exact GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | (intros; apply GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous <;> assumption)
