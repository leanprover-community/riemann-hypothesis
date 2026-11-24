module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
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

@[expose] public section

open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

theorem _root_.GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) → (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) → glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  first | exact @GlobalTheory.ChartGlue.glueMeas_add_of_compat_on | exact GlobalTheory.ChartGlue.glueMeas_add_of_compat_on | (intros; apply GlobalTheory.ChartGlue.glueMeas_add_of_compat_on <;> assumption)
