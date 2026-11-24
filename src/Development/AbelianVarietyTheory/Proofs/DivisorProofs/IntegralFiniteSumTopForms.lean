module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralAddStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem isTopForm_hasInt_finset_sum {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n))
    (he : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (hc : ∀ y, ∃ i, y ∈ (e i).source) {S : Set Y} (hS : MeasurableSet S) {ι : Type}
    {d : ι → κ → Y → ℝ} {t : ι → ℝ} (hd : ∀ a, IsTopForm e (d a) S) (ht : ∀ a, HasInt e (d a) S (t a))
    (s : Finset ι) :
    IsTopForm e (fun i y => ∑ a ∈ s, d a i y) S ∧ HasInt e (fun i y => ∑ a ∈ s, d a i y) S (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨fun _ _ _ _ _ _ => by simp, fun _ => aemeasurable_const⟩, GlobalTheory.T.hasTopFormChartIntegral_zero e S⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    obtain ⟨hF, hI⟩ := ih
    refine ⟨⟨fun i j y hy hi hj => ?_, fun i => ((hd a).meas i).add (hF.meas i)⟩,
      GlobalTheory.T.topFormIntegral_add e he hc hS (hd a) hF (ht a) hI⟩
    rw [(hd a).trans i j y hy hi hj, hF.trans i j y hy hi hj]
    ring

theorem hasInt_sum : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι]
    {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) →
    HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  intro n Y κ _ _ _ _ e he hc S hS ι _ d t hd ht
  exact (isTopForm_hasInt_finset_sum e he hc hS hd ht Finset.univ).2

end GlobalTheory.GoodTop
