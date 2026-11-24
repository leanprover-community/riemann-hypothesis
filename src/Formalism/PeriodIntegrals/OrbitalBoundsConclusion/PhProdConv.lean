module

public import Formalism.PeriodIntegrals.PhProdConv
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
public import Mathlib.MeasureTheory.Integral.Pi
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

theorem isConvIdempotent_pi : PI.PhProdConv.ProdConv := by
  intro ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv
  refine ⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩
  unfold PI.PhProdConv.PhConv
  refine ⟨?_, fun g => ?_, fun x y => ?_⟩
  · exact Finset.prod_eq_one (fun i _ => (hconv i).1)
  · change ∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))
  · have key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) =
        fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i) := by
      funext g
      rw [← Finset.prod_mul_distrib]
      rfl
    change MeasureTheory.Integrable
        (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i))
        (MeasureTheory.Measure.pi μ) ∧
      ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g
        ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)
    rw [key]
    refine ⟨MeasureTheory.Integrable.fintype_prod_dep
      (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)
