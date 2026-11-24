module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_assoc :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (e f h : G → ℂ) (C : ℝ),
      Continuous e → Integrable e μ → Continuous f → Integrable f μ → Continuous h → (∀ g, ‖h g‖ ≤ C) →
      (∀ x, conv μ e f x = f x) → ∀ x, conv μ f h x = conv μ e (conv μ f h) x := by
  intro G _ _ _ _ _ _ _ _ μ _ e f h C _ hei _ hfi hh hC hef x
  have h1 : Integrable (fun z : G × G => e z.1 * f z.2) (μ.prod μ) := hei.mul_prod hfi
  have h2 : Integrable (fun z : G × G => e z.1 * f (z.1⁻¹ * z.2)) (μ.prod μ) :=
    (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable h1
  have h3 : Integrable (fun z : G × G => e z.1 * f (z.1⁻¹ * z.2) * h (z.2⁻¹ * x)) (μ.prod μ) := by
    refine h2.mul_bdd (c := C) ?_ (Eventually.of_forall fun z => hC _)
    exact (hh.comp (continuous_snd.inv.mul continuous_const)).aestronglyMeasurable
  have h4 : ∀ g : G, conv μ f h (g⁻¹ * x) = ∫ y, f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self (fun y => f (g⁻¹ * y) * h (y⁻¹ * x)) g]
    simp only [conv, inv_mul_cancel_left, mul_inv_rev, mul_assoc]
  calc conv μ f h x = ∫ y, ∫ g, e g * f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ ∂μ := by
        unfold conv
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [integral_mul_const, ← hef y]
        rfl
    _ = ∫ g, ∫ y, e g * f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ ∂μ :=
        (integral_integral_swap (f := fun g y => e g * f (g⁻¹ * y) * h (y⁻¹ * x)) h3).symm
    _ = conv μ e (conv μ f h) x := by
        show _ = ∫ g, e g * conv μ f h (g⁻¹ * x) ∂μ
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        beta_reduce
        rw [h4, ← integral_const_mul]
        simp only [mul_assoc]
