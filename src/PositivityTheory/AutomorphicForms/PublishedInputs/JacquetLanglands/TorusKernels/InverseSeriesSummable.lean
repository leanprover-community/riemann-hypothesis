module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UpperTheory.Esk.InverseSeriesLemmas

theorem enorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (x : ℂ) : ‖r • x‖ₑ = ENNReal.ofReal r * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal hr]

theorem hasSum_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : HasSum (fun g : G => b (g⁻¹ • y)) 1 := by
  have h := (Equiv.inv G).hasSum_iff.mpr (hb.sum y)
  exact h

theorem tsum_ofReal_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
  have hs := UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb y
  calc ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ENNReal.ofReal (∑' g : G, b (g⁻¹ • y)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) hs.summable).symm
    _ = 1 := by rw [hs.tsum_eq, ENNReal.ofReal_one]

end UpperTheory.Esk.InverseSeriesLemmas

open UpperTheory.Esk.InverseSeriesLemmas in
theorem UpperTheory.Esk.inverse_series_summable : UpperTheory.Esk.C3 := by
  unfold UpperTheory.Esk.C3
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  have hμ' : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ := hμ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → Y → ℂ, ∀ g y, Φ g y = b y • f (g • y) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G → Y → ℂ, ∀ g y, Ψ g y = b (g⁻¹ • y) • f y := ⟨_, fun _ _ => rfl⟩
  have hΦm : ∀ g, Measurable (Φ g) := by
    intro g
    rw [show Φ g = fun y => b y • f (g • y) from funext (hΦ g)]
    exact hb.meas.smul (hf.comp (hμ' g).measurable)
  have hΨm : ∀ g, Measurable (Ψ g) := by
    intro g
    rw [show Ψ g = fun y => b (g⁻¹ • y) • f y from funext (hΨ g)]
    exact (hb.meas.comp (hμ' g⁻¹).measurable).smul hf
  have emb : ∀ g : G, MeasurableEmbedding (fun y : Y => g • y) := fun g =>
    (MeasurableEquiv.mk (MulAction.toPerm g) (hμ' g).measurable (hμ' g⁻¹).measurable).measurableEmbedding
  have hΨl : ∀ g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ := fun g =>
    lintegral_congr (fun z => by rw [hΨ, UpperTheory.Esk.InverseSeriesLemmas.enorm_smul_nonneg _ (hb.nonneg _)])
  have hΦl : ∀ g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    intro g
    rw [← (hμ' g).lintegral_comp (hΨm g).enorm]
    exact lintegral_congr (fun y => by rw [hΦ, hΨ, inv_smul_smul])
  have hfin : ∫⁻ z, ‖f z‖ₑ ∂μ < ⊤ := hfi.2
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∑' g : G, ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          tsum_congr hΨl
      _ = ∫⁻ z, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          (lintegral_tsum (fun g =>
            ((hb.meas.comp (hμ' g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable)).symm
      _ = ∫⁻ z, ‖f z‖ₑ ∂μ := lintegral_congr (fun z => by
          rw [ENNReal.tsum_mul_right, UpperTheory.Esk.InverseSeriesLemmas.tsum_ofReal_inv b hb z, one_mul])
  have hsumΦ' : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := (tsum_congr hΦl).trans hsumΨ
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ⊤ := by rw [hsumΦ']; exact hfin.ne
  have hΦi : ∀ g, ∫ y, Φ g y ∂μ = ∫ z, Ψ g z ∂μ := by
    intro g
    rw [← (hμ' g).integral_comp (emb g) (Ψ g)]
    congr 1
    funext y
    rw [hΦ, hΨ, inv_smul_smul]
  have hΨt : ∫ z, ∑' g, Ψ g z ∂μ = ∑' g, ∫ z, Ψ g z ∂μ :=
    integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (by rw [hsumΨ]; exact hfin.ne)
  have hΨp : ∀ z, ∑' g, Ψ g z = f z := by
    intro z
    simp only [hΨ]
    rw [((UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb z).smul_const (f z)).tsum_eq, one_smul]
  have hΦt : ∫ y, ∑' g, Φ g y ∂μ = ∑' g, ∫ y, Φ g y ∂μ :=
    integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ
  have hΦp : ∀ y, ∑' g, Φ g y = b y • ∑' g : G, f (g • y) := by
    intro y
    simp only [hΦ]
    exact tsum_const_smul'' (b y)
  have hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y :=
    funext (fun y => (hΦp y).symm)
  have heq : ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ := by
    rw [hfun, hΦt, tsum_congr hΦi, ← hΨt]
    congr 1
    funext z
    exact hΨp z
  have hint : Integrable (fun y => ∑' g, Φ g y) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun g => (hΦm g).aestronglyMeasurable), ?_⟩
    have hle : ∫⁻ y, ‖∑' g, Φ g y‖ₑ ∂μ ≤ ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ :=
      lintegral_mono (fun y => enorm_tsum_le_tsum_enorm)
    have hsum_eq : ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ = ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ :=
      lintegral_tsum (fun g => (hΦm g).enorm.aemeasurable)
    exact lt_of_le_of_lt (hle.trans hsum_eq.le) (lt_top_iff_ne_top.mpr hsumΦ)
  exact ⟨by rw [hfun]; exact hint, heq⟩
