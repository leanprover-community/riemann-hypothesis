module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.LocRep


open MeasureTheory Filter Topology in
open scoped ContDiff in
theorem _root_.GlobalTheory.LocRep.exists_eval_closure (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ι : K → G → ℂ)
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x)
    (A : K →L[ℂ] K) (E : Submodule ℂ K)
    (hE : ∀ v ∈ E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A v) =ᵐ[μ] φ)
    (hB : ∀ B, IsCompact B → ∃ C : ℝ, ∀ v ∈ E, ∀ φ : G → ℂ, Continuous φ → ι (A v) =ᵐ[μ] φ →
      ∀ x ∈ B, ‖φ x‖ ≤ C * ‖v‖) :
    ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v ∈ closure (E : Set K),
      (Continuous fun x => Λ x v) ∧ ι (A v) =ᵐ[μ] fun x => Λ x v := by
  have hE' : ∀ w : E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A w) =ᵐ[μ] φ := fun w => hE w w.2
  choose ψ hψc hψae using hE'
  have hadd : ∀ w w' : E, ψ (w + w') = fun x => ψ w x + ψ w' x := fun w w' =>
    (Continuous.ae_eq_iff_eq μ (hψc _) ((hψc w).add (hψc w'))).1 (by
      filter_upwards [hψae (w + w'), _root_.GlobalTheory.LocRep.rep_add hlin (A w) (A w'), hψae w, hψae w']
        with x h0 h1 h2 h3
      show ψ (w + w') x = ψ w x + ψ w' x
      rw [← h0, ← h2, ← h3, ← h1]
      simp)
  have hsmul : ∀ (a : ℂ) (w : E), ψ (a • w) = fun x => a * ψ w x := fun a w =>
    (Continuous.ae_eq_iff_eq μ (hψc _) (continuous_const.mul (hψc w))).1 (by
      filter_upwards [hψae (a • w), _root_.GlobalTheory.LocRep.rep_smul hlin a (A w), hψae w] with x h0 h1 h2
      show ψ (a • w) x = a * ψ w x
      rw [← h0, ← h2, ← h1]
      simp)
  let L : G → E →L[ℂ] ℂ := fun x => LinearMap.mkContinuousOfExistsBound
    { toFun := fun w => ψ w x
      map_add' := fun w w' => congrFun (hadd w w') x
      map_smul' := fun a w => by simpa using congrFun (hsmul a w) x } (by
      obtain ⟨c, hc⟩ := hB {x} isCompact_singleton
      exact ⟨c, fun w => hc w w.2 _ (hψc w) (hψae w) x rfl⟩)
  have hext : ∀ x, ∃ g : K →L[ℂ] ℂ, (∀ w : E, g w = L x w) ∧ ‖g‖ = ‖L x‖ :=
    fun x => exists_extension_norm_eq E (L x)
  choose Λ hΛext hΛnorm using hext
  have hbound : ∀ B, IsCompact B → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ B, ‖Λ x‖ ≤ c := by
    intro B hBc
    obtain ⟨c, hc⟩ := hB B hBc
    refine ⟨max c 0, le_max_right _ _, fun x hx => ?_⟩
    rw [hΛnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun w => ?_
    exact (hc w w.2 _ (hψc w) (hψae w) x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨Λ, fun v hv => ?_⟩
  obtain ⟨u, hun, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have hcont : ∀ n, Continuous fun x => Λ x (u n) := fun n => by
    have h : (fun x => Λ x (u n)) = ψ ⟨u n, hun n⟩ := funext fun x => hΛext x ⟨u n, hun n⟩
    rw [h]
    exact hψc _
  have hunif : ∀ B, IsCompact B →
      TendstoUniformlyOn (fun n x => Λ x (u n)) (fun x => Λ x v) atTop B := by
    intro B hBc
    obtain ⟨c, hc0, hc⟩ := hbound B hBc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hu' := (Metric.tendsto_nhds.1 hu) (ε / (c + 1)) (by positivity)
    filter_upwards [hu'] with n hn x hx
    rw [dist_eq_norm, ← map_sub]
    calc ‖Λ x (v - u n)‖ ≤ ‖Λ x‖ * ‖v - u n‖ := (Λ x).le_opNorm _
      _ ≤ c * (ε / (c + 1)) := by
          refine mul_le_mul (hc x hx) ?_ (norm_nonneg _) hc0
          rw [← dist_eq_norm, dist_comm]
          exact hn.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hcontv : Continuous fun x => Λ x v :=
    (tendstoLocallyUniformly_iff_forall_isCompact.2 hunif).continuous
      (Eventually.of_forall hcont).frequently
  have hint : ∀ C, IsCompact C → ∫ x in C, ι (A v) x ∂μ = ∫ x in C, Λ x v ∂μ := by
    intro C hC
    obtain ⟨Pr, hPr⟩ := _root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC
    obtain ⟨c, hc0, hc⟩ := hbound C hC
    have h1 : Tendsto (fun n => Pr (A (u n))) atTop (𝓝 (Pr (A v))) :=
      ((Pr.continuous.comp A.continuous).tendsto v).comp hu
    have h2 : ∀ n, Pr (A (u n)) = ∫ x in C, Λ x (u n) ∂μ := fun n => by
      rw [hPr]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hψae ⟨u n, hun n⟩] with x hx
      rw [hx]
      exact (hΛext x ⟨u n, hun n⟩).symm
    have h3 : Tendsto (fun n => ∫ x in C, Λ x (u n) ∂μ) atTop (𝓝 (∫ x in C, Λ x v ∂μ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (g := fun n => c * ‖u n - v‖ * (μ C).toReal)
        (fun n => ?_) ?_
      · rw [← integral_sub ((hcont n).locallyIntegrable.integrableOn_isCompact hC)
          (hcontv.locallyIntegrable.integrableOn_isCompact hC)]
        refine norm_setIntegral_le_of_norm_le_const hC.measure_lt_top fun x hx => ?_
        rw [← map_sub]
        exact ((Λ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hc x hx) (norm_nonneg _))
      · have h4 : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 hu
        simpa using (h4.const_mul c).mul_const (μ C).toReal
    rw [← hPr]
    exact tendsto_nhds_unique (h1.congr h2) h3
  exact ⟨hcontv, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hcontv.locallyIntegrable hint⟩

end GlobalTheory.LocRep
