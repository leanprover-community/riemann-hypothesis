module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsParamImageNull
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem ParamImageNull.segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} (c : K → ℂ) (v : (Σ k, ι k) → ℂ) :
    segre (torusSmul c v) = (∏ k, c k) • segre v := by
  funext x
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem ParamImageNull.differentiableAt_segre_comp {K : Type} [Fintype K] {ι : K → Type} {d : ℕ}
    {f : (Fin d → ℂ) → (Σ k, ι k) → ℂ} {w : Fin d → ℂ} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun u => segre (f u)) w := by
  refine differentiableAt_pi.2 fun x => ?_
  simp only [segre]
  have hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w := fun k => differentiableAt_pi.1 hf ⟨k, x k⟩
  fun_prop

theorem ParamImageNull.proof : ParamImageNull.Statement := by
  intro K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _
  classical
  set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG
  set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF
  have hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆
      ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0}) := by
    rintro y ⟨z, hzP, hzN, hzy⟩
    obtain ⟨i, w, hw, c, hc, rfl⟩ := hN z ⟨hzN, hzP⟩
    rw [ParamImageNull.segre_torusSmul, map_smul] at hzy
    have h0 := congrFun hzy 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hG0 : G i w 0 ≠ 0 := by
      intro h
      rw [hG] at h
      simp only at h
      rw [h, mul_zero] at h0
      exact zero_ne_one h0
    refine Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩
    funext l
    have hl := congrFun hzy l.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl
    simp only [hF]
    rw [div_eq_iff hG0, ← hl]
    have h0' : (∏ k, c k) * G i w 0 = 1 := h0
    calc G i w l.succ = G i w l.succ * ((∏ k, c k) * G i w 0) := by rw [h0', mul_one]
      _ = (∏ k, c k) * Ψ (segre (γ i w)) l.succ * G i w 0 := by simp only [hG]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null Set.inter_subset_left (hA i))
  intro w ⟨hwA, hw0⟩
  have hγw : DifferentiableAt ℂ (γ i) w := (hγ i w (hAV i hwA)).differentiableAt
  have hGw : DifferentiableAt ℂ (G i) w :=
    (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)
  have hFw : DifferentiableAt ℂ (F i) w := by
    refine differentiableAt_pi.2 fun l => ?_
    show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w
    simp only [div_eq_mul_inv]
    exact (differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)
  exact (hFw.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
