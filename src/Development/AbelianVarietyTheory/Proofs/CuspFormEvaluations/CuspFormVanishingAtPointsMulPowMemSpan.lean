import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSumMul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtCompCpt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurablePhi
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SmoothWtContDiffOn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FreeDivMetric

open GlobalTheory.Up GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

open Classical in

noncomputable def Wfree (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ)

theorem Wfree_of_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X G x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wfree
  rw [if_pos hx]

theorem Wfree_of_notMem {x : Frame X.Ψ r} (hx : x ∉ X.dom) : Wfree Xa Fl G n x = 0 := by
  unfold Wfree
  rw [if_neg hx]

private lemma sum_norm_sq_pos_of_exists_ne_zero {N : ℕ} {a : Fin N → ℂ} (h : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩

theorem Wfree_eq_exp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-(phla X G x +
      (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)))) := by
  have hA : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero (Xa.w_nz x hx)
  have hB : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero hs
  have key : Real.exp (-(phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))) =
      Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hA.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hB]

theorem Wfree_eq_pnorm {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have hc : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have key : Real.exp (-phla X G x) = Real.exp (-phla X (G + n • Xa.L) x) *
      Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) * Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, hw, hs, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul hc.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_rpow_of_pos hc, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hc.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

private lemma isBddSec_of_mem_SSgt {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ} (h : P ∈ X.SSgt la c) :
    X.IsBddSec la P := h.1.1

theorem measurable_Wfree : Measurable (Wfree Xa Fl G n) := by
  have hw : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (isBddSec_of_mem_SSgt (Xa.w_van k)).1.1.continuousOn
  have hs : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (isBddSec_of_mem_SSgt (Fl.s_van k)).1.1.continuousOn
  have ha : ContinuousOn (fun x => Real.exp (-phla X G x)) X.dom :=
    Real.continuous_exp.comp_continuousOn (IW.phla_contOn X G).neg
  have hA : ContinuousOn (fun x => ∑ k, ‖Xa.w k x‖ ^ 2) X.dom :=
    continuousOn_finset_sum _ fun k _ => ((hw k).norm).pow 2
  have hB : ContinuousOn (fun x => ∑ k, ‖Fl.s k x‖ ^ 2) X.dom :=
    continuousOn_finset_sum _ fun k _ => ((hs k).norm).pow 2
  have e : Wfree Xa Fl G n = fun x =>
      X.dom.indicator (fun x => ENNReal.ofReal (Real.exp (-phla X G x))) x *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) x ^ (-(1 / 2 : ℝ)) *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) x ^ (-((n : ℝ) - 1 / 2)) := by
    funext x
    by_cases hx : x ∈ X.dom
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact Wfree_of_mem Xa Fl G n hx
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul]
      exact Wfree_of_notMem Xa Fl G n hx
  rw [e]
  exact ((GlobalTheory.Up.DivMetricPf.measurable_cut ha).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hA).pow_const _)).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hB).pow_const _)

theorem Wfree_rmul (hN : NfacRmulStatement (E := E)) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    Wfree Xa Fl G n (rmul x b) =
      Wfree Xa Fl G n x / ENNReal.ofReal (‖bchar (G + n • Xa.L) b‖ ^ 2) := by
  have hxb : rmul x b ∈ X.dom := OntoS.dom_rmul X hx hb
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hx hb
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hx hb
  have h1 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hxb (G + n • Xa.L)
  have h2 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hx (G + n • Xa.L)
  have h3 := hN r X (G + n • Xa.L) x hx b hb
  have hn0 : X.nfac (G + n • Xa.L) (rmul x b) ≠ 0 := by
    intro h
    have hp := Real.exp_pos (-phla X (G + n • Xa.L) (rmul x b))
    rw [h1, h] at hp
    norm_num at hp
  have hc : ‖bchar (G + n • Xa.L) b‖ ≠ 0 := by
    intro h
    rw [h, inv_zero, zero_mul] at h3
    exact hn0 h3
  have hc2 : 0 < ‖bchar (G + n • Xa.L) b‖ ^ 2 := by positivity
  have hph : Real.exp (-phla X (G + n • Xa.L) (rmul x b)) =
      Real.exp (-phla X (G + n • Xa.L) x) / ‖bchar (G + n • Xa.L) b‖ ^ 2 := by
    rw [h1, h2, h3]
    field_simp
  rw [Wfree_eq_pnorm Xa Fl G n hxb, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs]
  rw [hph, ENNReal.ofReal_div_of_pos hc2]
  simp only [div_eq_mul_inv]
  ring

theorem Wfree_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wfree Xa Fl G n (lact γ x) = Wfree Xa Fl G n x := by
  have hxg : lact γ x ∈ X.dom := OntoS.dom_lact X hγ hx
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hγ hx
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hγ hx
  have hph : Real.exp (-phla X (G + n • Xa.L) (lact γ x)) = Real.exp (-phla X (G + n • Xa.L) x) := by
    rw [GlobalTheory.Up.DivMetricPf.exp_neg_phla hxg, GlobalTheory.Up.DivMetricPf.exp_neg_phla hx, hN r X _ γ hγ x hx]
  rw [Wfree_eq_pnorm Xa Fl G n hxg, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs, hph]

theorem Wfree_lower (hn : 1 ≤ n) : WLower X (G + n • Xa.L) (Wfree Xa Fl G n) := by
  obtain ⟨C, hC, hCw⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Xa.w_van k)
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Fl.s_van k)
  have ht : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)),
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hD _), fun x hx => ?_⟩
  have e1 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hC (hCw x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e2 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hD (hDs x hx) ht
  rw [Wfree_eq_pnorm Xa Fl G n hx]
  calc ENNReal.ofReal (C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)) * Real.exp (-phla X (G + n • Xa.L) x))
      = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) * ENNReal.ofReal (C ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (D ^ (-((n : ℝ) - 1 / 2))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hC.le _))]
        congr 1
        ring
    _ ≤ _ := by gcongr

theorem freeDivMetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → IsMetricW X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ WLower X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) x = ENNReal.ofReal (Real.exp (-(fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) x)) := by
  intro E _ _ _ r X Xa Fl G n hn
  have hR := GlobalTheory.NormFactor.nfacRmul_holds (E := E)
  have hL := GlobalTheory.NormFactor.nfacLact_holds (E := E)
  exact ⟨⟨measurable_Wfree Xa Fl G n, fun x hx b hb => Wfree_rmul Xa Fl G n hR hx hb,
    fun γ hγ x hx => Wfree_lact Xa Fl G n hL hγ hx⟩, Wfree_lower Xa Fl G n hn,
    fun x hx hs => Wfree_eq_exp Xa Fl G n hx hs⟩

end GlobalTheory.FreeDivMetric
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → IsMetricW X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ WLower X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) x = ENNReal.ofReal (Real.exp (-(fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) x)) := by
  atlas_forward_decl GlobalTheory.FreeDivMetric.freeDivMetric
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

open GlobalTheory.Up.DivLeviPf in

theorem divLevi_freeWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → ∀ x0, IsOrth X x0 → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) ∧ ∀ k0 : Fin (nd X), ContDiffOn ℝ ∞ (fun z => (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0} ∧ ∀ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 → ∀ ξ : Fin (nd X) → ℂ, leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ ≤ (leviV (nd X) (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  intro E _ _ _ r X Xa Fl G n hn x0 ho
  have hsS : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hwS : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hs : ∀ z ∈ OmF X x0, ∀ k, ContDiffAt ℂ ∞ (fun w => Fl.s k (cpt X x0 w)) z :=
    fun z hz k => contDiffAt_comp_cpt (hsS k).1 x0 hz
  have hw : ∀ z ∈ OmF X x0, ∀ k, ContDiffAt ℂ ∞ (fun w => Xa.w k (cpt X x0 w)) z :=
    fun z hz k => contDiffAt_comp_cpt (hwS k).1 x0 hz
  refine ⟨?_, fun k0 => ⟨fun z hz => ?_, fun z hz hz0 ξ => ?_⟩⟩
  · obtain ⟨k, x, hx, hne⟩ := exists_s_ne_zero Fl (IW.orth_mem_dom X x0 ho)
    by_contra h
    push Not at h
    exact hne (bigCellStatement_holds r X x0 ho Xa.L (Fl.s k) ⟨(hsS k).1, (hsS k).2.1⟩ (h k) x hx)
  · have h1 := IW.phla_cpt_cdAt X x0 hz.1 G
    have h2 := logSum_contDiffAt (hw z hz.1) (Xa.w_nz _ hz.1)
    have h3 := logSum_contDiffAt (hs z hz.1) ⟨k0, hz.2⟩
    exact ((h1.add (contDiffAt_const.mul h2)).add (contDiffAt_const.mul h3)).contDiffWithinAt
  · have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
    have h2 := (logSum_contDiffAt (hw z hz) (Xa.w_nz _ hz)).of_le HE.two_le_inf
    have h3 := (logSum_contDiffAt (hs z hz) ⟨k0, hz0⟩).of_le HE.two_le_inf
    have h4 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
    have l2 := logSum_levi_nonneg (hw z hz) (Xa.w_nz _ hz) ξ
    have l3 := logSum_levi_nonneg (hs z hz) ⟨k0, hz0⟩ ξ
    have e : (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
          ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) -
            Real.log (densF X x0 w) : ℝ) : ℂ)) =
        fun w => (((phla X G (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) +
          ((1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 w)‖ ^ 2) +
            ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k (cpt X x0 w)‖ ^ 2)) : ℝ) : ℂ) := by
      funext w
      congr 1
      ring
    rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h4))
        ((contDiffAt_const.mul h2).add (contDiffAt_const.mul h3)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h4),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) (contDiffAt_const.mul h3),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2,
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    have hn' : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have l3' := mul_nonneg hn' l3
    unfold leviO leviM leviDens
    linarith

end GlobalTheory.Shares
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singularMetricFreeDivisor_smooth_curvature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → ∀ x0, IsOrth X x0 → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) ∧ ∀ k0 : Fin (nd X), ContDiffOn ℝ ∞ (fun z => (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0} ∧ ∀ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 → ∀ ξ : Fin (nd X) → ℂ, leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ ≤ (leviV (nd X) (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  atlas_forward_decl GlobalTheory.Shares.divLevi_freeWeight
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FreeWeightInFF

open Filter GlobalTheory.Up GlobalTheory.Up.DivInFFPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r)

open Classical in

noncomputable def Wfree (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

theorem Wfree_of_mem (n : ℕ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X G x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wfree
  rw [if_pos hx]

theorem Wfree_eq_pnorm (n : ℕ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Xa.w k)
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Fl.s k)
  have he : Real.exp (-phla X (G + n • Xa.L) x) =
      Real.exp (-phla X G x) * Real.exp (-phla X Xa.L x) ^ n := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, neg_add, Real.exp_add, ← Real.exp_nat_mul, mul_neg]
  have hc0 : ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have key : ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ^ n *
      (ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ^ (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (Real.exp (-phla X Xa.L x)) ^ (-((n : ℝ) - 1 / 2))) = 1 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top,
      ← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top]
    convert ENNReal.rpow_zero using 2
    ring
  rw [Wfree_of_mem Xa Fl G n hx, hw, hs, he, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_pow (Real.exp_pos _).le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  generalize ENNReal.ofReal (Real.exp (-phla X Xa.L x)) = c at key ⊢
  generalize ENNReal.ofReal (Real.exp (-phla X G x)) = a
  generalize ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) = A
  generalize ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) = B
  calc a * A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2))
      = a * A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2)) *
        (c ^ n * (c ^ (-(1 / 2 : ℝ)) * c ^ (-((n : ℝ) - 1 / 2)))) := by rw [key, mul_one]
    _ = _ := by ring

noncomputable def phiW (n : ℕ) (h : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (X.dom.indicator (fun x => X.pnorm (G + n • Xa.L) h x ^ 2) x *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) x ^ (-(1 / 2 : ℝ)) *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) x ^ (-((n : ℝ) - 1 / 2)))

theorem phiW_of_mem (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiW Xa Fl G n h x = ENNReal.ofReal (X.pnorm (G + n • Xa.L) h x ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
  simp only [phiW, Set.indicator_of_mem hx]

theorem measurable_phiW (n : ℕ) {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (G + n • Xa.L) h) :
    Measurable (phiW Xa Fl G n h) := by
  have h1 : Measurable (X.dom.indicator fun x => X.pnorm (G + n • Xa.L) h x ^ 2) :=
    GlobalTheory.Up.DivInFFPf.measurable_cut ((GlobalTheory.Up.DivInFFPf.pnorm_contOn hh).pow 2)
  have h2 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) :=
    GlobalTheory.Up.DivInFFPf.measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (GlobalTheory.Up.DivInFFPf.pnorm_contOn (Xa.w_van k).1.1.1).pow 2)
  have h3 : Measurable (X.dom.indicator fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) :=
    GlobalTheory.Up.DivInFFPf.measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (GlobalTheory.Up.DivInFFPf.pnorm_contOn (Fl.s_van k).1.1.1).pow 2)
  exact ((h1.mul (h2.pow_const _)).mul (h3.pow_const _)).ennreal_ofReal

theorem phiW_inv (hN : NfacRmulStatement (E := E)) (hN' : NfacLactStatement (E := E)) (n : ℕ)
    {h : Frame X.Ψ r → ℂ} (hh : X.IsSec (G + n • Xa.L) h) :
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phiW Xa Fl G n h (lact γ (rmul x b)) = phiW Xa Fl G n h x := by
  intro γ hγ x hx b hb
  have hxb : rmul x b ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul (X := X) hx hb
  have hy : lact γ (rmul x b) ∈ X.dom :=
    (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff (X := X) hγ (rmul x b)).2 hxb
  have inv : ∀ {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}, X.IsSec la P →
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x := fun hP =>
    (GlobalTheory.Up.DivMetricPf.pnorm_lact hN' hP hγ hxb).trans (GlobalTheory.Up.DivMetricPf.pnorm_rmul hN hP hx hb)
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) (lact γ (rmul x b)) ^ 2 = ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [inv (Xa.w_van k).1.1.1]
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) (lact γ (rmul x b)) ^ 2 = ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [inv (Fl.s_van k).1.1.1]
  rw [phiW_of_mem Xa Fl G n h hy, phiW_of_mem Xa Fl G n h hx, inv hh, hw, hs]

theorem phiW_eq (n : ℕ) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : ∃ k, Fl.s k x ≠ 0) :
    phiW Xa Fl G n h x = ENNReal.ofReal (‖h x‖ ^ 2) * Wfree Xa Fl G n x := by
  have hw := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz x hx)
  have hs' := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx hs
  rw [phiW_of_mem Xa Fl G n h hx, Wfree_eq_pnorm Xa Fl G n hx,
    GlobalTheory.Up.pnorm_sq_eq_exp hx (G + n • Xa.L) h, ENNReal.ofReal_rpow_of_pos hw,
    ENNReal.ofReal_rpow_of_pos hs', ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul]
  · ring
  all_goals positivity

theorem phiW_le_local {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiW Xa Fl G n h x ≤
      ENNReal.ofReal (X.nfac G x ^ 2 * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (‖h x‖ ^ 2 * (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
  refine le_of_eq ?_
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Xa.w k)
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx Xa.L (Fl.s k)
  have he : Real.exp (-phla X (G + n • Xa.L) x) =
      Real.exp (-phla X G x) * Real.exp (-phla X Xa.L x) ^ n := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, neg_add, Real.exp_add, ← Real.exp_nat_mul, mul_neg]
  have hL := Real.exp_pos (-phla X Xa.L x)
  have hA : 0 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 := by positivity
  have hB : 0 ≤ ∑ k, ‖Fl.s k x‖ ^ 2 := by positivity
  have key : Real.exp (-phla X Xa.L x) ^ n * (Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2))) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL, ← Real.rpow_add hL]
    convert Real.rpow_zero _ using 2
    ring
  have hp : 0 ≤ Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by positivity
  rw [phiW_of_mem Xa Fl G n h hx, GlobalTheory.Up.pnorm_sq_eq_exp hx (G + n • Xa.L) h, hw, hs, he,
    Real.mul_rpow hL.le hA, Real.mul_rpow hL.le hB, ← GlobalTheory.Up.DivMetricPf.exp_neg_phla hx G,
    ← ENNReal.ofReal_mul hp]
  congr 1
  generalize Real.exp (-phla X Xa.L x) = c at key ⊢
  linear_combination (Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ‖h x‖ ^ 2 *
    (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) * key

theorem localW_int {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) < ⊤) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', phiW Xa Fl G n h (cpt X y z) < ⊤ := by
  have hO : IsOpen (OmF X y) := ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X y
  have h0 : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X y]
    exact hy
  have hwc : ContinuousOn (fun z => ∑ k, ‖Xa.w k (cpt X y z)‖ ^ 2) (OmF X y) :=
    continuousOn_finsetSum _ fun k _ =>
      ((((Xa.w_van k).1.1.1.1.continuousOn).comp
        (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cpt_cont X y).continuousOn fun z hz => hz).norm).pow 2
  have hpos0 : 0 < ∑ k, ‖Xa.w k (cpt X y 0)‖ ^ 2 := GlobalTheory.Up.sum_normSq_w_pos Xa (x := cpt X y 0) h0
  have hFc : ContinuousAt (fun z => X.nfac G (cpt X y z) ^ 2 *
      (∑ k, ‖Xa.w k (cpt X y z)‖ ^ 2) ^ (-(1 / 2 : ℝ))) 0 :=
    (((ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont (X := X) (x0 := y) G).continuousAt
      (hO.mem_nhds h0)).pow 2).mul ((hwc.continuousAt (hO.mem_nhds h0)).rpow_const (Or.inl hpos0.ne'))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hFc.eventually (gt_mem_nhds (lt_add_one _))).and (hO.mem_nhds h0))
  refine ⟨min ρ ε, lt_min hρ hε, ?_⟩
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min ρ ε), phiW Xa Fl G n h (cpt X y z)
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min ρ ε),
          ENNReal.ofReal (X.nfac G (cpt X y 0) ^ 2 * (∑ k, ‖Xa.w k (cpt X y 0)‖ ^ 2) ^ (-(1 / 2 : ℝ)) + 1) *
          ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by
        refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun z hz => ?_
        have hz' := hball z (Metric.ball_subset_ball (min_le_right ρ ε) hz)
        exact (phiW_le_local Xa Fl G hn h (x := cpt X y z) hz'.2).trans
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hz'.1.le) le_rfl)
    _ = ENNReal.ofReal (X.nfac G (cpt X y 0) ^ 2 * (∑ k, ‖Xa.w k (cpt X y 0)‖ ^ 2) ^ (-(1 / 2 : ℝ)) + 1) *
          ∫⁻ z in Metric.ball (0 : V (nd X)) (min ρ ε),
            ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 * (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((lintegral_mono_set (Metric.ball_subset_ball (min_le_left ρ ε))).trans_lt hint)

theorem inFF_sub {T : ℕ} (hT1 : 1 ≤ T) (hnT : nd X ≤ T) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) {f g : Frame X.Ψ r → ℂ}
    (hf : X.IsSec (G + T • Xa.L) f) (hg : X.IsSec (G + T • Xa.L) g)
    (hfi : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) ∂muF X x0 < ⊤)
    {C : ℝ} (hC : ∀ x ∈ X.dom,
      X.pnorm (G + T • Xa.L) g x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ T)
    (hvan : VanS X Fl.xs Fl.s (T - nd X) (fun x => f x - g x)) :
    InFF X x0 (Wfree Xa Fl G T) FF (fun x => f x - g x) := by
  have hM := GlobalTheory.FrameMeasureClosed.measInv_holds (E := E)
  have hN := GlobalTheory.NormFactor.nfacRmul_holds (E := E)
  have hN' := GlobalTheory.NormFactor.nfacLact_holds (E := E)
  have hfin := GlobalTheory.DriftCovolume.finMu_unconditional r X
  have hd : X.IsSec (G + T • Xa.L) (fun x => f x - g x) := by
    refine ⟨hf.1.sub hg.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
    · simp only [hf.2.1 x hx b hb, hg.2.1 x hx b hb]; ring
    · simp only [hf.2.2 γ hγ x hx, hg.2.2 γ hγ x hx]; ring
  have hφm := measurable_phiW Xa Fl G T hd
  have hφi := phiW_inv Xa Fl G hN hN' T hd
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      phiW Xa Fl G T (fun x => f x - g x) (rmul x b) = phiW Xa Fl G T (fun x => f x - g x) x := by
    intro x hx b hb
    have := hφi 1 X.Γ.one_mem x hx b hb
    rwa [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_one] at this

  have hloc : ∀ j, ∃ x1 : Frame X.Ψ r, ∃ ρ1 : ℝ, IsOrth X x1 ∧ 0 < ρ1 ∧
      Metric.ball (0 : V (nd X)) ρ1 ⊆ OmF X x1 ∧ (∃ b ∈ Bor X.Ψ r, Fl.xs j = rmul x1 b) ∧
      ∫⁻ y in Metric.ball (0 : V (nd X)) ρ1, phiW Xa Fl G T (fun x => f x - g x) (cpt X x1 y) ∂muF X x1 < ⊤ := by
    intro j
    obtain ⟨ρ, hρ, hint⟩ := hvan j
    have hexp : (-(((T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2)) = -((T : ℝ) - 1 / 2) := by
      rw [Nat.cast_sub hnT]; ring
    rw [hexp] at hint
    obtain ⟨ρ', hρ', hint'⟩ := localW_int Xa Fl G hT1 (fun x => f x - g x) (Fl.xs_mem j) hρ hint
    obtain ⟨x1, ho1, b, hb, hxs⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X (Fl.xs j) (Fl.xs_mem j)
    rw [hxs] at hint'
    obtain ⟨ρ1, hρ1, hsub, hfin1⟩ :=
      GlobalTheory.ChartChange.chart_change r X x1 b ho1 hb _ hφm hφB ρ' hρ' hint'
    exact ⟨x1, ρ1, ho1, hρ1, hsub, ⟨b, hb, hxs⟩, hfin1⟩
  choose x1 ρ1 ho1 hρ1 hsub hxb hfin1 using hloc
  obtain ⟨U, hU⟩ : ∃ U : Set (Frame X.Ψ r), U = ⋃ j, {x | ∃ y ∈ Metric.ball (0 : V (nd X)) (ρ1 j),
      ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X (x1 j) y) b)} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU]
    exact isOpen_iUnion fun j =>
      GlobalTheory.SatOpen.isOpen_saturation r X (x1 j) (ho1 j) _ Metric.isOpen_ball (hsub j)
  have hxsU : ∀ j, Fl.xs j ∈ U := by
    intro j
    obtain ⟨b, hb, hxs⟩ := hxb j
    rw [hU, Set.mem_iUnion]
    refine ⟨j, 0, Metric.mem_ball_self (hρ1 j), 1, X.Γ.one_mem, b, hb, ?_⟩
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_one, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
    exact hxs
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    rw [hU, Set.mem_iUnion] at hx ⊢
    obtain ⟨j, y, hy, γ0, hγ0, b0, hb0, rfl⟩ := hx
    refine ⟨j, y, hy, γ * γ0, X.Γ.mul_mem hγ hγ0, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.bmul X b0 b,
      ReciprocityTheory.ChartRestriction.G.AR.Up.IW.bmul_mem (X := X) hb0 hb, ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_rmul, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_lact,
      ReciprocityTheory.ChartRestriction.G.AR.Up.IW.rmul_rmul]
  obtain ⟨K, hK⟩ := Fl.family_le_coords U hUo hxsU hsat
  have hAo : IsOpen (cpt X x0 ⁻¹' U) := hUo.preimage (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cpt_cont X x0)

  have hae : (fun z => ENNReal.ofReal (‖f (cpt X x0 z) - g (cpt X x0 z)‖ ^ 2) * Wfree Xa Fl G T (cpt X x0 z))
      =ᵐ[(muF X x0).restrict FF] fun z => phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) := by
    filter_upwards [ae_restrict_of_ae (GlobalTheory.Up.DivInFFPf.ae_exists_ne Xa Fl ho), ae_restrict_mem hF.1]
      with z hz hzF
    exact (phiW_eq Xa Fl G T (fun x => f x - g x) (x := cpt X x0 z) (hF.2.1 hzF) (hz (hF.2.1 hzF))).symm

  have h1 : ∫⁻ z in FF ∩ cpt X x0 ⁻¹' U, phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 < ⊤ := by
    have hsubU : FF ∩ cpt X x0 ⁻¹' U ⊆ ⋃ j, FF ∩ {z | ∃ y ∈ Metric.ball (0 : V (nd X)) (ρ1 j),
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X (x1 j) y) b)} := by
      intro z hz
      have hzU := hz.2
      rw [Set.mem_preimage, hU, Set.mem_iUnion] at hzU
      obtain ⟨j, hj⟩ := hzU
      exact Set.mem_iUnion.2 ⟨j, hz.1, hj⟩
    calc _ ≤ _ := lintegral_mono_set hsubU
      _ ≤ ∑' j, ∫⁻ z in FF ∩ {z | ∃ y ∈ Metric.ball (0 : V (nd X)) (ρ1 j),
          ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X (x1 j) y) b)},
            phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 := lintegral_iUnion_le _ _
      _ ≤ ∑' j, ∫⁻ y in Metric.ball (0 : V (nd X)) (ρ1 j),
            phiW Xa Fl G T (fun x => f x - g x) (cpt X (x1 j) y) ∂muF X (x1 j) :=
        ENNReal.tsum_le_tsum fun j => GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 (x1 j) ho (ho1 j)
          FF hF _ hφm hφi _ Metric.isOpen_ball.measurableSet (hsub j)
      _ < ⊤ := by
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.2 fun j _ => hfin1 j

  have hc0 : (0 : ℝ) ≤ 2 * |K| ^ ((T : ℝ) - 1 / 2) := by positivity
  have hpt : ∀ z ∈ FF \ cpt X x0 ⁻¹' U, phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ≤
      ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
        ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) +
      ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C) := by
    intro z hz
    have hx : cpt X x0 z ∈ X.dom := hF.2.1 hz.1
    have hxU : cpt X x0 z ∉ U := hz.2
    have hw0 := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz _ hx)
    have hs0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 := by positivity
    have key := GlobalTheory.Up.DivInFFPf.real_bound (a := f (cpt X x0 z)) (b := g (cpt X x0 z)) hT1
      (Real.exp_pos (-phla X (G + T • Xa.L) (cpt X x0 z))).le
      (GlobalTheory.Up.pnorm_sq_eq_exp hx _ f) (GlobalTheory.Up.pnorm_sq_eq_exp hx _ g) hw0 hs0 (hK _ hx hxU) (hC _ hx)
    rw [phiW_of_mem Xa Fl G T _ hx, GlobalTheory.Up.pnorm_sq_eq_exp hx (G + T • Xa.L) (fun x => f x - g x),
      ← ENNReal.ofReal_mul hc0]
    exact (ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le
  have h2 : ∫⁻ z in FF \ cpt X x0 ⁻¹' U, phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 < ⊤ := by
    calc _ ≤ ∫⁻ z in FF \ cpt X x0 ⁻¹' U, (ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
          ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) +
          ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C)) ∂muF X x0 :=
        setLIntegral_mono' (hF.1.diff hAo.measurableSet) hpt
      _ ≤ ∫⁻ z in FF, (ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
          ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) +
          ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C)) ∂muF X x0 :=
        lintegral_mono_set fun z hz => hz.1
      _ = ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2)) *
          ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (G + T • Xa.L) f (cpt X x0 z) ^ 2 *
            (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(T : ℝ))) ∂muF X x0 +
          ENNReal.ofReal (2 * |K| ^ ((T : ℝ) - 1 / 2) * C) * muF X x0 FF := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi,
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top (GlobalTheory.Up.DivInFFPf.muF_lt_top hM hfin ho hF)⟩
  show ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z) - g (cpt X x0 z)‖ ^ 2) * Wfree Xa Fl G T (cpt X x0 z)
    ∂muF X x0 < ⊤
  rw [lintegral_congr_ae hae]
  calc _ = ∫⁻ z in FF ∩ cpt X x0 ⁻¹' U ∪ FF \ cpt X x0 ⁻¹' U,
        phiW Xa Fl G T (fun x => f x - g x) (cpt X x0 z) ∂muF X x0 := by rw [Set.inter_union_sdiff]
    _ ≤ _ := lintegral_union_le _ _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem inFF_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f : Frame X.Ψ r → ℂ, X.IsSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → InFF X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) FF f := by
  intro E _ _ _ r X Xa Fl G x0 ho FF hF f hf hbd hzero
  obtain ⟨C, hC⟩ := hbd
  have hM := GlobalTheory.FrameMeasureClosed.measInv_holds (E := E)
  have hfin := GlobalTheory.DriftCovolume.finMu_unconditional r X
  have hfi : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (G + (nd X + 1) • Xa.L) f (cpt X x0 z) ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + 1 : ℕ) : ℝ))) ∂muF X x0 < ⊤ := by
    calc _ ≤ ∫⁻ _ in FF, ENNReal.ofReal C ∂muF X x0 := by
          refine setLIntegral_mono' hF.1 fun z hz => ENNReal.ofReal_le_ofReal ?_
          have hx : cpt X x0 z ∈ X.dom := hF.2.1 hz
          have hS := GlobalTheory.Up.DivInFFPf.sum_pnorm_pos (la := Xa.L) hx (Xa.w_nz _ hx)
          calc _ ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (nd X + 1) *
                (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-((nd X + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right (hC _ hx) (Real.rpow_nonneg hS.le _)
            _ = C := by
              rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hS]
              simp
      _ = ENNReal.ofReal C * muF X x0 FF := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (GlobalTheory.Up.DivInFFPf.muF_lt_top hM hfin ho hF)
  have hzsec : X.IsSec (G + (nd X + 1) • Xa.L) (fun _ => (0 : ℂ)) :=
    ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩
  have hg0 : ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) (fun _ => (0 : ℂ)) x ^ 2 ≤
      0 * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1) := fun x _ => by
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
  have hvan : VanS X Fl.xs Fl.s (nd X + 1 - nd X) (fun x => f x - (fun _ => (0 : ℂ)) x) := by
    rw [show nd X + 1 - nd X = 1 by omega]
    refine GlobalTheory.vanS_of_isBigO r X Xa Fl 1 _ (hf.1.continuousOn.sub continuousOn_const) fun j => ?_
    have hyd : cpt X (Fl.xs j) 0 ∈ X.dom := by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
      exact Fl.xs_mem j
    have hd : DifferentiableAt ℂ (fun z => f (cpt X (Fl.xs j) z)) 0 :=
      (hf.1.differentiableAt ((ReciprocityTheory.ChartRestriction.G.AR.Up.IW.isOpen_dom X).mem_nhds hyd)).comp 0
        ((ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_diff X (Fl.xs j)) 0)
    have h0 : f (cpt X (Fl.xs j) 0) = 0 := by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
      exact hzero j
    have hb := hd.isBigO_sub.norm_right
    simp only [h0, sub_zero] at hb
    simpa only [sub_zero, pow_one] using hb
  have key := inFF_sub Xa Fl G (T := nd X + 1) (Nat.le_add_left 1 (nd X)) (Nat.le_succ (nd X)) ho hF
    hf hzsec hfi (C := 0) hg0 hvan
  simp only [sub_zero] at key
  exact key

end GlobalTheory.FreeWeightInFF
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_singular_metric_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f : Frame X.Ψ r → ℂ, X.IsSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → InFF X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) FF f := by
  atlas_forward_decl GlobalTheory.FreeWeightInFF.inFF_order_one
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares.DivOne

open GlobalTheory.Up GlobalTheory.Up.DivUpPf

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def smoothWtG (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ :=
  phla X G (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) + ((-bb) * rhF X x0 z +
    (1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2)))

theorem smoothWtG_contDiffOn (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) :
    ContDiffOn ℝ ∞ (smoothWtG Xa G x0 bb) (OmF X x0) := fun _ hz =>
  ((IW.phla_cpt_cdAt X x0 hz G).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add
    ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add
      (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt

theorem smoothWtG_levi (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ)
    (hm : bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) :
    0 ≤ (leviV (nd X) (fun w => ((smoothWtG Xa G x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
  have h2 := (OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf
  have h3 := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  have h4 := (logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf
  have h5 := logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ
  unfold smoothWtG
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2)
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (contDiffAt_const.mul h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hm
  linarith

theorem inAt_iffG (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb t : ℝ)
    (k0 : Fin (nd X)) (hnull : volume {y | y ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 y) = 0} = 0)
    (F : V (nd X) → ℂ) :
    InAt X x0 (fun x => open Classical in if x ∈ X.dom then
      ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-t) else 0) bb F ↔
      ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-t) *
        Real.exp (-smoothWtG Xa G x0 bb z)) < ⊤ := by
  have hU := OntoB.isOpen_OmF X x0
  have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
  unfold InAt muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))
  have hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    simpa using hz
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'
  have hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := ⟨k0, hz' hz⟩
  have hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := sum_normSq_pos hs
  have hdom : cpt X x0 z ∈ X.dom := hz
  have hw := sum_normSq_w_pos Xa hdom
  have hdp := OntoB.densF_pos hz
  have hka : 0 < kaF X x0 bb z := Real.exp_pos _
  simp only [Pi.mul_apply]
  rw [if_pos hdom, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hsp,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw.le _)),
    Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hsp, ← Real.exp_add, ← Real.exp_add,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hdp.le]
  congr 1
  rw [kaF, div_eq_mul_inv, ← Real.exp_neg]
  conv_lhs => rw [← Real.exp_log hdp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  unfold smoothWtG
  ring

end

theorem divOne_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  intro E _ _ _ r X Xa Fl G x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI
  have hU := OntoB.isOpen_OmF X x0
  have hc := OmFConnStatement_holds r X x0 ho
  have hgn := HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds)
  have hnull := HE.zeros_null hU (s_diffOn Fl x0 k0) hgn
  obtain ⟨S, hS, -⟩ := exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)
  have hcast : ((nd X + 1 : ℕ) : ℝ) - 1 / 2 = ((nd X : ℝ) - 1 / 2) + 1 := by
    push_cast; ring
  rw [inAt_iffG Xa Fl G x0 bb _ k0 hnull, hcast] at hI
  obtain ⟨H, hH, hFH⟩ := SkodaIter.step Xa.n_ge hU (s := fun k z => Fl.s k (cpt X x0 z)) k0
    (s_diffOn Fl x0) hgn ⟨S, hS⟩ (smoothWtG_contDiffOn Xa G x0 bb)
    (fun z hz ξ => smoothWtG_levi Xa G x0 bb hz ξ (hm z hz ξ)) (t := (nd X : ℝ) - 1 / 2)
    (by linarith) hF hI
  exact ⟨H, fun k => ⟨(hH k).1, (inAt_iffG Xa Fl G x0 bb _ k0 hnull _).2 (hH k).2⟩, hFH⟩

end GlobalTheory.Shares.DivOne
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_division_upstairs_free_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  atlas_forward_decl GlobalTheory.Shares.DivOne.divOne_up
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.DivFreeWeight

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra GlobalTheory.Up.DivCorePf

theorem division_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r), (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∀ P, X.IsBddSec (G + (nd X + 1) • Xa.L) P → P ∈ X.SS (G + (nd X + 1) • Xa.L)) → (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (G + (nd X + 1) • Xa.L), ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) → ∀ f, X.IsBddSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec (G + nd X • Xa.L) (h k)) ∧ ∀ x ∈ X.dom, f x = ∑ k, Fl.s k x * h k x := by
  intro E _ _ _ r X Xa Fl G ⟨bb, m, hbb, hbm, hmar⟩ hcusp ⟨K, gs, hgs⟩ f hf hfC hvan
  have h2 := Xa.n_ge
  have hPD : PropDisc X := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  obtain ⟨-, -, -, hPo, hOn⟩ := GlobalTheory.PoincareClosed.unfold_poincare_onto (E := E)
  have hExt := GlobalTheory.FrameMeasureClosed.extF_holds (E := E)
  obtain ⟨x0, ho⟩ : ∃ x0, IsOrth X x0 := by
    choose P hP hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ⟩
  obtain ⟨FF, hFF⟩ := fundSet_holds r X x0 ho hPD
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hbm' : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hIn := GlobalTheory.T.square_integrable_singular_metric_order_one E r X Xa Fl G x0 ho FF hFF f hf.1 hfC hvan
  obtain ⟨hMT, hLT, hET⟩ := GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound E r X Xa Fl G (nd X + 1) (by omega)
  obtain ⟨hMn, hLn, -⟩ := GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound E r X Xa Fl G (nd X) (by omega)
  obtain ⟨⟨k0, z0, hz0, hz0'⟩, hLev⟩ := GlobalTheory.T.singularMetricFreeDivisor_smooth_curvature E r X Xa Fl G (nd X + 1) (by omega) x0 ho
  obtain ⟨F, P, hF, hFI, hP, hPF, hpo⟩ := hOn r X x0 ho hPD _ _
    (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      (((nd X + 1 : ℕ) : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))
    (fun z => Fl.s k0 (cpt X x0 z)) bb m hMT hLT hbb hbm (OntoB.hol_comp X x0 (hs k0).1)
    ⟨z0, hz0, hz0'⟩ (hLev k0).1 (fun z hz hz' => hET _ hz ⟨k0, hz'⟩)
    (fun z hz hz' ξ => (hmar x0 ho z hz ξ).trans ((hLev k0).2 z hz hz' ξ)) hcusp FF hFF
    ⟨K, gs, fun f hf _ => hgs f hf⟩ _ (hcusp _ hf) hIn
  obtain ⟨H, hH, hFH⟩ := GlobalTheory.T.one_division_upstairs_free_weight E r X Xa Fl G x0 ho bb
    (fun z hz ξ => (mul_le_mul_of_nonneg_right hbm'
      (OntoB.levi_rh_nonneg RhGradFStatement_holds ho hz ξ)).trans (hmar x0 ho z hz ξ))
    ⟨k0, z0, hz0, hz0'⟩ F hF hFI
  choose Q hQ hQH using fun k => exists_extension hExt ho hLn hbb0 (hH k).1 (hH k).2
  have hPQ := fun k => hPo r X x0 ho hPD _ _ bb hMn hLn hbb (H k) (Q k) (hH k).1 (hH k).2 (hQ k) (hQH k)
  have hwt : G + (nd X + 1) • Xa.L = G + nd X • Xa.L + Xa.L := by
    rw [succ_nsmul, add_assoc]
  have hsum : ∀ y ∈ X.dom, P y = ∑ k, Fl.s k y * Q k y := by
    intro y hy
    refine sub_eq_zero.1 (bigCellStatement_holds r X x0 ho (G + (nd X + 1) • Xa.L)
      (fun y => P y - ∑ k, Fl.s k y * Q k y) ⟨?_, fun x hx b hb => ?_⟩ (fun z hz => ?_) y hy)
    · exact hP.1.sub (DifferentiableOn.fun_sum fun k _ => (hs k).1.mul (hQ k).1)
    · beta_reduce
      rw [mul_sub, hP.2 x hx b hb, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(hs k).2.1 x hx b hb, (hQ k).2 x hx b hb, hwt, bchar_add X hb _ Xa.L]
      ring
    · rw [hPF z hz, hFH z hz, sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by rw [hQH k z hz]
  refine ⟨fun k => poin X (G + nd X • Xa.L) (Q k), fun k => (hPQ k).2.1, fun x hx => ?_⟩
  rw [← hpo x hx, hwt]
  exact poin_sum_mul _ (fun k _ => hs k) hsum hx fun k _ => (hPQ k).1 x hx

end GlobalTheory.DivFreeWeight
end

section
namespace GlobalTheory.Shares.VanDiv

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem leviO_phla_add_nsmul (x0 : Frame X.Ψ r) (F L : Wt X.Ψ r) (k : ℕ) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (phla X (F + k • L)) z ξ = leviO X x0 (phla X F) z ξ + k * leviO X x0 (phla X L) z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz F).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have e : (fun w => ((phla X (F + k • L) (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun w => ((phla X F (cpt X x0 w) + (k : ℝ) * phla X L (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [OW.phla_add_nsmul X hw]
  unfold leviO leviM
  rw [Y.fc_leviV_congr _ _ _ _ e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h3),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

theorem pnorm_mul_pow_sq (F L : Wt X.Ψ r) (m : ℕ) (g w : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm (F + m • L) (fun x => g x * w x ^ m) x ^ 2 = X.pnorm F g x ^ 2 * (X.pnorm L w x ^ 2) ^ m := by
  rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.phla_add_nsmul X hx, neg_add,
    Real.exp_add, ← mul_neg, Real.exp_nat_mul, map_mul, map_pow]
  ring

theorem model_division (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) (k : ℕ)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + (k + (nd X + 1)) • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    (g : Frame X.Ψ r → ℂ) (hg : X.IsBddSec (Xa.Fp + k • Xa.L) g) (hv : ∀ j, g (Fl.xs j) = 0) :
    ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ i, h i ∈ X.SS (Xa.Fp + (k + nd X) • Xa.L)) ∧
      ∀ x ∈ X.dom, g x * Fl.w0 x ^ (nd X + 1) = ∑ i, Fl.s i x * h i x := by
  obtain ⟨-, ⟨bb, m, hbb, hbm, hmar⟩, hL, -, hcusp⟩ := hm
  have e : ∀ a : ℕ, Xa.Fp + k • Xa.L + a • Xa.L = Xa.Fp + (k + a) • Xa.L := fun a => by
    rw [add_nsmul, add_assoc]
  obtain ⟨C, hC⟩ := hg.2
  have hC2 : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + k • Xa.L) g x ^ 2 ≤ C ^ 2 := fun x hx =>
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hC x hx) 2
  obtain ⟨B, hB⟩ := Fl.weightForm_vanishes.1.1.2
  obtain ⟨K, hK⟩ := Fl.denom_le_family
  obtain ⟨h, hh, hs⟩ := GlobalTheory.DivFreeWeight.division_order_one E r X Xa Fl (Xa.Fp + k • Xa.L)
    ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => by
      have h1 := hmar x0 ho z hz ξ
      have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hL x0 ho z hz ξ)
      rw [leviO_phla_add_nsmul x0 _ _ k hz]
      linarith⟩
    (by rw [e]; exact hcusp _) (by rw [e]; exact hfin)
    (fun x => g x * Fl.w0 x ^ (nd X + 1))
    ⟨GlobalTheory.Up.DivCorePf.isSec_mul hg.1 (GlobalTheory.Up.DivCorePf.isSec_pow Fl.weightForm_vanishes.1.1.1 _),
      √(C ^ 2 * (B ^ 2) ^ (nd X + 1)), fun x hx => by
        refine Real.le_sqrt_of_sq_le ?_
        rw [pnorm_mul_pow_sq _ _ _ _ _ hx]
        exact mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _)
          (pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2) _) (by positivity) (by positivity)⟩
    ⟨C ^ 2 * |K| ^ (nd X + 1), fun x hx => by
      rw [pnorm_mul_pow_sq _ _ _ _ _ hx, mul_assoc, ← mul_pow]
      refine mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) ((hK x hx).trans ?_) _)
        (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)⟩
    (fun j => by simp [hv j])
  exact ⟨h, fun i => hcusp _ _ (e _ ▸ hh i), hs⟩

end Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (K : ℕ) (b : Fin K → B.Cusp j u),
      R.sp u Set.univ ≤ Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i))) := by
  obtain ⟨K, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨K, b, Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ _)
  simp only [map_sum, map_smul, R.ev_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem vanishing_division : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hen honto k g hg hv
  classical
  have hwt : ∀ (a : ℕ) c, laR T j (addL wF wL a) c = (A.Xa c).Fp + a • (A.Xa c).L := fun a c => by
    rw [(GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj c).2.2.1, A.hF, A.hL]
  obtain ⟨f, hf, hgf⟩ := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL k)).1 g hg
  have hfin : ∀ (a : ℕ) (c : (T.U j T.σ₀).Comp), ∃ (K : ℕ) (b : Fin K → Frame ((T.U j T.σ₀).X c).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X c).SS ((A.Xa c).Fp + a • (A.Xa c).L),
      ∃ cc : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X c).dom, f x = ∑ i, cc i * b i x := by
    intro a c
    obtain ⟨K, b, hb⟩ := sp_le_span R (addL wF wL a)
    refine ⟨K, fun i => rdR h j (b i) c, fun p hp => ?_⟩
    have h1 := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto a)
      (Function.update (fun _ => 0) c p) (fun c' => by
        by_cases hc : c' = c
        · subst hc
          rw [Function.update_self, hwt]
          exact hp
        · rw [Function.update_of_ne hc]
          exact (siegelSpaceAlgebra_holds _ _ _ 0 0).2.2.1.1.1)
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hb h1)
    refine ⟨cc, fun x hx => ?_⟩
    have h2 := congrFun hcc (e.symm ⟨c, ⟨x, hx⟩⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2] at h2
    rw [Equiv.apply_symm_apply] at h2
    simpa using h2.symm
  have hdiv := fun c => model_division (A.Xa c) (Fl.Fl c) (A.mar c) k (hfin _ c) (f c)
    (hwt k c ▸ (hf c).1.1) (fun i => by
      have h1 := hv (en.symm ⟨c, i⟩)
      rw [hgf, hen, Equiv.apply_symm_apply] at h1
      exact h1)
  choose H hH hsum using hdiv
  refine ⟨WeightFamilies.dimY D j, ?_⟩
  have hs : ∀ i y, R.s w t i y = ∑ a, t (i, a) * rdR h j (w a) (e y).1 (e y).2.1 := fun i y => by
    simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  have hmem : ∀ i : Fin (WeightFamilies.dimY D j),
      (fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1) ∈ R.sp (addL wF wL (k + WeightFamilies.dimY D j)) Set.univ :=
    fun i => (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto _) (fun c => H c (Fin.cast (A.dim c).symm i))
      (fun c => by
        rw [hwt]
        have h1 := hH c (Fin.cast (A.dim c).symm i)
        rwa [show k + nd ((T.U j T.σ₀).X c) = k + WeightFamilies.dimY D j by rw [A.dim c]] at h1)
  have heq : R.s w t 0 ^ (WeightFamilies.dimY D j + 1) * g =
      ∑ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) * fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1 := by
    have hmon : ∀ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) = R.s w t i.succ := fun i => by
      unfold Rdg.mon
      rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp
    funext y
    simp only [hmon, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hs]
    have h1 := hsum _ _ (e y).2.2
    rw [show nd ((T.U j T.σ₀).X (e y).1) + 1 = WeightFamilies.dimY D j + 1 by rw [A.dim]] at h1
    rw [← Fl.h0, hgf, mul_comm, h1]
    refine Fintype.sum_equiv (finCongr (A.dim (e y).1)) _ _ fun a => ?_
    rw [Fl.hs]
    rfl
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Pi.single i 1, _, by simp, hmem i, rfl⟩

end GlobalTheory.Shares.VanDiv
end
