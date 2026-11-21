import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.GoodS

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem v0_ne (C : Choice X θ) (τ : D.what₂.Tau) : v0Of C τ ≠ 0 := by
  intro h0
  have hy : (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hg := (C.isT τ).2.2.1
    have hyU : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
    calc (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ)
        = (C.Qi τ)ᴴ * ((C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.y τ) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hyU, qiHqi _ (C.isT τ).2.1 hg]
  have hn := (X.ds (vOf X τ)).2.2.1.2.1 _ hy (X.B.w (vOf X τ))
  have h1 := (X.low (vOf X τ)).1
  unfold v0Of sigB at h0
  rw [h0, norm_zero] at hn
  rw [← hn] at h1
  exact zero_ne_one h1

theorem finrank_pos (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : 0 < Module.finrank ℂ (X.Vloc u v) := by
  have : Nontrivial (X.Vloc u v) := (X.piLoc_type u v).1
  exact Module.finrank_pos

theorem l2SG_const_smul {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (s : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    l2SG ν (fun m => s • f m) = (‖s‖₊ : ℝ≥0∞) ^ 2 * l2SG ν f := by
  unfold l2SG
  simp only [nnnorm_smul, ENNReal.coe_mul, mul_pow]
  first
    | exact lintegral_const_mul' _ _ (by simp)
    | exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem goodSRest_of {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hLu : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hLu' : l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤)
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ := by
  set v := vOf X τ
  have hd : (0 : ℝ) < Module.finrank ℂ (X.Vloc u v) := by exact_mod_cast finrank_pos u v
  have hd' : (0 : ℝ) < Module.finrank ℂ (X.Vloc u' v) := by exact_mod_cast finrank_pos u' v
  have hL : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos hLu.1 hLu.2.ne
  have hL' : 0 < (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal := ENNReal.toReal_pos hLu'.1 hLu'.2.ne
  have hc : 0 < cOf hB u τ := div_pos hL hd
  refine ⟨Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, hsm, v0_ne C τ, hc, ?_, ?_, ?_⟩
  · show l2SG (C.nuS u τ) (phiOf hB u τ) = _
    rw [cOf, div_mul_cancel₀ _ hd.ne', ENNReal.ofReal_toReal hLu.2.ne]
  · show l2SG (C.nuS u' τ) (fun m => sclOf hB u u' τ • phiOf hB u' τ m) = _
    rw [l2SG_const_smul, sclOf]
    set a := cOf hB u τ * (Module.finrank ℂ (X.Vloc u' v) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal
      with ha
    have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hc.le hd'.le) hL'.le
    have hnorm : (‖((Real.sqrt a : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal a := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ha0]
    rw [hnorm, ← ENNReal.ofReal_toReal hLu'.2.ne, ← ENNReal.ofReal_mul ha0, ha, div_mul_cancel₀ _ hL'.ne']
  · obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP.1, ?_⟩
    have hε : ∀ i, epsSH D.R i = X.B.I.ε v (Fin.cast (n_eq' X).symm i) := fun i => by
      rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl)
    have hF := fdegHpk_tr (n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.σ v) (X.ds v).2.2.1
      (Formalism.L2.SG.Pf.RowDictPf.fdeg_of_schur X Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series v)
      (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
    have hDS := dsHpk_tr (n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.lam v) (lamSH D.R (D.hc τ))
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ v) (X.ds v) (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
    have hF2 := Formalism.L2.SG.Pf.RowDictPf.isFdeg_smul (D.s.cdScale_pos _ (epsSH D.R)) hF
    have htie := hT τ (X.B.H v) _ _ hDS hF2
    rw [← htie]
    exact hF2

end Formalism.L2.SG.Pf.GoodS
end
end

section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.WuBL

theorem l2RightTranslation_thm : L2RightTranslation := by
  classical
  intro k r z hz hT μG μS ν hG hS hq Vp _ W hWc hW0 hWS y hy
  obtain ⟨hGg, hSg, hSG, hRG, hRS⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (Formalism.QuantumDeterminants.Sset k r z) μG μS ν :=
    ⟨hGg, hSg, hSG, hG, hS, hRG μG hG, hRS μS hS, hq⟩
  let G : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}
  have hGc : IsClosed G := hGg.1.preimage continuous_id
  let F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ((‖W (Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2
  have hFG : F = G.piecewise F (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ G
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, F, hW0 (Matrix.of x) hx]
  have hcont : ContinuousOn F G := by
    have hW' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of x)) G :=
      hWc.comp continuous_id.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hW'.nnnorm)
  have hmeas : Measurable F := by
    rw [hFG]
    exact hcont.measurable_piecewise continuousOn_const hGc.measurableSet
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x : Formalism.QuantumDeterminants.Mt k r,
      Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      F (fun i j => (s * Matrix.of x) i j) = F x := by
    intro s hs x hx
    have h2 : ‖W (s * Matrix.of x)‖₊ = ‖W (Matrix.of x)‖₊ := NNReal.eq (hWS s hs (Matrix.of x) hx)
    change ((‖W (s * Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2 = _
    rw [h2]
  exact quotient_invariant (2 * r + k + 1) _ _ μG μS ν hset F hmeas hinv y hy

end Formalism.L2.SG.Pf.WuBL
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.GoodS

theorem nu_conc {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hS : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS) (hq : Formalism.MainNotions.S.IsQuotMeas μG μS ν) :
    ν {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  classical
  have hUH : ∀ a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro a b ha hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']
  have hSG : ∀ M, M ∈ Formalism.QuantumDeterminants.Sset k r z → M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rintro M ⟨g, hg, m, hm, rfl⟩
    exact hUH g m hg.1 hm.1
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x := by
    have h0 : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => Matrix.of x := continuous_id
    exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
  have hBm : MeasurableSet
      {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
    have hcl : IsClosed {x : Formalism.QuantumDeterminants.Mt k r |
        (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
      isClosed_eq hc continuous_const
    exact hcl.measurableSet.compl
  have hq1 := hq
    ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
      fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hBm)
  rw [lintegral_indicator_const hBm, hG.2.2.1, mul_zero] at hq1
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => μS Set.univ) x ≤
      ∫⁻ s, ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => (1 : ℝ≥0∞)) (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
    · have hnm : x ∉ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        fun h => h hx
      rw [Set.indicator_apply, if_neg hnm]
      exact bot_le
    · have hxm : x ∈ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := hx
      rw [Set.indicator_apply, if_pos hxm]
      calc μS Set.univ = ∫⁻ _, (1 : ℝ≥0∞) ∂μS := lintegral_one.symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Formalism.QuantumDeterminants.Sset k r z := ae_iff.mpr hS.2.2.1
          filter_upwards [hae] with s hs
          have hsG : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s = Formalism.QuantumDeterminants.Hpk k r :=
            hSG _ hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
            show ¬ (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
            intro hG'
            have e : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r *
                (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk k r := hG'
            apply hx
            show (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r
            rw [Matrix.conjTranspose_mul] at e
            calc (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x
                = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s) *
                    Matrix.of x := by rw [hsG]
              _ = Formalism.QuantumDeterminants.Hpk k r := by simpa only [Matrix.mul_assoc] using e
          simp only [Set.indicator_of_mem hmem, le_refl]
  have hle := lintegral_mono (μ := ν) hpt
  rw [lintegral_indicator_const hBm, ← hq1] at hle
  have hpos : μS Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr hS.2.1).ne'
  rcases mul_eq_zero.mp (nonpos_iff_eq_zero.mp hle) with h | h
  · exact absurd h hpos
  · exact h

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (m : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy := C.y_mem τ
  obtain ⟨hrep, -⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hm hy
  have hJ : (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hmy' : (m * C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (m * C.y τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hmy
    calc (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ)
        = (C.Qi τ)ᴴ * ((m * C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * (m * C.y τ)) *
            C.Qi τ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hmy', qiHqi _ h2 hg]
  set γ := toUJn (C.Q τ * (m * C.y τ) * C.Qi τ) hJ
  have hγ : uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ := rfl
  have hW := (hB u τ).choose_spec.2 γ
  have e1 : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) = X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hm _ hy, hγ]
    rfl
  unfold phiOf bOf
  rw [e1, ← hW, ← Formalism.L2.SG.Pf.WuBL.wT_at C u τ γ, hγ]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem l2SG_phiOf_ne_zero_and_lt_infty (C : Choice X θ) (hLF : LocFactor C) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤ := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  have hHG := Formalism.L2.SG.Pf.haarTr C τ
  have hq := C.nuS_q u τ
  have hy := C.y_mem τ
  have hconc := nu_conc hz hT hHG hSH hq
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
    rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]
  have heq := Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc
    (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) := by
    unfold l2SG
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [phi_eq C hB u τ _ hx]
  rw [hphi, heq]
  exact ⟨hne, hfin⟩

end Formalism.L2.SG.Pf.GoodS
end
end
