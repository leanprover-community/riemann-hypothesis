import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2NormScaling

section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

variable {k r : ℕ}

local notation "MX" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
local notation "UHk" => Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

theorem uh_meas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
  have hc : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ((Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    fun_prop
  exact (isClosed_eq hc continuous_const).measurableSet

theorem sigma_one {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : MX → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hD⟩ := hds
  have h1 := hD.2.2.1.1.1
  have hPu : IsUnit P.det :=
    Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
  simpa [Matrix.nonsing_inv_mul P hPu] using h1

theorem zero_of_ae {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    {E : Type*} [NormedAddCommGroup E] {f : MX → E} (hf : ContinuousOn f UHk)
    (hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → f (Matrix.of x) = 0)
    {g0 : MX} (hg0 : g0 ∈ UHk) : f g0 = 0 := by
  by_contra hne
  obtain ⟨V, hVo, hV⟩ := (continuousOn_iff'.mp hf) {0}ᶜ isOpen_compl_singleton
  have hg0V : g0 ∈ V := by
    have hm : g0 ∈ f ⁻¹' {0}ᶜ ∩ UHk := ⟨hne, hg0⟩
    rw [hV] at hm
    exact hm.1
  have hnull0 : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ V ∧ Matrix.of x ∈ UHk} = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro x hx
    obtain ⟨hxV, hxU⟩ := hx
    have hm : Matrix.of x ∈ V ∩ UHk := ⟨hxV, hxU⟩
    rw [← hV] at hm
    exact fun h => hm.1 (h hxU)
  have hc0 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
  let O : UHk → Set (Formalism.QuantumDeterminants.Mt k r) := fun g => {y | (g : MX)⁻¹ * Matrix.of y ∈ V}
  have hO : ∀ g, IsOpen (O g) := fun g => hVo.preimage (continuous_const.matrix_mul hc0)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcover : ∀ y : Formalism.QuantumDeterminants.Mt k r, Matrix.of y ∈ UHk → ∃ g ∈ T, y ∈ O g := by
    intro y hy
    have hy' : y ∈ ⋃ g, O g := by
      refine Set.mem_iUnion.2 ⟨⟨Matrix.of y * g0⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg0)⟩, ?_⟩
      show (Matrix.of y * g0⁻¹)⁻¹ * Matrix.of y ∈ V
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0),
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy), Matrix.mul_one]
      exact hg0V
    rw [← hTU] at hy'
    obtain ⟨g, hgT, hyg⟩ := Set.mem_iUnion₂.1 hy'
    exact ⟨g, hgT, hyg⟩
  have hnullg : ∀ g : UHk,
      μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} = 0 := by
    intro g
    have hinv := hμ.2.2.2 g g.2
    have hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
    have hmeasO : MeasurableSet (O g) := (hO g).measurableSet
    have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g} :=
      uh_meas.inter hmeasO
    have hcm : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (g : MX)) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul hc1
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (g : MX)) := hcm.measurable
    rw [← hinv, Measure.map_apply hlm hmeas]
    refine measure_mono_null ?_ hnull0
    intro x hx
    obtain ⟨hxU, hxO⟩ := hx
    have hgu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh g.2
    have h1 : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) = Matrix.of x := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
    have hxO' : (g : MX)⁻¹ * ((g : MX) * Matrix.of x) ∈ V := hxO
    have hxU' : (g : MX) * Matrix.of x ∈ UHk := hxU
    refine ⟨?_, ?_⟩
    · rw [h1] at hxO'
      exact hxO'
    · have := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv g.2) hxU'
      rwa [h1] at this
  have hUnull : μG {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk} = 0 := by
    refine measure_mono_null
      (t := ⋃ g ∈ T, {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ UHk ∧ x ∈ O g})
      ?_ ((measure_biUnion_null_iff hTc).2 (fun g _ => hnullg g))
    intro x hx
    obtain ⟨g, hgT, hxg⟩ := hcover x hx
    exact Set.mem_iUnion₂.2 ⟨g, hgT, hx, hxg⟩
  apply hμ.2.1
  rw [← Measure.measure_univ_eq_zero]
  have hsplit : (Set.univ : Set (Formalism.QuantumDeterminants.Mt k r)) =
      {x | Matrix.of x ∈ UHk} ∪ {x | Matrix.of x ∉ UHk} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    exact em _
  rw [hsplit]
  exact measure_union_null hUnull hμ.2.2.1

theorem aez {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : MX → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hμN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hμG : PI.BesselPeriodGGP.IsHaarOn UHk μG)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) νq)
    (F : MX → Wp) (hFc : ContinuousOn F UHk)
    (hFeq : ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ UHk,
      F (h * n * g) = Formalism.QuantumDeterminants.psi k r z c n • π h (F g))
    (hl2 : PI.BesselPeriodGGP.l2SG νq F = 0) : ∀ g ∈ UHk, F g = 0 := by
  classical
  have := hμW.1
  have := hμN.1
  let S : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ UHk}
  let G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    S.piecewise (fun x => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) (fun _ => 0)
  have hSm : MeasurableSet S := uh_meas
  have hc1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : MX)) := continuous_id
  have hGc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) S := by
    have h2 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) S :=
      hFc.comp hc1.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn h2)
  have hGm : Measurable G := hGc.measurable_piecewise continuousOn_const hSm
  have hGle : ∀ x, G x ≤ (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    intro x
    by_cases hx : x ∈ S
    · simp [G, hx]
    · simp [G, hx]
  have hνG : ∫⁻ x, G x ∂νq = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc ∫⁻ x, G x ∂νq ≤ ∫⁻ x, (‖F (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νq := lintegral_mono hGle
      _ = PI.BesselPeriodGGP.l2SG νq F := rfl
      _ = 0 := hl2
  have hGae : ∀ᵐ x ∂νq, G x = 0 := (lintegral_eq_zero_iff hGm).1 hνG
  have hGval : ∀ x, x ∈ S → G x = 0 → F (Matrix.of x) = 0 := by
    intro x hx h0
    simp only [G, Set.piecewise, hx, if_true] at h0
    have : (‖F (Matrix.of x)‖₊ : ℝ≥0∞) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    simpa using this
  have hmul : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : MX)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : MX)) := continuous_snd
    exact h1.matrix_mul h2
  have hW : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hμW.2.2.1)
  have hN : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hμN.2.2.1)
  have hμGint : ∫⁻ x, G x ∂μG = 0 := by
    rw [hQ G hGm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hGae] with x hx
    show ∫⁻ s, G (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.FourierDecayAlt.ThreeDimData.muSof μW μN) = 0
    have hrm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
        G (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
      hGm.comp ((show Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) from
          hc1.matrix_mul continuous_const).measurable)
    rw [Formalism.FourierDecayAlt.ThreeDimData.muSof, lintegral_map hrm hmul.measurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hW, hN] with p hp1 hp2
    have hsU : Matrix.of p.1 * Matrix.of p.2 ∈ UHk := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1
    show G (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j) = 0
    by_cases hxU : x ∈ S
    · have hFx := hGval x hxU hx
      have hmem : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j :
          Formalism.QuantumDeterminants.Mt k r) ∈ S := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hsU hxU
      simp only [G, Set.piecewise, hmem, if_true]
      show (‖F (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 = 0
      rw [hFeq _ hp1 _ hp2 (Matrix.of x) hxU, hFx, map_zero, smul_zero]
      simp
    · have hnot : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of x) i j :
          Formalism.QuantumDeterminants.Mt k r) ∉ S := by
        intro hm
        exact hxU (DDSmoothness.uh_cancel hsU hm)
      simp only [G, Set.piecewise, hnot, if_false]
  have hGaeG : ∀ᵐ x ∂μG, G x = 0 := (lintegral_eq_zero_iff hGm).1 hμGint
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UHk → F (Matrix.of x) = 0 := by
    filter_upwards [hGaeG] with x hx hxU
    exact hGval x hxU hx
  intro g hg
  exact zero_of_ae hμG hFc hae hg

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P
end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

open Formalism.FourierDecayAlt.ThreeDimData

theorem vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : BeConv) (hIn : Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, hBC2, hBC3, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hc : ContinuousOn (fun g => be z c π σ μW μN (σ g x) v ξ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hBC3 x hx v hv).clm_apply continuousOn_const
  have heq : ∀ hh ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      be z c π σ μW μN (σ (hh * n * g) x) v ξ = Formalism.QuantumDeterminants.psi k r z c n • π hh (be z c π σ μW μN (σ g x) v ξ) := by
    intro hh hhW n hn g hg
    have hhn : hh * n ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhW.1 hn.1
    have hm : σ (hh * n * g) = (σ (hh * n)).comp (σ g) := TranslationBesselVanishing.sigma_mul hσ hhn hg
    rw [hm, ContinuousLinearMap.comp_apply,
      hBC2 v hv hh hhW n hn (σ g x) (TranslationBesselVanishing.smooth_translate hσ hx hg)]
    rfl
  have h0 := aez hW hN hG hq (fun g => be z c π σ μW μN (σ g x) v ξ) hc heq (hl ξ) 1 Formalism.QuantumDeterminants.WeylGroupFacts.uh_one
  simpa [sigma_one hσ] using h0

theorem zeroCaseDD_of (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp

theorem zeroCase_of (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCase := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  have hA := zeroCaseDD_of hBC hNI hSch hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hDD
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv

  have hB : ∀ u ∈ DDsp σ w0, be z c π σ μW μN u v = 0 := by
    intro u hu
    have h1 : be z c π σ μW μN v u = 0 := hA u hu v hvs
    have h2 := (hBC4 u hu v (Or.inr hv)).2
    rw [h1] at h2
    have h3 := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_adjoint, map_zero] at h3

  have hw0n : ‖w0‖ = 1 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    exact hn1
  have hw0ne : w0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw0n; exact zero_ne_one hw0n
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hdeg : PI.BesselPeriodGGP.fdegH μG σ w0 = d := DDSmoothness.fdeg_eq hd hSd hw0ne
  have hw0DD : w0 ∈ DDsp σ w0 := by
    refine Submodule.subset_span ⟨1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, ?_⟩
    simp [sigma_one hσ]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 w0 hw0DD
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hC : ∀ ξ : Wp, ⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ = 0 := by
    intro ξ
    obtain ⟨hNv, him, hre⟩ := hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS w0 hw0s v (Or.inr hv) ξ
    have hL : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g w0) v ξ) = 0 := by
      unfold PI.BesselPeriodGGP.l2SG
      refine (lintegral_congr_ae (hae.mono fun g hg => ?_)).trans lintegral_zero
      have hgD : σ (Matrix.of g) w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨Matrix.of g, hg, rfl⟩
      simp [hB _ hgD]
    rw [hL, hdeg, hw0n] at hNv
    have h0 : 1 ^ 2 * (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re / d ≤ 0 := ENNReal.ofReal_eq_zero.mp hNv.symm
    have hre0 : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re = 0 := by
      have : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re ≤ 0 := by
        rw [one_pow, one_mul] at h0
        exact (div_nonpos_iff.mp h0).elim (fun h => absurd h.2 (not_le.mpr hd)) (fun h => h.1)
      linarith
    exact Complex.ext hre0 him
  have hvv : be z c π σ μW μN v v = 0 := by
    have hlin : (be z c π σ μW μN v v : Wp →ₗ[ℂ] Wp) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro ξ
      rw [← inner_conj_symm]
      simp [hC ξ]
    ext ξ
    have := LinearMap.congr_fun hlin ξ
    simpa using this

  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inr hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) ξ).1, hvv]
  simp

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P
end
end
