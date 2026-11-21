import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnitNormAllOfCore
import Formalism.FormalDegreeBessel.FinalBF

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conj_mem_UJ {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  have hJ := hP.1.2
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * _ * (P * g * P⁻¹) = _
  have e1 : (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) =
      (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg', ← hJ]
  calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hinv']; simp

theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsCayleyU k r ε P) (g : Mx k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [hinv]; simp

theorem ds_rep {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
      (∀ a ∈ UH (Hpk k r), ∀ v : H, ‖σ a v‖ = ‖v‖) ∧
      ∀ v : H, ContinuousOn (fun g => σ g v) (UH (Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, -⟩ := hDS
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hinv] using h1
  · intro a ha b hb
    have h := hmul _ (conj_mem_UJ hP ha) _ (conj_mem_UJ hP hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (a * b) * P⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    simp only [e, conj_back hP] at h
    exact h
  · intro a ha v
    have h := hnorm _ (conj_mem_UJ hP ha) v
    simp only [conj_back hP] at h
    exact h
  · intro v
    have hc : Continuous (fun g : Mx k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h := (hcont v).comp hc.continuousOn (fun g hg => conj_mem_UJ hP hg)
    refine h.congr (fun g _ => ?_)
    show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
    rw [conj_back hP]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end PI.WBL.FSW
end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem star_inner (x y : Wp) : star ⟪x, y⟫_ℂ = ⟪y, x⟫_ℂ := by
  exact inner_conj_symm y x

variable [FiniteDimensional ℂ Wp]

end PI.WBL.FSW
end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Meas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

theorem ae_UH_of_haar {μG : Measure (Mt k r)} (h : IsHaarOn (UH (Hpk k r)) μG) :
    ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by
  rw [ae_iff]
  exact h.2.2.1

private theorem isClosed_UH' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    IsClosed (UH A) := by
  have hc : Continuous fun g : Matrix n n ℂ => gᴴ * A * g :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

theorem measurableSet_UH' : MeasurableSet {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  exact ((isClosed_UH' (Hpk k r)).preimage (continuous_id : Continuous fun y : Mt k r => y)).measurableSet

theorem coef_contOn {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (w v : H) :
    ContinuousOn (fun y : Mt k r => ⟪v, σ (Matrix.of y) w⟫_ℂ) {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  have hσ := (ds_rep hds).2.2.2 w
  have hof : Continuous fun y : Mt k r => (Matrix.of y : Mx k r) := continuous_id
  exact continuousOn_const.inner (hσ.comp hof.continuousOn fun y hy => hy)

theorem coef_aesm {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG) (w v : H) :
    AEStronglyMeasurable (fun y : Mt k r => ⟪v, σ (Matrix.of y) w⟫_ℂ) μG := by
  have h1 := (coef_contOn hds w v).aestronglyMeasurable (measurableSet_UH' (k := k) (r := r)) (μ := μG)
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)})
    (ae_UH_of_haar hG)] at h1

def Tset (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ UH (Hpk k r) ∧ (Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r)}

private theorem isClosed_UWset' (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have h1 : ∀ u : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mx k r => g *ᵥ u :=
    fun u => continuous_id.matrix_mulVec continuous_const
  simp only [UWset, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_UH' _).inter ((isClosed_iInter fun a =>
    (isClosed_eq (h1 _) continuous_const).inter (isClosed_eq (h1 _) continuous_const)).inter
      (isClosed_eq (h1 _) continuous_const))

private theorem isClosed_Nset_bessel_line (k r : ℕ) : IsClosed (Nset k r) := by
  simp only [Nset, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_UH' _).inter ((isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem _ _) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const))

theorem measurableSet_Tset (z : Fin (2 * r + k + 1) → ℂ) : MeasurableSet (Tset (k := k) (r := r) z) := by
  have c1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r) := continuous_fst
  have c2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r) :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r) :=
    continuous_snd.comp continuous_snd
  exact (((isClosed_UH' (Hpk k r)).preimage c1).inter
    (((isClosed_UWset' (k := k) (r := r) z).preimage c2).inter ((isClosed_Nset_bessel_line k r).preimage c3))).measurableSet

theorem joint_ae {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    [SFinite μG] (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ Tset z := by
  have h1 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ UH (Hpk k r) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_UH_of_haar hG)
  have h2 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hM1
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, hq2⟩

theorem matrix_coefficient_continuousOn {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z) (w v : H) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ) (Tset z) := by
  have hσ := (ds_rep hds).2.2.2 w
  have a1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mx k r) :=
    continuous_fst.comp continuous_snd
  have a2 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mx k r) :=
    continuous_snd.comp continuous_snd
  have a3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mx k r) := continuous_fst
  have hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => sM q.2 * Matrix.of q.1 := by
    unfold sM
    exact (a1.matrix_mul a2).matrix_mul a3
  refine continuousOn_const.inner (hσ.comp hc.continuousOn ?_)
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  exact hGr.1 _ (hGr.1 _ h2.1 _ h3.1) _ h1

theorem matrix_coefficient_ae_strongly_measurable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} (hGr : Cv.GrpF k r z)
    {μW μN μG : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μG] (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hM1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) (w v : H) :
    AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) => ⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ)
      (μG.prod (μW.prod μN)) := by
  have h := (matrix_coefficient_continuousOn hds hGr w v).aestronglyMeasurable (measurableSet_Tset z) (μ := μG.prod (μW.prod μN))
  rwa [Measure.restrict_eq_self_of_ae_mem (joint_ae hG hM1)] at h

theorem sfinite_haar {μG : Measure (Mt k r)} (h : IsHaarOn (UH (Hpk k r)) μG) : SFinite μG := by
  have := h.1
  infer_instance

end Meas

end PI.WBL.FSW
end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

theorem fdegH_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μG : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {d : ℝ}
    (hS : 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w : H} (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, h⟩ := hS
  obtain ⟨_, heq⟩ := h w w w w
  have h1 : ∀ x : Mt k r, ⟪w, σ (Matrix.of x) w⟫_ℂ * star ⟪w, σ (Matrix.of x) w⟫_ℂ =
      ((‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    have h3 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [← h1]
      rw [heq, inner_self_eq_norm_sq_to_K, Complex.ofReal_div, Complex.ofReal_pow]
      ring_nf
      try exact mul_comm _ _
    exact_mod_cast h3
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  show ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = d
  rw [hR]
  field_simp

end PI.WBL.FSW
end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Lemmas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

def trL : (Wp →L[ℂ] Wp) →L[ℂ] ℂ :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wp i)).comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wp i))

def kap (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (p : Mt k r × Mt k r) : ℂ :=
  psi k r z c (Matrix.of p.2) * star (trW (π (Matrix.of p.1)⁻¹))

end Lemmas

end PI.WBL.FSW
end
end
