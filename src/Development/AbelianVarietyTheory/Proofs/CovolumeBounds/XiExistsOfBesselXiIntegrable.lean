import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuous
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitive
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SphericalFunctionLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_positive_volume_continuous : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  first | exact @GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | exact GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | (intros; apply GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn <;> assumption)
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_isotropic_orthonormal : ∀ k r : ℕ, 1 ≤ k → (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  first | exact @GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | exact GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | (intros; apply GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic <;> assumption)
end

section
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem submatrix_mul_upperTriangular_castLE {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin m) ℂ) {j : ℕ} (hj : j ≤ m) (hu : u.BlockTriangular id) :
    (A * u).submatrix id (Fin.castLE hj) =
      A.submatrix id (Fin.castLE hj) * u.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
  ext i b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ?_ ?_ ?_ ?_
  · intro a _ c _ h
    exact Fin.castLE_injective hj h
  · intro a _
    exact Finset.mem_univ _
  · intro c _ hc
    have hlt : Fin.castLE hj b < c := by
      by_contra hle
      apply hc
      have h1 : c.val ≤ b.val := by
        have := not_lt.mp hle
        exact this
      refine ⟨⟨c.val, lt_of_le_of_lt h1 b.2⟩, by simp, ?_⟩
      ext
      simp
    rw [hu (show id (Fin.castLE hj b) < id c from hlt), mul_zero]
  · intro a _
    rfl

theorem det_leading_gram_mul_upperTriangular :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  intro n m A u j hj hu
  have key : ∀ B : Matrix (Fin n) (Fin m) ℂ,
      (Bᴴ * B).submatrix (Fin.castLE hj) (Fin.castLE hj) =
        (B.submatrix id (Fin.castLE hj))ᴴ * B.submatrix id (Fin.castLE hj) := by
    intro B
    ext a b
    simp [Matrix.mul_apply]
  have hu' : (u.submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := by
    intro a b hab
    exact hu (show id (Fin.castLE hj b) < id (Fin.castLE hj a) from hab)
  rw [key, key, submatrix_mul_upperTriangular_castLE A u hj hu, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (u.submatrix (Fin.castLE hj) (Fin.castLE hj)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_upperTriangular hu']
  simp only [Matrix.submatrix_apply]
  rw [← map_prod Complex.normSq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end GlobalTheory.HCXi
end

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_minor_det_triangular_mul : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  atlas_forward_decl GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular
end

section
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem gram_nonneg_vmul (k r : ℕ) (g : Mat k r) (a : Fin (r + 1)) : 0 ≤ gram k r g a := by
  unfold gram
  have h := ((Matrix.posSemidef_conjTranspose_mul_self (g * frame k r)).submatrix
    (Fin.castLE (Nat.succ_le_of_lt a.isLt))).det_nonneg
  exact (Complex.nonneg_iff.mp h).1

theorem gram_unitary_mul (k r : ℕ) (κ g : Mat k r) (hκ : κᴴ * κ = 1) (a : Fin (r + 1)) :
    gram k r (κ * g) a = gram k r g a := by
  have h : (κ * g * frame k r)ᴴ * (κ * g * frame k r) = (g * frame k r)ᴴ * (g * frame k r) := by
    rw [Matrix.mul_assoc κ g, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]
  unfold gram
  rw [h]

theorem gram_mul_flag (k r : ℕ) (hk : 1 ≤ k) (g p : Mat k r) (hp : p ∈ Pset k r)
    (a : Fin (r + 1)) : gram k r (g * p) a = gram k r g a * gram k r p a := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  have hF := (GlobalTheory.T.frame_isotropic_orthonormal k r hk).1
  have h1 := GlobalTheory.T.gram_minor_det_triangular_mul _ _ (g * frame k r) u _ (Nat.succ_le_of_lt a.isLt) hu
  have h2 := GlobalTheory.T.gram_minor_det_triangular_mul _ _ (frame k r) u _ (Nat.succ_le_of_lt a.isLt) hu
  have e1 : g * p * frame k r = g * frame k r * u := by
    rw [Matrix.mul_assoc, hpu, Matrix.mul_assoc]
  rw [hF, Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one, mul_one] at h2
  unfold gram
  rw [e1, hpu, h1, h2, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm]

theorem vHalf_left_inv_and_mul : ∀ k r : ℕ, 1 ≤ k →
    (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧
    ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by
  intro k r hk
  refine ⟨fun κ hκ g => ?_, fun g _ p hp => ?_⟩
  · unfold vHalf
    simp only [gram_unitary_mul k r κ g hκ.2]
  · unfold vHalf
    simp only [gram_mul_flag k r hk g p hp, mul_inv, Finset.prod_mul_distrib]
    rw [Real.mul_rpow (gram_nonneg_vmul k r g _) (gram_nonneg_vmul k r p _)]
    ring

end GlobalTheory.HCXi
end

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_volume_equivariant : ∀ k r : ℕ, 1 ≤ k → (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧ ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by
  atlas_forward_decl GlobalTheory.HCXi.vHalf_left_inv_and_mul
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.Funct

lemma gv_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma meas_v {k r : ℕ} (hk : 1 ≤ k) {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {f : α → Mat k r} (hf : Continuous f) :
    Measurable fun t => ENNReal.ofReal (vHalf k r (f t)) := by
  have hm := (GlobalTheory.T.gram_positive_volume_continuous k r hk).2.2.1
  have hf' : Continuous (Y := Mt k r) fun t => Matrix.of.symm (f t) := hf
  exact ENNReal.measurable_ofReal.comp (hm.comp hf'.measurable)

lemma cont_of {k r : ℕ} : Continuous fun κ : Mt k r => (Matrix.of κ : Mat k r) := continuous_id

lemma inner {k r : ℕ} (μK : Measure (Mt k r)) (hk : 1 ≤ k) (hμ : IsKMeas k r μK) {x : Mat k r} (hx : x ∈ GV k r)
    {g : Mat k r} (hg : g ∈ GV k r) :
    (∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * Matrix.of κ * g)) ∂μK)
      = XiE k r μK x * ENNReal.ofReal (vHalf k r g) := by
  obtain ⟨κ₀, hκ₀, p, hp, rfl⟩ := GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k r hk g hg
  obtain ⟨hl, hr⟩ := GlobalTheory.T.half_volume_equivariant k r hk
  have hpos := (GlobalTheory.T.gram_positive_volume_continuous k r hk).2.1
  have hae : ∀ᵐ κ ∂μK, (Matrix.of κ : Mat k r) ∈ Kset k r := hμ.1.conc
  have hm : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * Matrix.of κ)) :=
    meas_v hk (continuous_const.matrix_mul cont_of)
  have hm2 : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) :=
    meas_v hk (continuous_const.matrix_mul (cont_of.matrix_mul continuous_const))
  have hrm : Measurable (rmulF κ₀ : Mt k r → Mt k r) :=
    Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
  have h1 : XiE k r μK x = ∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) ∂μK := by
    unfold XiE
    conv_lhs => rw [← hμ.1.right κ₀ hκ₀]
    rw [lintegral_map hm hrm]
    rfl
  rw [h1, ← lintegral_mul_const _ hm2, hl κ₀ hκ₀ p]
  refine lintegral_congr_ae (hae.mono fun κ hκ => ?_)
  have hmem : x * (Matrix.of κ * κ₀) ∈ GV k r := gv_mul hx (gv_mul hκ.1 hκ₀.1)
  have e : x * Matrix.of κ * (κ₀ * p) = x * (Matrix.of κ * κ₀) * p := by
    simp only [Matrix.mul_assoc]
  show ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
  rw [e, hr _ hmem p hp, ENNReal.ofReal_mul (hpos _ hmem).le]

end GlobalTheory.HCXi.Funct
end

section
namespace GlobalTheory.HCXi

theorem xiExists_of_besselXiIntegrable : BesselXiIntegrable → Formalism.FourierDecayAlt.B.XiExists := fun h => h

end GlobalTheory.HCXi
end
