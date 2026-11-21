import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetMulRCReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiCoord
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix ComplexConjugate

section Iso

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_of_isom (f : E →ₗ[ℝ] F) (hn : ∀ x, ‖f x‖ = ‖x‖) (hs : Function.Surjective f) :
    MeasurePreserving f volume volume := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : ‖a - b‖ = 0 := by rw [← hn, map_sub, hab, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  let e : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective f ⟨hinj, hs⟩
  let g : E ≃ₗᵢ[ℝ] F := { e with norm_map' := hn }
  exact g.measurePreserving

variable {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem mp_of_isom_prod (f : U × V →ₗ[ℝ] F) (hn : ∀ a b, ‖f (a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2)
    (hs : Function.Surjective f) : MeasurePreserving f volume volume := by
  let L : WithLp 2 (U × V) ≃ₗ[ℝ] U × V := WithLp.linearEquiv 2 ℝ (U × V)
  have h1 : MeasurePreserving (f.comp L.toLinearMap) volume volume := by
    apply mp_of_isom
    · intro t
      have h := hn (L t).1 (L t).2
      have h2 := WithLp.prod_norm_sq_eq_of_L2 t
      have e : (L t) = ((L t).1, (L t).2) := rfl
      rw [← e] at h
      have h3 : ‖f (L t)‖ ^ 2 = ‖t‖ ^ 2 := by rw [h, h2]; rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
    · exact hs.comp L.surjective
  have h2 := WithLp.volume_preserving_toLp U V
  have h3 : (⇑(f.comp L.toLinearMap) ∘ WithLp.toLp 2) = ⇑f := by
    funext x
    rfl
  have h4 := h1.comp h2
  rwa [h3] at h4

end Iso

def reimL {n m : ℕ} : Matrix (Fin n) (Fin m) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun := reim
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]

theorem reimL_apply {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : reimL Y = reim Y := rfl

theorem norm_reim_sq {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) :
    ‖reim Y‖ ^ 2 = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [reim, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem reim_surj {n m : ℕ} (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    ∃ Y : Matrix (Fin n) (Fin m) ℂ, reim Y = y := by
  refine ⟨Matrix.of fun i j => ⟨y.ofLp (i, j, true), y.ofLp (i, j, false)⟩, ?_⟩
  ext p
  rcases p with ⟨i, j, s⟩
  cases s <;> simp [reim]

theorem herm_cross {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (∑ i, ∑ j, A i j * conj (B i j)).im = 0 := by
  have hA' : ∀ i j, A j i = conj (A i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hA j) i).symm
  have hB' : ∀ i j, B j i = conj (B i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hB j) i).symm
  have hc : conj (∑ i, ∑ j, A i j * conj (B i j)) = ∑ i, ∑ j, A i j * conj (B i j) := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA' j i, hB' j i, Complex.conj_conj]
  exact Complex.conj_eq_iff_im.mp hc

theorem herm_pyth {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ∑ i, ∑ j, ‖(Complex.I • A + B) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 + ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  have key : ∀ i j, ‖(Complex.I • A + B) i j‖ ^ 2 =
      ‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 - 2 * (A i j * conj (B i j)).im := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have h0 := herm_cross A B hA hB
  simp only [Complex.im_sum] at h0
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0]
  ring

def psiLp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun z := reimL (Complex.I • H z.1 + H z.2)
  map_add' a b := by
    show reimL (Complex.I • H (a + b).1 + H (a + b).2) =
      reimL (Complex.I • H a.1 + H a.2) + reimL (Complex.I • H b.1 + H b.2)
    rw [← map_add]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    rw [smul_comm Complex.I c, ← smul_add, map_smul]

theorem psiLp_apply {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (z : EuclideanSpace ℝ η × EuclideanSpace ℝ η) : psiLp H z = reim (Complex.I • H z.1 + H z.2) := rfl

theorem psi_mp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    MeasurePreserving (psiLp H) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [psiLp_apply, norm_reim_sq, herm_pyth _ _ (hH a) (hH b), hn a, hn b]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    set A : Matrix (Fin m) (Fin m) ℂ := (-(Complex.I / 2)) • (Y - Yᴴ) with hAdef
    set B : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (Y + Yᴴ) with hBdef
    have hA : Aᴴ = A := by
      rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hB : Bᴴ = B := by
      rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    obtain ⟨s, hsA⟩ := hs A hA
    obtain ⟨t, htB⟩ := hs B hB
    refine ⟨(s, t), ?_⟩
    rw [psiLp_apply]
    congr 1
    simp only [hsA, htB]
    ext i j
    simp [hAdef, hBdef, Complex.ext_iff]
    constructor <;> ring

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def liftL {Z E X : Type} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup E] [Module ℝ E] [AddCommGroup X]
    [Module ℝ X] (L : E →ₗ[ℝ] X) (hL : Function.Injective L) (Ξ : Z →ₗ[ℝ] X) (h : ∀ z, ∃ x, L x = Ξ z) :
    Z →ₗ[ℝ] E :=
  (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ
    Ξ.codRestrict (LinearMap.range L) (fun z => by obtain ⟨x, hx⟩ := h z; exact ⟨x, hx⟩)

theorem liftL_spec {Z E X : Type} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup E] [Module ℝ E] [AddCommGroup X]
    [Module ℝ X] (L : E →ₗ[ℝ] X) (hL : Function.Injective L) (Ξ : Z →ₗ[ℝ] X) (h : ∀ z, ∃ x, L x = Ξ z) (z : Z) :
    L (liftL L hL Ξ h z) = Ξ z := by
  have key := (LinearEquiv.ofInjective L hL).apply_symm_apply
    (Ξ.codRestrict (LinearMap.range L) (fun z => by obtain ⟨x, hx⟩ := h z; exact ⟨x, hx⟩) z)
  exact congrArg Subtype.val key

theorem inj_of_frob {ι p q : Type} [Fintype ι] [Fintype p] [Fintype q]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix p q ℂ) (hn : ∀ t, ∑ i, ∑ j, ‖L t i j‖ ^ 2 = ‖t‖ ^ 2) :
    Function.Injective L := by
  refine (injective_iff_map_eq_zero L).mpr ?_
  intro t ht
  have h := hn t
  rw [ht] at h
  simp only [Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at h
  have h2 : ‖t‖ ^ 2 = 0 := h.symm
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

def congL {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun M := Bᴴ * M * B
  map_add' _ _ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp

theorem congL_herm {m : ℕ} (B M : Matrix (Fin m) (Fin m) ℂ) (hM : Mᴴ = M) : (congL B M)ᴴ = congL B M := by
  show (Bᴴ * M * B)ᴴ = Bᴴ * M * B
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM,
    Matrix.mul_assoc]

def congH {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ η :=
  liftL H (inj_of_frob H hn) (congL B ∘ₗ H) (fun s => hs _ (congL_herm B _ (hH s)))

theorem congH_spec {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ) (s) :
    H (congH H hH hn hs B s) = Bᴴ * H s * B := by
  unfold congH
  exact liftL_spec _ _ _ _ s

theorem cong_factor {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ η)).map (congH H hH hn hs B) =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
  set C := congH H hH hn hs B with hCdef
  have hspec : ∀ s, H (C s) = Bᴴ * H s * B := congH_spec H hH hn hs B
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hBh : IsUnit Bᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hB)
  have canc : ∀ X : Matrix (Fin m) (Fin m) ℂ, (Bᴴ)⁻¹ * (Bᴴ * X * B) * B⁻¹ = X := by
    intro X
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hBh, Matrix.one_mul]
  have hinjC : Function.Injective C := by
    intro a b hab
    apply inj_of_frob H hn
    have h1 := congrArg H hab
    rw [hspec, hspec] at h1
    rw [← canc (H a), h1, canc]
  have hdet : LinearMap.det C ≠ 0 := fun h =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hinjC)
  have hC := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ η))) hdet
  set c := ENNReal.ofReal |(LinearMap.det C)⁻¹| with hc

  set mR : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    (reimE (r := m) (m := m)).toLinearMap ∘ₗ ((mulRC (r := m) B).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := m)).symm.toLinearMap with hmR
  set mL : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    (reimE (r := m) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) Bᴴ).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := m)).symm.toLinearMap with hmL
  have hmRf : (mR : _ → _) = fun y => reim (Matrix.of ((reimE (r := m) (m := m)).symm y) * B) := by
    funext y
    simp only [hmR, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulRC_apply]
    rfl
  have hmLf : (mL : _ → _) = fun y => reim (Bᴴ * Matrix.of ((reimE (r := m) (m := m)).symm y)) := by
    funext y
    simp only [hmL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulLC_apply]
    rfl
  have hR : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))).map mR =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [hmRf]; exact map_mulR B hB
  have hL : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))).map mL =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [hmLf, map_mulL Bᴴ (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hB), Matrix.det_conjTranspose,
      Complex.star_def, Complex.normSq_conj]
  have key : ∀ z : EuclideanSpace ℝ η × EuclideanSpace ℝ η, psiLp H (Prod.map C C z) = mL (mR (psiLp H z)) := by
    intro z
    rw [hmLf, hmRf]
    simp only [psiLp_apply, Prod.map_fst, Prod.map_snd, hspec]
    have e1 : ∀ M : Matrix (Fin m) (Fin m) ℂ, (reimE (r := m) (m := m)).symm (reim M) = M :=
      fun M => (reimE (r := m) (m := m)).symm_apply_apply M
    rw [e1, e1]
    congr 1
    show _ = Bᴴ * ((Complex.I • H z.1 + H z.2) * B)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hmC : Measurable C := C.continuous_of_finiteDimensional.measurable
  have hmP := psi_mp H hH hn hs
  have hmRm : Measurable mR := mR.continuous_of_finiteDimensional.measurable
  have hmLm : Measurable mL := mL.continuous_of_finiteDimensional.measurable
  have lhs : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map (psiLp H ∘ Prod.map C C) =
      (c * c) • volume := by
    rw [← Measure.map_map hmP.measurable (hmC.prodMap hmC), Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ hmC hmC, hC, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul, ← Measure.volume_eq_prod, hmP.map_eq]
  have rhs : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map (psiLp H ∘ Prod.map C C) =
      (ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ * ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹) • volume := by
    have : (psiLp H ∘ Prod.map C C) = mL ∘ mR ∘ psiLp H := funext key
    rw [this, ← Measure.map_map hmLm (hmRm.comp hmP.measurable), ← Measure.map_map hmRm hmP.measurable,
      hmP.map_eq, hR, Measure.map_smul, hL, smul_smul]
  have hball := lhs.symm.trans rhs
  have hv := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool)) => μ (Metric.ball 0 1)) hball
  simp only [Measure.smul_apply, smul_eq_mul] at hv
  have hpos : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hcc := (ENNReal.mul_left_inj hpos hfin).1 hv
  have q0 : 0 ≤ (Complex.normSq B.det ^ m)⁻¹ := inv_nonneg.2 (pow_nonneg (Complex.normSq_nonneg _) _)
  rw [hc, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul q0,
    ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg q0 q0),
    mul_self_inj (abs_nonneg _) q0] at hcc
  rw [hC, hc, hcc]
end AprimeInfW
end PI
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1

theorem sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : sgn ε i * sgn ε i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem star_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : star (sgn ε i) = sgn ε i := by
  unfold sgn
  split_ifs <;> simp

theorem star_I' : star Complex.I = -Complex.I := Complex.conj_I

theorem norm_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ‖sgn ε i‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem lie_apply {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M) i j = star (M j i) * sgn ε j + sgn ε i * M i j := by
  simp only [Matrix.add_apply, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, sgn]

def cpx {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a : Fin k) (b : Fin m) : ℂ :=
  ⟨u (a, b, true), u (a, b, false)⟩

theorem cpx_add {k m : ℕ} (u v : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (u + v) a b = cpx u a b + cpx v a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_smul {k m : ℕ} (c : ℝ) (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (c • u) a b = (c : ℂ) * cpx u a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_eq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    Matrix.of (cpx u) = Matrix.of ((reimE (r := k) (m := m)).symm u) := rfl

theorem cpx_reim {k m : ℕ} (Y : Matrix (Fin k) (Fin m) ℂ) (a b) : cpx (reim Y) a b = Y a b := by
  apply Complex.ext <;> simp [cpx, reim]

theorem norm_cpx_sq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    ‖u‖ ^ 2 = ∑ a, ∑ b, ‖cpx u a b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [cpx, Real.norm_eq_abs, sq]

def r2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem inv_sqrt_two_mul : r2 * (Real.sqrt 2 : ℂ) = 1 := by
  rw [r2, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr two_pos), Complex.ofReal_one]

theorem norm_inv_sqrt_two_sq : ‖r2‖ ^ 2 = 1 / 2 := by
  rw [r2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

variable {n k m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S})
  (eU : Fin m ≃ {i // i ∉ S}) {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)

def xiF (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if hi : i ∈ S then (if hj : j ∈ S then 0 else r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))
    else (if hj : j ∈ S then -(sgn ε i * sgn ε j) * star (r2 * cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩))
      else sgn ε i * Complex.I * H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))

def xiL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := xiF ε S eS eU H
  map_add' a b := by
    ext i j
    simp only [xiF, Matrix.add_apply]
    split_ifs <;> (try simp [cpx_add]) <;> ring
  map_smul' c z := by
    ext i j
    simp only [xiF, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [cpx_smul, Complex.real_smul, Complex.conj_ofReal]) <;> ring

theorem xi_SS (z) (a b : Fin k) : xiF ε S eS eU H z (eS a) (eS b) = 0 := by
  simp [xiF, (eS a).2, (eS b).2]

theorem xi_SU (z) (a : Fin k) (b : Fin m) : xiF ε S eS eU H z (eS a) (eU b) = r2 * cpx z.1 a b := by
  simp [xiF, (eS a).2, (eU b).2]

theorem xi_US (z) (a : Fin m) (b : Fin k) :
    xiF ε S eS eU H z (eU a) (eS b) = -(sgn ε (eU a) * sgn ε (eS b)) * star (r2 * cpx z.1 b a) := by
  simp [xiF, (eU a).2, (eS b).2]

theorem xi_UU (z) (a b : Fin m) : xiF ε S eS eU H z (eU a) (eU b) = sgn ε (eU a) * Complex.I * H z.2 a b := by
  simp [xiF, (eU a).2, (eU b).2]

theorem sum_split {M : Type} [AddCommMonoid M] (f : Fin n → M) : ∑ i, f i = ∑ a, f (eS a) + ∑ a, f (eU a) := by
  have h : ∑ i, f i = ∑ x : ↥S, f ↑x + ∑ x : {i // i ∉ S}, f ↑x := by
    convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f).symm
  exact h.trans (congrArg₂ (· + ·) (eS.sum_comp (fun x => f x)).symm (eU.sum_comp (fun x => f x)).symm)

theorem xi_norm (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (z) :
    ∑ i, ∑ j, ‖xiF ε S eS eU H z i j‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp only [sum_split S eS eU, xi_SS, xi_SU, xi_US, xi_UU, norm_zero, norm_mul, norm_neg, norm_star,
    norm_sgn, Complex.norm_I, mul_pow, norm_inv_sqrt_two_sq, one_mul, mul_one]
  rw [norm_cpx_sq z.1, ← hn z.2]
  have hc : ∑ x : Fin m, ∑ y : Fin k, ‖cpx z.1 y x‖ ^ 2 = ∑ y : Fin k, ∑ x : Fin m, ‖cpx z.1 y x‖ ^ 2 :=
    Finset.sum_comm
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc]
  ring

theorem xi_mem (hH : ∀ t, (H t)ᴴ = H t) (z) :
    (xiF ε S eS eU H z)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * xiF ε S eS eU H z = 0 ∧
      ∀ i ∈ S, ∀ j ∈ S, xiF ε S eS eU H z i j = 0 := by
  refine ⟨?_, fun i hi j hj => by simp [xiF, hi, hj]⟩
  have hHe : ∀ a b, star (H z.2 b a) = H z.2 a b := fun a b => by
    have h := congrFun (congrFun (hH z.2) a) b
    rwa [Matrix.conjTranspose_apply] at h
  ext i j
  rw [lie_apply, Matrix.zero_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, star_mul', star_neg, star_star, star_sgn]
    linear_combination (-(sgn ε i) * (r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j
  · simp only [xiF, dif_pos hj, dif_neg hi, star_mul']
    linear_combination (-(sgn ε j) * (star r2 * star (cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩)))) * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, star_mul', star_sgn, star_I', hHe]
    linear_combination (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε i - (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j

theorem xi_onto (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (ξ : Matrix (Fin n) (Fin n) ℂ)
    (h1 : ξᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ξ = 0) (h2 : ∀ i ∈ S, ∀ j ∈ S, ξ i j = 0) :
    ∃ z, xiF ε S eS eU H z = ξ := by
  have hξ : ∀ i j, star (ξ j i) * sgn ε j + sgn ε i * ξ i j = 0 := fun i j => by
    have h := congrFun (congrFun h1 i) j
    rwa [lie_apply, Matrix.zero_apply] at h
  let u : EuclideanSpace ℝ (Fin k × Fin m × Bool) :=
    reim (Matrix.of fun a b => (Real.sqrt 2 : ℂ) * ξ (eS a) (eU b))
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => -Complex.I * sgn ε (eU a) * ξ (eU a) (eU b)
  have hM : Mᴴ = M := by
    ext a b
    simp only [M, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_neg, star_I', star_sgn]
    linear_combination Complex.I * hξ (eU a) (eU b)
  obtain ⟨t, ht⟩ := hs M hM
  have e2 : ∀ w : ℂ, r2 * ((Real.sqrt 2 : ℂ) * w) = w := fun w => by rw [← mul_assoc, inv_sqrt_two_mul, one_mul]
  refine ⟨(u, t), ?_⟩
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj, h2 i hi j hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
  · simp only [xiF, dif_neg hi, dif_pos hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
    linear_combination (-(sgn ε i)) * hξ i j + ξ i j * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, ht, M, Matrix.of_apply, Equiv.apply_symm_apply]
    linear_combination (-(sgn ε i) ^ 2 * ξ i j) * Complex.I_sq + ξ i j * sgn_mul_self ε i

theorem dom_exists {ι : Type} [Fintype ι] (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0)
    (hnL : ∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2)
    (hLs : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M)
    (hH : ∀ t, (H t)ᴴ = H t) (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    ∃ Λ : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι,
      MeasurePreserving Λ volume volume ∧ ∀ z, L (Λ z) = xiF ε S eS eU H z := by
  have hxi : ∀ z, ∃ x, L x = xiL ε S eS eU H z := fun z =>
    hLs _ (xi_mem ε S eS eU H hH z).1 (xi_mem ε S eS eU H hH z).2
  let Λ := liftL L (inj_of_frob L hnL) (xiL ε S eS eU H) hxi
  have hΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z := fun z => liftL_spec L (inj_of_frob L hnL) _ hxi z
  refine ⟨Λ, mp_of_isom_prod Λ (fun a b => ?_) ?_, hΛ⟩
  · rw [← hnL, hΛ]
    exact xi_norm ε S eS eU H hnH (a, b)
  · intro x
    obtain ⟨z, hz⟩ := xi_onto ε S eS eU H hsH (L x) (hL x).1 (hL x).2
    exact ⟨z, inj_of_frob L hnL ((hΛ z).trans hz)⟩

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

variable {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S}) (eU : Fin m ≃ {i // i ∉ S})

def rowsM (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j => if hi : i ∈ S then X (eS.symm ⟨i, hi⟩) j else Y (eU.symm ⟨i, hi⟩) j

theorem rowsM_S (X Y) (a : Fin k) (j) : rowsM S eS eU X Y (eS a) j = X a j := by
  simp [rowsM]

theorem rowsM_U (X Y) (a : Fin m) (j) : rowsM S eS eU X Y (eU a) j = Y a j := by
  simp [rowsM, (eU a).2]

theorem rows_ext {p : Type} (X Y : Matrix (Fin n) p ℂ) (h1 : ∀ a j, X (eS a) j = Y (eS a) j)
    (h2 : ∀ a j, X (eU a) j = Y (eU a) j) : X = Y := by
  ext i j
  by_cases hi : i ∈ S
  · simpa using h1 (eS.symm ⟨i, hi⟩) j
  · simpa using h2 (eU.symm ⟨i, hi⟩) j

theorem of_cpx_reim {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℂ) : Matrix.of (cpx (reim X)) = X := by
  ext a b
  simp [cpx_reim]

def rsL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun z := reim (rowsM S eS eU (Matrix.of (cpx z.1)) (Matrix.of (cpx z.2)))
  map_add' a b := by
    ext p
    rcases p with ⟨i, j, c⟩
    by_cases hi : i ∈ S <;> cases c <;> simp [reim, rowsM, hi, cpx]
  map_smul' r z := by
    ext p
    rcases p with ⟨i, j, c⟩
    by_cases hi : i ∈ S <;> cases c <;> simp [reim, rowsM, hi, cpx]

theorem rsL_apply (z) : rsL S eS eU z = reim (rowsM S eS eU (Matrix.of (cpx z.1)) (Matrix.of (cpx z.2))) := rfl

theorem rs_mp : MeasurePreserving (rsL S eS eU) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [rsL_apply, norm_reim_sq, sum_split S eS eU, norm_cpx_sq a, norm_cpx_sq b]
    simp [rowsM_S, rowsM_U]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    refine ⟨(reim (Matrix.of fun a j => Y (eS a) j), reim (Matrix.of fun a j => Y (eU a) j)), ?_⟩
    rw [rsL_apply, of_cpx_reim, of_cpx_reim]
    congr 1
    apply rows_ext S eS eU
    · intro a j
      rw [rowsM_S]
      rfl
    · intro a j
      rw [rowsM_U]
      rfl

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

theorem const_alg (N P : ℝ) (k m : ℕ) (hN : N ≠ 0) (hP : P ≠ 0) :
    ((1 / P * N) ^ k)⁻¹ * (((P * N) ^ m)⁻¹ * ((1 / P ^ 2 * (N * (N ^ 2)⁻¹)) ^ m)⁻¹) = P ^ m * P ^ k / N ^ k := by
  have h1 : N * (N ^ 2)⁻¹ = N⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  have h2 : 1 / P ^ 2 * N⁻¹ = (P ^ 2 * N)⁻¹ := by
    rw [one_div, mul_inv]
  rw [h1, h2, inv_pow, inv_inv, one_div, mul_pow, mul_pow, mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul]
  field_simp
  ring

private theorem sum_eq_sum_compl_equiv_of_eq_zero_on {n m : ℕ} (S : Finset (Fin n)) (eU : Fin m ≃ {i // i ∉ S})
    (f : Fin n → ℂ) (hf : ∀ i ∈ S, f i = 0) : ∑ i, f i = ∑ c, f (eU c) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f,
    Finset.sum_eq_zero (fun i _ => hf i.1 i.2), zero_add]
  exact (Equiv.sum_comp eU (fun i => f i)).symm

private theorem rowsM_mul {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X : Matrix (Fin k) (Fin m) ℂ) (Y Z : Matrix (Fin m) (Fin m) ℂ) :
    rowsM S eS eU X Y * Z = rowsM S eS eU (X * Z) (Y * Z) := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi, Matrix.mul_apply]

private theorem rowsM_add_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X X' : Matrix (Fin k) (Fin m) ℂ) (Y Y' : Matrix (Fin m) (Fin m) ℂ) :
    rowsM S eS eU X Y + rowsM S eS eU X' Y' = rowsM S eS eU (X + X') (Y + Y') := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi]

private theorem smul_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (c : ℂ) (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    c • rowsM S eS eU X Y = rowsM S eS eU (c • X) (c • Y) := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi]

private theorem xiF_mul_eq_rowsM {n k m : ℕ} {η : Type} [Fintype η] (ε : Fin n → Bool) (S : Finset (Fin n))
    (eS : Fin k ≃ ↥S) (eU : Fin m ≃ {i // i ∉ S}) (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) :
    xiF ε S eS eU H z * w = rowsM S eS eU (Matrix.of (cpx z.1) * (r2 • Matrix.of fun b j => w (eU b) j))
      (Matrix.diagonal (fun a => sgn ε (eU a)) * (Complex.I • H z.2) * Matrix.of fun b j => w (eU b) j) := by
  ext i j
  rw [Matrix.mul_apply, sum_eq_sum_compl_equiv_of_eq_zero_on S eU _ (fun l hl => by rw [hw l hl, mul_zero])]
  by_cases hi : i ∈ S
  · obtain ⟨a, rfl⟩ : ∃ a, ((eS a : ↥S) : Fin n) = i := ⟨eS.symm ⟨i, hi⟩, by simp⟩
    rw [rowsM_S]
    simp only [xi_SU, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨a, rfl⟩ : ∃ a, ((eU a : {i // i ∉ S}) : Fin n) = i := ⟨eU.symm ⟨i, hi⟩, by simp⟩
    rw [rowsM_U, Matrix.mul_apply]
    simp only [xi_UU, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

private theorem mul_eq_rowsM_zero_of_zero_on {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    w * X = rowsM S eS eU 0 ((Matrix.of fun b j => w (eU b) j) * X) := by
  ext i j
  by_cases hi : i ∈ S
  · simp [rowsM, hi, Matrix.mul_apply, hw i hi]
  · simp [rowsM, hi, Matrix.mul_apply]

private theorem conjTranspose_mul_Jm_mul_eq_of_zero_on {n m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n))
    (eU : Fin m ≃ {i // i ∉ S}) (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0) :
    wᴴ * Formalism.REAL.Jm ε * w = (Matrix.of fun b j => w (eU b) j)ᴴ *
      Matrix.diagonal (fun a => sgn ε (eU a)) * (Matrix.of fun b j => w (eU b) j) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply, sum_eq_sum_compl_equiv_of_eq_zero_on S eU _ (fun i hi => by rw [hw i hi b, mul_zero])]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Formalism.REAL.Jm, Matrix.mul_diagonal, sgn, Matrix.conjTranspose_apply]

private theorem rsL_reim_eq_reim_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    rsL S eS eU (reim X, reim Y) = reim (rowsM S eS eU X Y) := by
  have h1 : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ), Matrix.of (cpx (reim Z)) = Z := by
    intro p q Z
    ext a b
    exact cpx_reim Z a b
  rw [rsL_apply, h1, h1]

private theorem dg_smul_mul_add_half_eq_half_mul_add {m : ℕ} (W0 Dg Hz Ht : Matrix (Fin m) (Fin m) ℂ) (hW : W0.det ≠ 0)
    (hD : Dg * Dg = 1) :
    Dg * (Complex.I • Hz) * W0 + (1 / 2 : ℂ) • (W0 * (W0ᴴ * Dg * W0)⁻¹ * Ht) =
      ((1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹)) *
        (Complex.I • ((((Real.sqrt 2 : ℝ) : ℂ) • W0)ᴴ * Hz * (((Real.sqrt 2 : ℝ) : ℂ) • W0)) + Ht) := by
  have hWu : IsUnit W0.det := isUnit_iff_ne_zero.mpr hW
  have hWHu : IsUnit W0ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  have hDinv : Dg⁻¹ = Dg := Matrix.inv_eq_left_inv hD
  have hG : W0 * (W0ᴴ * Dg * W0)⁻¹ = Dg * W0ᴴ⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDinv, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul]
  have hB : (((Real.sqrt 2 : ℝ) : ℂ) • W0)ᴴ * Hz * (((Real.sqrt 2 : ℝ) : ℂ) • W0) =
      (2 : ℂ) • (W0ᴴ * Hz * W0) := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hG, hB]
  have hP : W0ᴴ⁻¹ * W0ᴴ = 1 := Matrix.nonsing_inv_mul _ hWHu
  simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W0ᴴ⁻¹ W0ᴴ, hP, Matrix.one_mul]
  congr 1
  congr 1
  ring

private theorem of_reimE_reim {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix.of ((reimE (r := p) (m := q)).symm (reim Z)) = Z :=
  (reimE (r := p) (m := q)).symm_apply_apply Z

private theorem continuous_reim {p q : ℕ} : Continuous (fun Y : Matrix (Fin p) (Fin q) ℂ => reim Y) :=
  (reimL (n := p) (m := q)).continuous_of_finiteDimensional.congr fun Y => reimL_apply Y

set_option maxHeartbeats 800000 in

private theorem key_lemma_12 {n m : ℕ} {ι η : Type} [Fintype ι] [Fintype η] (ε : Fin n → Bool)
    (S : Finset (Fin n)) (eS : Fin S.card ≃ ↥S) (eU : Fin m ≃ {i // i ∉ S})
    (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) (hH : ∀ t, (H t)ᴴ = H t)
    (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M)
    (Λ : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hLΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z) (W0 Dg B A2 : Matrix (Fin m) (Fin m) ℂ)
    (hW0def : W0 = Matrix.of fun b j => w (eU b) j) (hDgdef : Dg = Matrix.diagonal fun a => sgn ε (eU a))
    (hBdef : B = ((Real.sqrt 2 : ℝ) : ℂ) • W0) (hA2def : A2 = (1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹))
    (hW0 : W0.det ≠ 0) (hDD : Dg * Dg = 1)
    (z1 : EuclideanSpace ℝ (Fin S.card × Fin m × Bool)) (z2 t : EuclideanSpace ℝ η) :
    reim (L (Λ (z1, z2)) * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H t)) =
      rsL S eS eU (reim (Matrix.of ((reimE (r := S.card) (m := m)).symm z1) * (r2 • W0)),
        reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
          (psiLp H (congH H hH hnH hsH B z2, t))))) := by
  subst hBdef hA2def
  rw [hLΛ, xiF_mul_eq_rowsM ε S eS eU H w hw, mul_eq_rowsM_zero_of_zero_on S eS eU w hw, rowsM_mul, smul_rowsM,
    rowsM_add_rowsM, psiLp_apply, of_reimE_reim, ← cpx_eq, rsL_reim_eq_reim_rowsM, congH_spec,
    conjTranspose_mul_Jm_mul_eq_of_zero_on ε S eU w hw, ← hW0def, ← hDgdef]
  congr 2
  · rw [Matrix.zero_mul, smul_zero, add_zero]
  · exact dg_smul_mul_add_half_eq_half_mul_add W0 Dg (H z2) (H t) hW0 hDD

set_option maxHeartbeats 800000 in

private theorem map_volume_reim_block_eq_of_det_ne_zero {m : ℕ} {η : Type} [Fintype η]
    (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) (hH : ∀ t, (H t)ᴴ = H t)
    (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M)
    (B A2 : Matrix (Fin m) (Fin m) ℂ) (hB : B.det ≠ 0) (hA : A2.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map
      (fun p => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
        (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))) =
      (ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ * ENNReal.ofReal (Complex.normSq A2.det ^ m)⁻¹) •
        volume := by
  have hc2 : Continuous fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      Matrix.of ((reimE (r := m) (m := m)).symm y) :=
    (reimE (r := m) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hmulLm : Measurable fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y)) :=
    (continuous_reim.comp (continuous_const.matrix_mul hc2)).measurable
  have hpsim : Measurable (psiLp H) := (psiLp H).continuous_of_finiteDimensional.measurable
  have hcgm : Measurable (congH H hH hnH hsH B) :=
    (congH H hH hnH hsH B).continuous_of_finiteDimensional.measurable
  have hPm : Measurable (Prod.map (congH H hH hnH hsH B)
      (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η)) := Measurable.prodMap hcgm measurable_id
  have hcg : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map
      (Prod.map (congH H hH hnH hsH B) id) =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hcgm measurable_id,
      cong_factor H hH hnH hsH B hB, Measure.map_id, Measure.prod_smul_left]
  have e : (fun p => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
      (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))) =
      (fun y => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y))) ∘ (psiLp H) ∘
        (Prod.map (congH H hH hnH hsH B) id) := rfl
  rw [e, ← Measure.map_map hmulLm (hpsim.comp hPm), ← Measure.map_map hpsim hPm, hcg,
    Measure.map_smul, (psi_mp H hH hnH hsH).map_eq, Measure.map_smul, map_mulL A2 hA, smul_smul]

private theorem inv_pow_mul_inv_pow_eq_two_pow_div_pow (N : ℝ) (m k : ℕ) (hN : N ≠ 0) :
    ((1 / (2 : ℝ) ^ m * N) ^ k)⁻¹ * ((((2 : ℝ) ^ m * N) ^ m)⁻¹ * (((1 / 4 : ℝ) ^ m * N⁻¹) ^ m)⁻¹) =
      2 ^ ((m + k) * m) / N ^ k := by
  have h4 : (1 / 4 : ℝ) ^ m * N⁻¹ = 1 / ((2 : ℝ) ^ m) ^ 2 * (N * (N ^ 2)⁻¹) := by
    rw [show N * (N ^ 2)⁻¹ = N⁻¹ by rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN, one_mul],
      show ((2 : ℝ) ^ m) ^ 2 = 4 ^ m by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      _root_.one_div_pow]
  rw [h4, const_alg N (2 ^ m) k m hN (by positivity), ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

set_option maxHeartbeats 800000 in

theorem placeJac_holds : PlaceJac := by
  intro n m ε S w ι η _ _ L H hn hw hG hL hnL hLs hH hnH hsH
  classical
  have hcardU : Fintype.card {i // i ∉ S} = m := by
    simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    omega
  obtain ⟨eS⟩ : Nonempty (Fin S.card ≃ ↥S) := ⟨S.equivFin.symm⟩
  obtain ⟨eU⟩ : Nonempty (Fin m ≃ {i // i ∉ S}) := ⟨(Fintype.equivFinOfCardEq hcardU).symm⟩
  obtain ⟨W0, hW0def⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = Matrix.of fun b j => w (eU b) j := ⟨_, rfl⟩
  obtain ⟨Dg, hDgdef⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = Matrix.diagonal fun a => sgn ε (eU a) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = ((Real.sqrt 2 : ℝ) : ℂ) • W0 := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = (1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹) := ⟨_, rfl⟩
  have hgram : wᴴ * Formalism.REAL.Jm ε * w = W0ᴴ * Dg * W0 := by
    rw [hW0def, hDgdef]
    exact conjTranspose_mul_Jm_mul_eq_of_zero_on ε S eU w hw
  have hDD : Dg * Dg = 1 := by
    rw [hDgdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [sgn]
    split_ifs <;> norm_num
  have hDnorm : ‖Dg.det‖ = 1 := by
    rw [hDgdef, Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [sgn]
    split_ifs <;> simp
  have hW0 : W0.det ≠ 0 := by
    intro h0
    apply hG
    rw [hgram, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hWHu : IsUnit W0ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW0)
  have hDdet : Dg.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDnorm
    exact zero_ne_one hDnorm
  have hBdet : B.det ≠ 0 := by
    rw [hBdef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')) hW0
  have hA2det : A2.det ≠ 0 := by
    rw [hA2def, Matrix.det_smul, Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero hDdet (Matrix.isUnit_nonsing_inv_det _ hWHu).ne_zero)
  have hR : (r2 • W0).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).ne')) hW0

  obtain ⟨Λ, hΛ, hLΛ⟩ := dom_exists (ε := ε) (S := S) (eS := eS) (eU := eU) (H := H)
    L hL hnL hLs hH hnH hsH

  have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
      Matrix.of ((reimE (r := S.card) (m := m)).symm y) :=
    (reimE (r := S.card) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hc2 : Continuous fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      Matrix.of ((reimE (r := m) (m := m)).symm y) :=
    (reimE (r := m) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hΦ1m : Measurable fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
      reim (Matrix.of ((reimE (r := S.card) (m := m)).symm y) * (r2 • W0)) :=
    (continuous_reim.comp (hc1.matrix_mul continuous_const)).measurable
  have hmulLm : Measurable fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y)) :=
    (continuous_reim.comp (continuous_const.matrix_mul hc2)).measurable
  have hpsim : Measurable (psiLp H) := (psiLp H).continuous_of_finiteDimensional.measurable
  have hcgm : Measurable (congH H hH hnH hsH B) :=
    (congH H hH hnH hsH B).continuous_of_finiteDimensional.measurable
  have hPm : Measurable (Prod.map (congH H hH hnH hsH B)
      (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η)) := Measurable.prodMap hcgm measurable_id
  have hΦ2m : Measurable fun p : EuclideanSpace ℝ η × EuclideanSpace ℝ η =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
        (psiLp H (Prod.map (congH H hH hnH hsH B) id p)))) := hmulLm.comp (hpsim.comp hPm)
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hHc : Continuous H := H.continuous_of_finiteDimensional
  have hFc : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2) := by
    have h1 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => L z.1 * w :=
      (hLc.comp continuous_fst).matrix_mul continuous_const
    have h2 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2 :=
      continuous_const.matrix_mul (hHc.comp continuous_snd)
    have h3 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2) := h2.const_smul (1 / 2 : ℂ)
    exact h1.add h3
  have hFm : Measurable fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2)) :=
    (continuous_reim.comp hFc).measurable
  have hrsm : Measurable (rsL S eS eU) := (rsL S eS eU).continuous_of_finiteDimensional.measurable
  have hΦm := Measurable.prodMap hΦ1m hΦ2m

  have hPre : MeasurePreserving (Prod.map Λ (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η))
      (volume : Measure ((EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η) ×
        EuclideanSpace ℝ η)) (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) := by
    rw [Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η)
      (EuclideanSpace ℝ η), Measure.volume_eq_prod (EuclideanSpace ℝ ι) (EuclideanSpace ℝ η)]
    exact hΛ.prod (MeasurePreserving.id _)
  have hAssoc := measurePreserving_prodAssoc
    (volume : Measure (EuclideanSpace ℝ (Fin S.card × Fin m × Bool)))
    (volume : Measure (EuclideanSpace ℝ η)) (volume : Measure (EuclideanSpace ℝ η))
  have hfun : (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2))) ∘ Prod.map Λ id =
      (rsL S eS eU) ∘ (Prod.map (fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
        reim (Matrix.of ((reimE (r := S.card) (m := m)).symm y) * (r2 • W0)))
        (fun p : EuclideanSpace ℝ η × EuclideanSpace ℝ η => reim (A2 * Matrix.of
          ((reimE (r := m) (m := m)).symm (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))))
        ∘ (MeasurableEquiv.prodAssoc) := by
    funext ⟨⟨z1, z2⟩, t⟩
    exact key_lemma_12 ε S eS eU w hw L H hH hnH hsH Λ hLΛ W0 Dg B A2 hW0def hDgdef hBdef hA2def hW0 hDD
      z1 z2 t
  rw [← hPre.map_eq, Measure.map_map hFm hPre.measurable, hfun,
    ← Measure.map_map hrsm (hΦm.comp MeasurableEquiv.prodAssoc.measurable),
    ← Measure.map_map hΦm MeasurableEquiv.prodAssoc.measurable,
    Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η)
      (EuclideanSpace ℝ η),
    Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool)) (EuclideanSpace ℝ η),
    hAssoc.map_eq, ← Measure.map_prod_map _ _ hΦ1m hΦ2m,
    ← Measure.volume_eq_prod (EuclideanSpace ℝ η) (EuclideanSpace ℝ η),
    map_volume_reim_block_eq_of_det_ne_zero H hH hnH hsH B A2 hBdet hA2det, map_mulR (r2 • W0) hR,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
    ← Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool))
      (EuclideanSpace ℝ (Fin m × Fin m × Bool)), (rs_mp S eS eU).map_eq]

  congr 1
  have hN : Complex.normSq W0.det ≠ 0 := (Complex.normSq_pos.mpr hW0).ne'
  have e1 : Complex.normSq (r2 • W0).det = 1 / (2 : ℝ) ^ m * Complex.normSq W0.det := by
    rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    congr 1
    simp only [r2, Complex.normSq_ofReal]
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_pow]
  have e2 : Complex.normSq B.det = (2 : ℝ) ^ m * Complex.normSq W0.det := by
    rw [hBdef, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdinv : Complex.normSq (W0ᴴ⁻¹).det = (Complex.normSq W0.det)⁻¹ := by
    have h1 : (W0ᴴ⁻¹).det * W0ᴴ.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hWHu, Matrix.det_one]
    have h3 := congrArg Complex.normSq h1
    rw [map_mul, map_one, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_conj] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hDsq : Complex.normSq Dg.det = 1 := by
    rw [Complex.normSq_eq_norm_sq, hDnorm, one_pow]
  have h12 : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    norm_num
  have e3 : Complex.normSq A2.det = (1 / 4) ^ m * (Complex.normSq W0.det)⁻¹ := by
    rw [hA2def, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, map_mul, map_mul, map_pow, hDsq,
      hdinv, h12, one_mul]
  have e4 : ‖(wᴴ * Formalism.REAL.Jm ε * w).det‖ = Complex.normSq W0.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hDnorm, mul_one,
      Matrix.det_conjTranspose, norm_star, Complex.normSq_eq_norm_sq, sq]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (Complex.normSq_nonneg _) _)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (Complex.normSq_nonneg _) _))]
  congr 1
  rw [e1, e2, e3, e4, show n * m = (m + S.card) * m from congrArg (· * m) hn,
    inv_pow_mul_inv_pow_eq_two_pow_div_pow _ m S.card hN]

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

theorem pi_smul_measure {V : Type} [Fintype V] {X : V → Type} [∀ v, MeasurableSpace (X v)]
    (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)] (c : V → ℝ≥0) :
    Measure.pi (fun v => c v • μ v) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi μ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem pi_map_smul {V : Type} [Fintype V] {X Y : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (Y v)] (μ : ∀ v, Measure (X v)) (ν : ∀ v, Measure (Y v)) [∀ v, SigmaFinite (ν v)]
    (f : ∀ v, X v → Y v) (hf : ∀ v, Measurable (f v)) (c : V → ℝ≥0)
    (hc : ∀ v, (μ v).map (f v) = c v • ν v) :
    (Measure.pi μ).map (fun x v => f v (x v)) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi ν := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v =>
    SigmaFinite.of_map (μ v) (hf v).aemeasurable (by rw [hc v]; infer_instance)
  rw [← pi_smul_measure]
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun x : ∀ v, X v => fun v => f v (x v)) :=
    measurable_pi_lambda _ fun v => (hf v).comp (measurable_pi_apply v)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ v, X v => fun v => f v (x v)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun v => f v ⁻¹' s v) := by
    ext x
    simp
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← hc v, Measure.map_apply (hf v) (hs v)]

theorem bij_of_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] F) (c : ℝ≥0∞) (h0 : c ≠ 0) (htop : c ≠ ⊤) (h : μ.map f = c • ν) : Function.Bijective f := by
  have key : ∀ s : Set F, MeasurableSet s → μ ((f : E → F) ⁻¹' s) = c * ν s := by
    intro s hs
    have h1 := congrArg (fun ρ : Measure F => ρ s) h
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rwa [Measure.map_apply (LinearMap.continuous_of_finiteDimensional f).measurable hs] at h1
  have hsurj : Function.Surjective f := by
    by_contra hns
    have hr : LinearMap.range f ≠ ⊤ := fun hh => hns (LinearMap.range_eq_top.mp hh)
    have h0 : ν (LinearMap.range f : Set F) = 0 := Measure.addHaar_submodule ν _ hr
    have hm : MeasurableSet (LinearMap.range f : Set F) :=
      (Submodule.closed_of_finiteDimensional (LinearMap.range f)).measurableSet
    have h1 := key _ hm
    rw [h0, mul_zero] at h1
    have hpre : (f : E → F) ⁻¹' (LinearMap.range f : Set F) = Set.univ := by
      ext x
      simp
    rw [hpre] at h1
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' h1
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := by
    set K : Set F := Metric.closedBall 0 1 with hKdef
    have hKc : IsCompact K := isCompact_closedBall 0 1
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    have hK0 : ν K ≠ 0 := (Metric.measure_closedBall_pos ν (0 : F) one_pos).ne'
    have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
    open Pointwise in
    have h2m : MeasurableSet ((2 : ℝ) • K) := (hKc.smul (2 : ℝ)).isClosed.measurableSet
    open Pointwise in
    have hpre : (f : E → F) ⁻¹' ((2 : ℝ) • K) = (2 : ℝ) • ((f : E → F) ⁻¹' K) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
        · rw [map_smul, ← hxy, smul_smul]
          norm_num
          exact hy
        · rw [smul_smul]
          norm_num
      · rintro ⟨y, hy, rfl⟩
        exact ⟨f y, hy, (map_smul f (2 : ℝ) y).symm⟩
    have e1 := key _ h2m
    rw [hpre, Measure.addHaar_smul, key K hKm, Measure.addHaar_smul] at e1
    set X := c * ν K with hX
    have hX0 : X ≠ 0 := mul_ne_zero h0 hK0
    have hXt : X ≠ ⊤ := ENNReal.mul_ne_top htop hKt
    have e2 : ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ E| * X =
        ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ F| * X := by
      rw [e1, hX]
      ring
    have hu : IsUnit X := isUnit_iff_exists_inv.mpr ⟨X⁻¹, ENNReal.mul_inv_cancel hX0 hXt⟩
    have e3 := hu.mul_left_inj.mp e2
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e3
    have e4 : (2 : ℕ) ^ Module.finrank ℝ E = 2 ^ Module.finrank ℝ F := by
      have e5 : ((2 : ℕ) : ℝ) ^ Module.finrank ℝ E = ((2 : ℕ) : ℝ) ^ Module.finrank ℝ F := by
        simpa using e3
      exact_mod_cast e5
    exact Nat.pow_right_injective (le_refl 2) e4
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

theorem norm_reimE_sq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖reimE (r := a) (m := b) M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [reimE, reim, Real.norm_eq_abs, sq_abs, sq]

set_option maxHeartbeats 800000 in

theorem place_split {V : Type} [Fintype V] {a b : ℕ} {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin a) (Fin b) ℂ)) (Q : V → Matrix (Fin a) (Fin b) ℂ → Prop)
    (hQ : ∀ x v, Q v (L x v)) (hQ0 : ∀ v, Q v 0)
    (hn : ∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2)
    (hs : ∀ M : V → Matrix (Fin a) (Fin b) ℂ, (∀ v, Q v (M v)) → ∃ x, L x = M) :
    ∃ (κ : V → Type) (_ : ∀ v, Fintype (κ v)) (Lv : ∀ v, EuclideanSpace ℝ (κ v) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ)
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (κ v)),
      (∀ v y, Q v (Lv v y)) ∧ (∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2) ∧
      (∀ v M, Q v M → ∃ y, Lv v y = M) ∧ (∀ x v, Lv v (T x v) = L x v) ∧ Function.Bijective T ∧
      (∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) := by
  classical
  let R : Matrix (Fin a) (Fin b) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a × Fin b × Bool) := reimE (r := a) (m := b)
  have hRn : ∀ M : Matrix (Fin a) (Fin b) ℂ, ‖R M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := fun M => norm_reimE_sq M
  let S : V → Submodule ℝ (EuclideanSpace ℝ (Fin a × Fin b × Bool)) := fun v =>
    LinearMap.range (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
  have hmem : ∀ v (M : Matrix (Fin a) (Fin b) ℂ), R M ∈ S v ↔ Q v M := by
    intro v M
    constructor
    · intro hM
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hM
      have hx' : R (L x v) = R M := by simpa using hx
      rw [← R.injective hx']
      exact hQ x v
    · intro hq
      obtain ⟨x, hx⟩ := hs (Pi.single v M) (fun w => by
        by_cases hw : w = v
        · subst hw
          rw [Pi.single_eq_same]
          exact hq
        · rw [Pi.single_eq_of_ne hw]
          exact hQ0 w)
      refine LinearMap.mem_range.mpr ⟨x, ?_⟩
      simp [hx]
  let n : V → ℕ := fun v => Module.finrank ℝ (S v)
  let B : ∀ v, OrthonormalBasis (Fin (n v)) ℝ (S v) := fun v => stdOrthonormalBasis ℝ (S v)
  let Lv : ∀ v, EuclideanSpace ℝ (Fin (n v)) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ := fun v =>
    R.symm.toLinearMap ∘ₗ (S v).subtype ∘ₗ (B v).repr.symm.toLinearEquiv.toLinearMap
  have hLv_apply : ∀ v y, R (Lv v y) = ((B v).repr.symm y : EuclideanSpace ℝ (Fin a × Fin b × Bool)) := by
    intro v y
    simp [Lv]
  have hLv_norm : ∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2 := by
    intro v y
    rw [← hRn, hLv_apply]
    exact congrArg (fun t => t ^ 2) ((B v).repr.symm.norm_map y)
  have hLvQ : ∀ v y, Q v (Lv v y) := by
    intro v y
    refine (hmem v _).mp ?_
    rw [hLv_apply]
    exact ((B v).repr.symm y).2
  have hLvSurj : ∀ v M, Q v M → ∃ y, Lv v y = M := by
    intro v M hq
    refine ⟨(B v).repr ⟨R M, (hmem v M).mpr hq⟩, ?_⟩
    apply R.injective
    rw [hLv_apply, LinearIsometryEquiv.symm_apply_apply]
  have hLvinj : ∀ v, Function.Injective (Lv v) := by
    intro v
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hLv_norm v y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hn y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  let Tv : ∀ v, EuclideanSpace ℝ ι →ₗ[ℝ] S v := fun v =>
    LinearMap.codRestrict (S v) (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
      (fun x => LinearMap.mem_range_self _ x)
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (Fin (n v)) :=
    LinearMap.pi fun v => (B v).repr.toLinearEquiv.toLinearMap ∘ₗ Tv v
  have hTL : ∀ x v, Lv v (T x v) = L x v := by
    intro x v
    apply R.injective
    rw [hLv_apply]
    simp [T, Tv]
  have hTinj : Function.Injective T := by
    intro x x' hxx
    apply hLinj
    funext v
    rw [← hTL x v, ← hTL x' v, hxx]
  have hTsurj : Function.Surjective T := by
    intro y
    obtain ⟨x, hx⟩ := hs (fun v => Lv v (y v)) (fun v => hLvQ v (y v))
    refine ⟨x, ?_⟩
    funext v
    apply hLvinj v
    rw [hTL, hx]
  have hTnorm : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← hn x]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hLv_norm v (T x v), hTL]
  exact ⟨fun v => Fin (n v), fun v => inferInstance, Lv, T, hLvQ, hLv_norm, hLvSurj, hTL, ⟨hTinj, hTsurj⟩, hTnorm⟩

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

section Lin

variable {n m : ℕ} {α β : Type} [Fintype α] [Fintype β]

def jacM (w : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (Lv : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (Hv : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    (EuclideanSpace ℝ α × EuclideanSpace ℝ β) →ₗ[ℝ] (Fin n → Fin m → ℂ) where
  toFun z := (Lv z.1 * w + (1 / 2 : ℂ) • (B * Hv z.2) : Matrix (Fin n) (Fin m) ℂ)
  map_add' z z' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Matrix.add_mul, Matrix.mul_add, smul_add]
    abel
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply]
    rw [smul_comm]
    exact (smul_add _ _ _).symm

def mulCR (c : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (reimE (r := n) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) c).restrictScalars ℝ) ∘ₗ
    (reimE (r := n) (m := m)).symm.toLinearMap

theorem mulCR_apply (c : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    mulCR c y = reim (c * Matrix.of ((reimE (r := n) (m := m)).symm y)) := by
  unfold mulCR
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, mulLC_apply]
  rfl

end Lin

def flatL (V β : Type) [Fintype V] [Fintype β] :
    (∀ _ : V, EuclideanSpace ℝ β) →ₗ[ℝ] EuclideanSpace ℝ (V × β) where
  toFun z := WithLp.toLp 2 (fun p : V × β => z p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatL_pres (V β : Type) [Fintype V] [Fintype β] :
    (Measure.pi fun _ : V => (volume : Measure (EuclideanSpace ℝ β))).map (flatL V β) = volume := by
  classical
  have hmeas : Measurable (fun z : V → β → ℝ => Function.uncurry z) := by
    have h := (MeasurableEquiv.curry V β ℝ).symm.measurable
    rw [MeasurableEquiv.coe_curry_symm] at h
    exact h
  have hU : MeasurePreserving (fun z : V → β → ℝ => Function.uncurry z) volume volume := by
    refine ⟨hmeas, ?_⟩
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun z : V → β → ℝ => Function.uncurry z) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun v => Set.pi Set.univ (fun b => s (v, b))) := by
      ext z
      simp [Function.uncurry]
    rw [hpre, volume_pi, Measure.pi_pi]
    simp only [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  have hP := volume_preserving_pi (fun _ : V => PiLp.volume_preserving_ofLp β)
  have hT := PiLp.volume_preserving_toLp (V × β)
  have h := (hT.comp hU).comp hP
  have hf : (⇑(flatL V β)) = (WithLp.toLp 2 ∘ fun z : V → β → ℝ => Function.uncurry z) ∘
      (fun z : V → EuclideanSpace ℝ β => fun v => WithLp.ofLp (z v)) := by
    funext z
    rfl
  rw [hf]
  exact h.map_eq

theorem detJm_ne {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> norm_num)

theorem normSq_det_of_unitary {n : ℕ} (ε : Fin n → Bool) (c : Matrix (Fin n) (Fin n) ℂ)
    (hc : cᴴ * Formalism.REAL.Jm ε * c = Formalism.REAL.Jm ε) : Complex.normSq c.det = 1 := by
  have h := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := detJm_ne ε
  have h2 : star c.det * c.det = 1 := by
    have e : (star c.det * c.det) * (Formalism.REAL.Jm ε).det = 1 * (Formalism.REAL.Jm ε).det := by
      rw [one_mul]
      nth_rewrite 2 [← h]
      ring
    exact mul_right_cancel₀ hJ e
  have h3 : ((Complex.normSq c.det : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, mul_comm]
    exact h2
  exact_mod_cast h3

theorem placeJacAll_of (h : PlaceJac) : PlaceJacAll := by
  classical
  intro V _ n m ε S w c ι κ _ _ L H hn hw hG hc hL1 hL2 hL3 hH1 hH2 hH3
  obtain ⟨ιv, _, Lv, T, hLQ, hLn, hLs, hLT, hTb, hTn⟩ := place_split L
    (fun v M => Mᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M i j = 0)
    hL1 (fun v => ⟨by simp, fun i _ j _ => rfl⟩) hL2 hL3
  obtain ⟨κv, _, Hv, T', hHQ, hHn, hHs, hHT, hT'b, hT'n⟩ := place_split H (fun v M => Mᴴ = M)
    hH1 (fun v => by simp) hH2 hH3
  let G : V → Matrix (Fin m) (Fin m) ℂ := fun v => (w v)ᴴ * Formalism.REAL.Jm (ε v) * w v
  let cst : V → ℝ := fun v => 2 ^ (n * m) / ‖(G v).det‖ ^ (S v).card
  have hcst : ∀ v, 0 < cst v := fun v => div_pos (by positivity) (pow_pos (norm_pos_iff.2 (hG v)) _)
  let Φ : ∀ v, (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
    fun v => mulCR (c v) ∘ₗ (reimE (r := n) (m := m)).toLinearMap ∘ₗ jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)
  have hΦ : ∀ v z, Φ v z = reim (c v * (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := by
    intro v z
    simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, mulCR_apply]
    congr 2
  have hPJ : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map
      (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) =
      ENNReal.ofReal (cst v) • volume :=
    fun v => h n m (ε v) (S v) (w v) (Lv v) (Hv v) (hn v) (hw v) (hG v) (hLQ v) (hLn v)
      (fun M h1 h2 => hLs v M ⟨h1, h2⟩) (hHQ v) (hHn v) (hHs v)
  have hd : ∀ v, (c v).det ≠ 0 := fun v h0 => by
    have := normSq_det_of_unitary (ε v) (c v) (hc v)
    rw [h0] at this
    simp at this
  have hΦm : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map (Φ v) =
      ((cst v).toNNReal : ℝ≥0∞) • volume := by
    intro v
    have e : (Φ v : _ → _) = (mulCR (m := m) (c v)) ∘
        (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := rfl
    have hm1 : Measurable (fun z : EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) =>
        reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) :=
      ((reimE (r := n) (m := m)).toLinearMap ∘ₗ
        jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)).continuous_of_finiteDimensional.measurable
    rw [e, ← Measure.map_map (mulCR (m := m) (c v)).continuous_of_finiteDimensional.measurable hm1, hPJ v,
      Measure.map_smul]
    have hC : (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool))).map (mulCR (m := m) (c v)) = volume := by
      have e2 : (mulCR (m := m) (c v) : _ → _) =
          fun y => reim (c v * Matrix.of ((reimE (r := n) (m := m)).symm y)) := funext (mulCR_apply (c v))
      rw [e2, map_mulL (c v) (hd v), normSq_det_of_unitary (ε v) (c v) (hc v)]
      simp
    rw [hC]
    rfl
  let F : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →ₗ[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
    flatL V (Fin n × Fin m × Bool) ∘ₗ
      (LinearMap.pi fun v => Φ v ∘ₗ LinearMap.prodMap (LinearMap.proj v ∘ₗ T) (LinearMap.proj v ∘ₗ T'))
  have hF : ∀ z, F z = reimV (fun v => c v * (L z.1 v * w v +
      (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v))) := by
    intro z
    have e1 : F z = flatL V (Fin n × Fin m × Bool) (fun v => Φ v (T z.1 v, T' z.2 v)) := rfl
    rw [e1]
    simp only [hΦ, hLT, hHT]
    rfl
  have hmT := PI.AprimeInfG.measurePreserving_of_normSq T hTb hTn
  have hmT' := PI.AprimeInfG.measurePreserving_of_normSq T' hT'b hT'n
  have h12 := hmT.prod hmT'
  have h3 := MeasurePreserving.symm (PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v))
    (fun v => EuclideanSpace ℝ (κv v))) (PI.AprimeInfG.measurePreserving_piProdEquiv
    (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v)) (fun v => volume) (fun v => volume))
  have h123 := h3.comp h12
  have hPm : Measurable (fun x : ∀ v, EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) => fun v => Φ v (x v)) :=
    measurable_pi_lambda _ fun v => (Φ v).continuous_of_finiteDimensional.measurable.comp (measurable_pi_apply v)
  have h4 := pi_map_smul (fun v => (volume : Measure (EuclideanSpace ℝ (ιv v))).prod volume)
    (fun v => (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool)))) (fun v => Φ v)
    (fun v => (Φ v).continuous_of_finiteDimensional.measurable) (fun v => (cst v).toNNReal)
    (fun v => by rw [ENNReal.smul_def]; exact hΦm v)
  have hfun : (F : _ → _) = flatL V (Fin n × Fin m × Bool) ∘ ((fun x v => Φ v (x v)) ∘
      ((PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v))).symm ∘
        Prod.map T T')) := rfl
  have hmap : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map F =
      ENNReal.ofReal (∏ v, cst v) • volume := by
    rw [hfun, ← Measure.map_map (flatL V (Fin n × Fin m × Bool)).continuous_of_finiteDimensional.measurable
      (hPm.comp h123.measurable), ← Measure.map_map hPm h123.measurable,
      show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl,
      h123.map_eq, h4, Measure.map_smul, flatL_pres, ENNReal.ofReal_prod_of_nonneg (fun v _ => (hcst v).le)]
    rfl
  have hpos : ENNReal.ofReal (∏ v, cst v) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun v _ => hcst v
  have : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).IsAddHaarMeasure := by
    rw [show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl]
    infer_instance
  have hbij := bij_of_map (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) volume F _ hpos
    ENNReal.ofReal_ne_top hmap
  exact ⟨(LinearEquiv.ofBijective F hbij).toContinuousLinearEquiv, fun z => hF z, hmap⟩

end PI.AprimeInfW
end
end

section
namespace PI.AprimeInfW

theorem placeJacAll_holds : PlaceJacAll := placeJacAll_of placeJac_holds

end PI.AprimeInfW
end
