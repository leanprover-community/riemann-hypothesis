import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.ExistsIntOfMemIntegralFiniteAdeles
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

section
open NumberField IsDedekindDomain Matrix CongruenceSubgroup
open GroundTheory.Global
open scoped MatrixGroups

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

def toReal : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)

@[simp]
theorem toReal_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (toReal γ : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) :=
  rfl

theorem det_toReal (γ : GL (Fin 2) ℚ) : (toReal γ).det.val = ((γ.det.val : ℚ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact ((Rat.castHom ℝ).map_det (γ : Matrix (Fin 2) (Fin 2) ℚ)).symm

def realInf : GL (Fin 2) ℝ →* InfiniteAdelicGL ℚ 2 :=
  Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.symm.toRingHom

def realEmb : GL (Fin 2) ℝ →* AdelicGL ℚ 2 :=
  (prodEquiv ℚ 2).symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp realInf)

theorem prodEquiv_realEmb (h : GL (Fin 2) ℝ) : prodEquiv ℚ 2 (realEmb h) = (realInf h, 1) :=
  (prodEquiv ℚ 2).apply_symm_apply _

theorem realInf_injective : Function.Injective realInf := fun x y hxy => by
  refine Units.ext (Matrix.ext fun a b => ?_)
  have := congrArg (fun g : InfiniteAdelicGL ℚ 2 =>
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) hxy
  exact RationalIdeles.realEquiv.symm.injective this


theorem realEmb_mul_finEmb_comm (h : GL (Fin 2) ℝ) (y : FiniteAdelicGL ℚ 2) :
    realEmb h * finEmb ℚ 2 y = finEmb ℚ 2 y * realEmb h := by
  apply (prodEquiv ℚ 2).injective
  simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]

def realPart (g : AdelicGL ℚ 2) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.toRingHom (prodEquiv ℚ 2 g).1

theorem realInf_realPart (g : AdelicGL ℚ 2) : realInf (realPart g) = (prodEquiv ℚ 2 g).1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  exact RationalIdeles.realEquiv.symm_apply_apply _

theorem realEmb_realPart_mul_finEmb (g : AdelicGL ℚ 2) :
    realEmb (realPart g) * finEmb ℚ 2 (prodEquiv ℚ 2 g).2 = g := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul,
    realInf_realPart]

theorem diagonal_eq (γ : GL (Fin 2) ℚ) :
    diagonal ℚ 2 γ = realEmb (toReal γ) * finEmb ℚ 2 (finiteDiagonal ℚ 2 γ) := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (Units.ext (Matrix.ext fun a b => ?_))
  · change (algebraMap ℚ (InfiniteAdeleRing ℚ)) (γ a b) =
      RationalIdeles.realEquiv.symm (((γ : Matrix (Fin 2) (Fin 2) ℚ) a b : ℚ) : ℝ)
    exact RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (InfiniteAdeleRing ℚ))
      (RationalIdeles.realEquiv.symm.toRingHom.comp (Rat.castHom ℝ))) _
  · rfl

theorem diagonal_mul_realEmb_mul_finEmb (δ γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ)
    (u : FiniteAdelicGL ℚ 2) :
    diagonal ℚ 2 δ * realEmb h * finEmb ℚ 2 u =
      diagonal ℚ 2 (δ * γ) * realEmb ((toReal γ)⁻¹ * h) *
        finEmb ℚ 2 ((finiteDiagonal ℚ 2 γ)⁻¹ * u) := by
  apply (prodEquiv ℚ 2).injective
  simp only [map_mul, map_inv, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk,
    Prod.inv_mk, mul_one, one_mul, inv_one]
  refine Prod.ext ?_ ?_ <;> simp only [] <;> group

variable (N : ℕ) [NeZero N]

theorem finiteDiagonal_mem_Gamma0Level_of_int {γ : GL (Fin 2) ℚ} (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ i j, (A i j : ℚ) = γ i j) (hB : ∀ i j, (B i j : ℚ) = (γ⁻¹ : GL (Fin 2) ℚ) i j)
    (hN : (N : ℤ) ∣ A 1 0) : finiteDiagonal ℚ 2 γ ∈ Gamma0Level N := by
  refine ⟨(mem_integralFiniteGL_iff ℚ 2).2 ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · rw [finiteDiagonal_apply, ← hA, map_intCast]
    exact intCast_mem_integralFiniteAdeles _
  · rw [← map_inv, finiteDiagonal_apply, ← hB, map_intCast]
    exact intCast_mem_integralFiniteAdeles _
  · obtain ⟨m, hm⟩ := hN
    refine ⟨(m : 𝔸f), intCast_mem_integralFiniteAdeles m, ?_⟩
    change algebraMap ℚ 𝔸f (γ 1 0) = _
    rw [← hA, hm, Int.cast_mul, map_mul, map_intCast, map_intCast, Int.cast_natCast]

@[simp]
theorem mapGL_apply (σ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) :=
  rfl

theorem toReal_mapGL (σ : SL(2, ℤ)) :
    toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ) = Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) : ℝ) = ((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)
  exact Rat.cast_intCast _

theorem finiteDiagonal_mapGL_mem_Gamma0Level {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) :
    finiteDiagonal ℚ 2 (Matrix.SpecialLinearGroup.mapGL ℚ σ) ∈ Gamma0Level N := by
  refine finiteDiagonal_mem_Gamma0Level_of_int N (σ : Matrix (Fin 2) (Fin 2) ℤ)
    ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (fun i j => rfl) (fun i j => ?_) ?_
  · rw [← map_inv]
    rfl
  · rw [Gamma0_mem] at hσ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hσ

theorem exists_mem_Gamma0_of_mem {γ : GL (Fin 2) ℚ} (hγ : finiteDiagonal ℚ 2 γ ∈ Gamma0Level N)
    (hdet : 0 < (γ.det.val : ℚ)) :
    ∃ σ ∈ Gamma0 N, Matrix.SpecialLinearGroup.mapGL ℚ σ = γ := by
  obtain ⟨A, hA, hN, hd⟩ := exists_int_of_finiteDiagonal_mem N hγ
  have hdetA : ((A.det : ℤ) : ℚ) = γ.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have e : (Int.castRingHom ℚ).mapMatrix A = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j
      exact hA i j
    rw [← e, ← RingHom.map_det]
    rfl
  have h1 : A.det = 1 := by
    rcases hd with h | h
    · exact h
    · rw [h] at hdetA
      rw [← hdetA] at hdet
      norm_num at hdet
  refine ⟨(⟨A, h1⟩ : SL(2, ℤ)), ?_, Units.ext (Matrix.ext fun i j => hA i j)⟩
  exact Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hN)

def epsilon : GL (Fin 2) ℚ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

theorem epsilon_inv : epsilon⁻¹ = epsilon :=
  inv_eq_of_mul_eq_one_right (Units.ext (by simp [epsilon, Matrix.one_fin_two]))

theorem det_toReal_epsilon : (toReal epsilon).det.val = -1 := by
  rw [det_toReal, Matrix.GeneralLinearGroup.val_det_apply]
  simp [epsilon, Matrix.det_fin_two_of]

theorem finiteDiagonal_epsilon_mem : finiteDiagonal ℚ 2 epsilon ∈ Gamma0Level N := by
  refine finiteDiagonal_mem_Gamma0Level_of_int N !![-1, 0; 0, 1] !![-1, 0; 0, 1] ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [epsilon]
  · intro i j
    rw [epsilon_inv]
    fin_cases i <;> fin_cases j <;> simp [epsilon]
  · simp

theorem exists_decomposition (g : AdelicGL ℚ 2) :
    ∃ γ : GL (Fin 2) ℚ, ∃ h : GL (Fin 2) ℝ, 0 < h.det.val ∧ ∃ u ∈ Gamma0Level N,
      g = diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u := by
  obtain ⟨δ, u, hu, hy⟩ := exists_eq_finiteDiagonal_mul N (prodEquiv ℚ 2 g).2
  have hg : g = diagonal ℚ 2 δ * realEmb ((toReal δ)⁻¹ * realPart g) * finEmb ℚ 2 u := by
    conv_lhs => rw [← realEmb_realPart_mul_finEmb g, hy]
    apply (prodEquiv ℚ 2).injective
    simp only [map_mul, map_inv, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk,
      Prod.inv_mk, inv_one, mul_one, one_mul]
    rw [Prod.mk.injEq]
    exact ⟨by group, by group⟩
  set x := (toReal δ)⁻¹ * realPart g
  by_cases hx : 0 < x.det.val
  · exact ⟨δ, x, hx, u, hu, hg⟩
  · refine ⟨δ * epsilon, (toReal epsilon)⁻¹ * x, ?_, (finiteDiagonal ℚ 2 epsilon)⁻¹ * u,
      mul_mem (inv_mem (finiteDiagonal_epsilon_mem N)) hu,
      hg.trans (diagonal_mul_realEmb_mul_finEmb δ epsilon x u)⟩
    have hne : x.det.val ≠ 0 := x.det.ne_zero
    have hneg : x.det.val < 0 := lt_of_le_of_ne (not_lt.1 hx) hne
    rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal_epsilon]
    linarith

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open Matrix UpperHalfPlane

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

theorem det_fin_two_kmat (w : ℂ) : (!![w.re, -w.im; w.im, w.re] : Matrix (Fin 2) (Fin 2) ℝ).det =
    Complex.normSq w := by
  rw [Matrix.det_fin_two_of, Complex.normSq_apply]
  ring

def kGL (w : ℂ) (hw : w ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![w.re, -w.im; w.im, w.re] (by
    rw [det_fin_two_kmat]
    exact (Complex.normSq_pos.2 hw).ne')

@[simp]
theorem coe_kGL (w : ℂ) (hw : w ≠ 0) :
    (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ) = !![w.re, -w.im; w.im, w.re] :=
  rfl

theorem det_kGL (w : ℂ) (hw : w ≠ 0) : (kGL w hw).det.val = Complex.normSq w := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_kGL, det_fin_two_kmat]

theorem det_kGL_pos (w : ℂ) (hw : w ≠ 0) : 0 < (kGL w hw).det.val := by
  rw [det_kGL]
  exact Complex.normSq_pos.2 hw

theorem denom_kGL (w : ℂ) (hw : w ≠ 0) : denom (kGL w hw) (I : ℂ) = w := by
  rw [denom]
  apply Complex.ext <;> simp

theorem kGL_smul_I (w : ℂ) (hw : w ≠ 0) : kGL w hw • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_kGL_pos w hw), denom_kGL, div_eq_iff hw]
  rw [num]
  apply Complex.ext <;> simp


def borelGL (z : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![z.im, z.re; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    simpa using z.im_pos.ne')

@[simp]
theorem coe_borelGL (z : ℍ) :
    (borelGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] :=
  rfl

theorem det_borelGL (z : ℍ) : (borelGL z).det.val = z.im := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelGL, Matrix.det_fin_two_of]
  ring

theorem det_borelGL_pos (z : ℍ) : 0 < (borelGL z).det.val := by
  rw [det_borelGL]
  exact z.im_pos

theorem denom_borelGL (z : ℍ) (w : ℂ) : denom (borelGL z) w = 1 := by
  simp [denom]

theorem borelGL_smul_I (z : ℍ) : borelGL z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_borelGL_pos z), denom_borelGL, div_one, num]
  apply Complex.ext <;> simp

theorem re_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).re = ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 0 + h 0 1 * h 1 1) /
      Complex.normSq (denom h (I : ℂ)) := by
  rw [UpperHalfPlane.re, coe_smul_of_det_pos hpos, Complex.div_re]
  simp only [num, denom, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, coe_I, Complex.I_re, Complex.I_im]
  ring

theorem im_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).im = h.det.val / Complex.normSq (denom h (I : ℂ)) := by
  rw [im_smul_eq_div_normSq, abs_of_pos hpos, I_im, mul_one]

theorem eq_borelGL_mul_kGL {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    h = borelGL (h • I) * kGL (denom h (I : ℂ)) (denom_ne_zero h I) := by
  have hN : Complex.normSq (denom h (I : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.2 (denom_ne_zero h I)).ne'
  have hN' : Complex.normSq (denom h (I : ℂ)) = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 := by
    simp [denom, Complex.normSq_apply]
    ring
  have hdet : h.det.val = (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hre := re_smul_I hpos
  have him := im_smul_I hpos
  rw [hN'] at hre him
  have hD : (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 ≠ 0 := hN' ▸ hN
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_borelGL, coe_kGL]
  have hdr : (denom h (I : ℂ)).re = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [denom]
  have hdi : (denom h (I : ℂ)).im = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp [denom]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, hdr, hdi, hre, him, hdet] <;>
    field_simp <;> ring

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} (k : ℤ)

theorem σ_of_det_pos {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℂ) : σ h z = z := by
  rw [σ, if_pos hpos]
  rfl

theorem denom_mul_of_det_pos (g : GL (Fin 2) ℝ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℍ) :
    denom (g * h) z = denom g ((h • z : ℍ) : ℂ) * denom h z := by
  rw [denom_cocycle_σ, σ_of_det_pos hpos]

theorem sqrt_div_normSq {a : ℝ} (w : ℂ) :
    Real.sqrt (a / Complex.normSq w) = Real.sqrt a / ‖w‖ := by
  rw [Real.sqrt_div' _ (Complex.normSq_nonneg w), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg w)]

theorem div_norm_zpow_neg (w : ℂ) : (w / (‖w‖ : ℂ)) ^ (-k) = w ^ (-k) * (‖w‖ : ℂ) ^ k := by
  rw [div_eq_mul_inv, mul_zpow, _root_.inv_zpow', neg_neg]

def archLift (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (Real.sqrt h.det.val : ℂ) ^ k * f (h • I) * denom h (I : ℂ) ^ (-k)

theorem apply_mapGL_smul {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma0 N) (z : ℍ) :
    f (Matrix.SpecialLinearGroup.mapGL ℝ s • z) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) (z : ℂ) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn'' (SlashInvariantForm.mk f hf) (Subgroup.mem_map_of_mem _ hs) z

theorem archLift_mapGL_mul {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma0 N) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    archLift k f (Matrix.SpecialLinearGroup.mapGL ℝ s * h) = archLift k f h := by
  have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ s * h).det.val = h.det.val := by
    rw [map_mul, Matrix.SpecialLinearGroup.det_mapGL, one_mul]
  have hne : denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • I : ℍ) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hA : denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • I : ℍ) : ℂ) ^ k *
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • I : ℍ) : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hne, add_neg_cancel, zpow_zero]
  rw [archLift, archLift, hdet, mul_smul, apply_mapGL_smul k hf hs, denom_mul_of_det_pos _ hpos,
    mul_zpow]
  linear_combination ((Real.sqrt h.det.val : ℂ) ^ k * f (h • I) * denom h (I : ℂ) ^ (-k)) * hA

theorem archLift_mul_kGL (f : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (w : ℂ)
    (hw : w ≠ 0) :
    archLift k f (h * kGL w hw) = (w / (‖w‖ : ℂ)) ^ (-k) * archLift k f h := by
  have hdet : (h * kGL w hw).det.val = h.det.val * Complex.normSq w := by
    rw [map_mul, Units.val_mul, det_kGL]
  have hsq : Real.sqrt (h.det.val * Complex.normSq w) = Real.sqrt h.det.val * ‖w‖ := by
    rw [Real.sqrt_mul hpos.le, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  rw [archLift, archLift, hdet, hsq, mul_smul, kGL_smul_I, denom_mul_of_det_pos _ (det_kGL_pos w hw),
    kGL_smul_I, denom_kGL, div_norm_zpow_neg, Complex.ofReal_mul, mul_zpow, mul_zpow]
  ring

theorem archLift_add (f f' : ℍ → ℂ) (h : GL (Fin 2) ℝ) :
    archLift k (f + f') h = archLift k f h + archLift k f' h := by
  simp only [archLift, Pi.add_apply]
  ring

theorem archLift_smul (c : ℂ) (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) :
    archLift k (c • f) h = c * archLift k f h := by
  simp only [archLift, Pi.smul_apply, smul_eq_mul]
  ring

theorem archLift_borelGL (f : ℍ → ℂ) (z : ℍ) :
    archLift k f (borelGL z) = (Real.sqrt z.im : ℂ) ^ k * f z := by
  rw [archLift, det_borelGL, borelGL_smul_I, denom_borelGL, _root_.one_zpow, mul_one]

variable (N) [NeZero N]

def decompGL (g : AdelicGL ℚ 2) : GL (Fin 2) ℝ :=
  Classical.choose (Classical.choose_spec (exists_decomposition N g))

theorem decompGL_spec (g : AdelicGL ℚ 2) :
    0 < (decompGL N g).det.val ∧ ∃ γ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N,
      g = diagonal ℚ 2 γ * realEmb (decompGL N g) * finEmb ℚ 2 u :=
  ⟨(Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).1,
    Classical.choose (exists_decomposition N g),
    (Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).2⟩

def adelicLift (f : ℍ → ℂ) (g : AdelicGL ℚ 2) : ℂ :=
  archLift k f (decompGL N g)

variable {N k}

theorem archLift_eq_of_decomp {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ₁ γ₂ : GL (Fin 2) ℚ} {h₁ h₂ : GL (Fin 2) ℝ} {u₁ u₂ : FiniteAdelicGL ℚ 2}
    (hpos₁ : 0 < h₁.det.val) (hpos₂ : 0 < h₂.det.val) (hu₁ : u₁ ∈ Gamma0Level N)
    (hu₂ : u₂ ∈ Gamma0Level N)
    (heq : diagonal ℚ 2 γ₁ * realEmb h₁ * finEmb ℚ 2 u₁ =
      diagonal ℚ 2 γ₂ * realEmb h₂ * finEmb ℚ 2 u₂) :
    archLift k f h₁ = archLift k f h₂ := by
  have hc := congrArg (prodEquiv ℚ 2) heq
  simp only [map_mul, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one,
    one_mul, Prod.mk.injEq] at hc
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = γ₂⁻¹ * γ₁ := ⟨_, rfl⟩
  have hreal : toReal δ * h₁ = h₂ := realInf_injective (by
    simp only [hδdef, map_mul, map_inv, mul_assoc, hc.1, inv_mul_cancel_left])
  have hfin : finiteDiagonal ℚ 2 δ = u₂ * u₁⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    simp only [hδdef, map_mul, map_inv, mul_assoc, hc.2, inv_mul_cancel_left]
  have hδ : finiteDiagonal ℚ 2 δ ∈ Gamma0Level N := hfin ▸ mul_mem hu₂ (inv_mem hu₁)
  have hdetδ : 0 < (δ.det.val : ℚ) := by
    have hprod : (toReal δ).det.val * h₁.det.val = h₂.det.val := by
      rw [← hreal, MonoidHom.map_mul Matrix.GeneralLinearGroup.det, Units.val_mul]
    rw [det_toReal] at hprod
    have hb : 0 < ((δ.det.val : ℚ) : ℝ) * h₁.det.val := hprod ▸ hpos₂
    have : (0 : ℝ) < ((δ.det.val : ℚ) : ℝ) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    exact_mod_cast this
  obtain ⟨s, hs, hsδ⟩ := exists_mem_Gamma0_of_mem N hδ hdetδ
  rw [← hreal, ← hsδ, toReal_mapGL]
  exact (archLift_mapGL_mul k hf hs hpos₁).symm

theorem adelicLift_apply {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (γ : GL (Fin 2) ℚ)
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) :
    adelicLift N k f (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u) = archLift k f h := by
  obtain ⟨hpos', γ', u', hu', heq⟩ := decompGL_spec N (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u)
  exact archLift_eq_of_decomp hf hpos' hpos hu' hu heq.symm

theorem adelicLift_realEmb {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    adelicLift N k f (realEmb h) = archLift k f h := by
  have := adelicLift_apply hf 1 hpos (one_mem (Gamma0Level N))
  rwa [map_one, map_one, one_mul, mul_one] at this

theorem adelicLift_borelGL {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (z : ℍ) :
    adelicLift N k f (realEmb (borelGL z)) = (Real.sqrt z.im : ℂ) ^ k * f z := by
  rw [adelicLift_realEmb hf (det_borelGL_pos z), archLift_borelGL]

variable (N k)

structure IsWeightLevel (φ : AdelicGL ℚ 2 → ℂ) : Prop where
  isLeftInvariant : IsLeftInvariant φ
  right_level : ∀ g, ∀ u ∈ Gamma0Level N, φ (g * finEmb ℚ 2 u) = φ g
  right_kGL : ∀ g (w : ℂ) (hw : w ≠ 0), φ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * φ g

def weightLevelSpace : Submodule ℂ (AdelicGL ℚ 2 → ℂ) where
  carrier := {φ | IsWeightLevel N k φ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' {φ ψ} hφ hψ := ⟨hφ.isLeftInvariant.add hψ.isLeftInvariant,
    fun g u hu => by simp [hφ.right_level g u hu, hψ.right_level g u hu],
    fun g w hw => by simp [hφ.right_kGL g w hw, hψ.right_kGL g w hw, mul_add]⟩
  smul_mem' c φ hφ := ⟨hφ.isLeftInvariant.smul c,
    fun g u hu => by simp [hφ.right_level g u hu],
    fun g w hw => by simp [hφ.right_kGL g w hw]; ring⟩

variable {N k}

theorem IsWeightLevel.apply_decomp {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) :
    φ (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u) = φ (realEmb h) := by
  rw [hφ.right_level _ u hu]
  exact hφ.isLeftInvariant γ _

theorem IsWeightLevel.apply_realEmb {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    φ (realEmb h) = (denom h (I : ℂ) / (‖denom h (I : ℂ)‖ : ℂ)) ^ (-k) *
      φ (realEmb (borelGL (h • I))) := by
  conv_lhs => rw [eq_borelGL_mul_kGL hpos, map_mul]
  exact hφ.right_kGL _ _ _

theorem isWeightLevel_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    IsWeightLevel N k (adelicLift N k f) where
  isLeftInvariant δ g := by
    obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
    conv_lhs => rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul]
    rw [adelicLift_apply hf _ hpos hu]
    rfl
  right_level g v hv := by
    obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
    conv_lhs => rw [hg, mul_assoc, ← map_mul]
    rw [adelicLift_apply hf _ hpos (mul_mem hu hv)]
    rfl
  right_kGL g w hw := by
    obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
    have key : ∀ h : GL (Fin 2) ℝ, g = diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u →
        g * realEmb (kGL w hw) = diagonal ℚ 2 γ * realEmb (h * kGL w hw) * finEmb ℚ 2 u := by
      intro h hgh
      rw [hgh, map_mul, mul_assoc _ (finEmb ℚ 2 u), ← realEmb_mul_finEmb_comm, ← mul_assoc,
        mul_assoc (diagonal ℚ 2 γ)]
    have := key _ hg
    have hpos' : 0 < (decompGL N g * kGL w hw).det.val := by
      rw [map_mul, Units.val_mul]
      exact mul_pos hpos (det_kGL_pos w hw)
    rw [this, adelicLift_apply hf _ hpos' hu, archLift_mul_kGL k f hpos]
    rfl

variable (k)

def descend (φ : AdelicGL ℚ 2 → ℂ) (z : ℍ) : ℂ :=
  (Real.sqrt z.im : ℂ) ^ (-k) * φ (realEmb (borelGL z))

variable {k}

theorem descend_slash {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma0 N) : descend k φ ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s = descend k φ := by
  funext z
  set g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg1 : g.det.val = 1 := by rw [Matrix.SpecialLinearGroup.det_mapGL]; rfl
  have hgpos : 0 < g.det.val := by rw [hg1]; exact one_pos
  set j := denom g z
  have hj : j ≠ 0 := denom_ne_zero g z

  have hA : φ (realEmb (g * borelGL z)) = φ (realEmb (borelGL z)) := by
    have h1 := hφ.isLeftInvariant (Matrix.SpecialLinearGroup.mapGL ℚ s) (realEmb (borelGL z))
    rw [diagonal_eq, toReal_mapGL, mul_assoc, ← realEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul,
      hφ.right_level _ _ (finiteDiagonal_mapGL_mem_Gamma0Level N hs)] at h1
    exact h1

  have hpos : 0 < (g * borelGL z).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hgpos (det_borelGL_pos z)
  have hsmul : (g * borelGL z) • I = g • z := by rw [mul_smul, borelGL_smul_I]
  have hden : denom (g * borelGL z) (I : ℂ) = j := by
    rw [denom_mul_of_det_pos _ (det_borelGL_pos z), borelGL_smul_I, denom_borelGL, mul_one]
  have hB : φ (realEmb (borelGL z)) =
      (j / (‖j‖ : ℂ)) ^ (-k) * φ (realEmb (borelGL (g • z))) := by
    rw [← hA, hφ.apply_realEmb hpos, hsmul, hden]
  have him : (g • z).im = z.im / Complex.normSq j := by
    rw [im_smul_eq_div_normSq, hg1, abs_one, one_mul]
  have hn : (‖j‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hj)
  have hnk : (‖j‖ : ℂ) ^ (-k) * (‖j‖ : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hn, neg_add_cancel, zpow_zero]
  rw [slash_apply, σ_of_det_pos hgpos, hg1, abs_one, Complex.ofReal_one, _root_.one_zpow, mul_one,
    descend, descend, him,
    sqrt_div_normSq, Complex.ofReal_div, div_zpow, hB, div_norm_zpow_neg, div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right hnk]
  ring

theorem descend_slash_eq {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) :
    ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), descend k φ ∣[k] γ = descend k φ := by
  intro γ hγ
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hγ
  exact descend_slash hφ hs

theorem descend_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    descend k (adelicLift N k f) = f := by
  funext z
  have hy : (Real.sqrt z.im : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 z.im_pos).ne'
  rw [descend, adelicLift_borelGL hf, ← mul_assoc, ← zpow_add₀ hy, neg_add_cancel, zpow_zero,
    one_mul]

theorem adelicLift_descend {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) :
    adelicLift N k (descend k φ) = φ := by
  funext g
  obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
  set h := decompGL N g
  set j := denom h (I : ℂ)
  have hj : j ≠ 0 := denom_ne_zero h I
  have hn : (‖j‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hj)
  have hnk : (‖j‖ : ℂ) ^ (-k) * (‖j‖ : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hn, neg_add_cancel, zpow_zero]
  have hd : (Real.sqrt h.det.val : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hdk : (Real.sqrt h.det.val : ℂ) ^ k * (Real.sqrt h.det.val : ℂ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hd, add_neg_cancel, zpow_zero]
  have hφg : φ g = φ (realEmb h) := by
    conv_lhs => rw [hg]
    exact hφ.apply_decomp γ h hu
  change archLift k (descend k φ) h = φ g
  rw [hφg, hφ.apply_realEmb hpos, archLift, descend, im_smul_I hpos, sqrt_div_normSq,
    Complex.ofReal_div, div_zpow, div_norm_zpow_neg, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hnk]
  linear_combination ((‖j‖ : ℂ) ^ k * φ (realEmb (borelGL (h • I))) * j ^ (-k)) * hdk

variable (N k)

def liftEquiv :
    SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k ≃ₗ[ℂ] weightLevelSpace N k where
  toFun f := ⟨adelicLift N k f,
    isWeightLevel_adelicLift fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ⟩
  map_add' f f' := by
    ext g
    simp only [Submodule.coe_add, Pi.add_apply, adelicLift, FunLike.coe_add]
    exact archLift_add k f f' _
  map_smul' c f := by
    ext g
    simp only [Submodule.coe_smul, Pi.smul_apply, adelicLift, FunLike.coe_smul,
      RingHom.id_apply, smul_eq_mul]
    exact archLift_smul k c f _
  invFun φ := SlashInvariantForm.mk (descend k φ) (descend_slash_eq φ.2)
  left_inv f := SlashInvariantForm.ext fun z => congrFun
    (descend_adelicLift fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ) z
  right_inv φ := Subtype.ext (adelicLift_descend φ.2)

variable {N k}

@[simp]
theorem liftEquiv_apply (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) = adelicLift N k f :=
  rfl

@[simp]
theorem liftEquiv_symm_apply (φ : weightLevelSpace N k) (z : ℍ) :
    (liftEquiv N k).symm φ z = descend k φ z :=
  rfl

end GL2Classical

end

end GroundTheory.Automorphic
end
