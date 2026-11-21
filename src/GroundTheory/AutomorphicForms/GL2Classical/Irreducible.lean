import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslates

section
open Complex

namespace GroundTheory.Automorphic

namespace GL2Classical

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {Rr Ll Jj : Module.End ℂ E}

theorem J_pow_apply (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) {κ : ℂ} {t : E} (ht : Jj t = κ • t) (j : ℕ) :
    Jj ((Rr ^ j) t) = (κ + 2 * I * j) • (Rr ^ j) t := by
  induction j with
  | zero => simpa using ht
  | succ j ih =>
    have h1 : Jj (Rr ((Rr ^ j) t)) = Rr (Jj ((Rr ^ j) t)) + (2 * I) • Rr ((Rr ^ j) t) := by
      have := congrArg (fun F : Module.End ℂ E => F ((Rr ^ j) t)) hJR
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      rw [← this]
      abel
    rw [pow_succ', Module.End.mul_apply, h1, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem L_pow_succ_apply (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) (hLR : Ll * Rr - Rr * Ll = (4 * I) • Jj)
    {κ : ℂ} {t : E} (ht : Jj t = κ • t) (hL : Ll t = 0) (j : ℕ) :
    Ll ((Rr ^ (j + 1)) t) = (4 * I * (j + 1) * (κ + I * j)) • (Rr ^ j) t := by
  have hcomm : ∀ v, Ll (Rr v) = Rr (Ll v) + (4 * I) • Jj v := by
    intro v
    have := congrArg (fun F : Module.End ℂ E => F v) hLR
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [← this]
    abel
  induction j with
  | zero =>
    rw [pow_one, hcomm, hL, map_zero, zero_add, ht, smul_smul, pow_zero, Module.End.one_apply]
    congr 1
    push_cast
    ring
  | succ j ih =>
    rw [pow_succ' Rr (j + 1), Module.End.mul_apply, hcomm, ih, map_smul, J_pow_apply hJR ht, smul_smul]
    have e : Rr ((Rr ^ j) t) = (Rr ^ (j + 1)) t := by rw [pow_succ', Module.End.mul_apply]
    rw [e, ← add_smul]
    congr 1
    push_cast
    ring

theorem L_pow_R_pow_apply (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) (hLR : Ll * Rr - Rr * Ll = (4 * I) • Jj)
    {κ : ℂ} {t : E} (ht : Jj t = κ • t) (hL : Ll t = 0) (j : ℕ) :
    (Ll ^ j) ((Rr ^ j) t) = (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (κ + I * m))) • t := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ Ll j, Module.End.mul_apply, L_pow_succ_apply hJR hLR ht hL, map_smul, ih, smul_smul,
      Finset.prod_range_succ, mul_comm]

theorem prod_ne_zero_of_pos {k : ℤ} (hk : 0 < k) (j : ℕ) :
    (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro m _
  have h1 : (4 * I * (m + 1) : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
    (by exact_mod_cast Nat.succ_ne_zero m)
  have h2 : (I * k + I * m : ℂ) ≠ 0 := by
    rw [← mul_add]
    refine mul_ne_zero I_ne_zero ?_
    have : (0 : ℝ) < (k : ℝ) + m := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact mul_ne_zero h1 h2

theorem mem_of_sum_mem_of_eigen {W : Submodule ℂ E} (hW : ∀ v ∈ W, Jj v ∈ W) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) : ∀ (v : ι → E) (μ : ι → ℂ), (∀ i ∈ s, Jj (v i) = μ i • v i) → Set.InjOn μ s →
      ∑ i ∈ s, v i ∈ W → ∀ i ∈ s, v i ∈ W := by
  induction s using Finset.induction_on with
  | empty => intro v μ _ _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro v μ hv hμ hsum
    rw [Finset.sum_insert ha] at hsum

    have hJs : ∑ i ∈ s, (μ i - μ a) • v i ∈ W := by
      have h1 : Jj (v a + ∑ i ∈ s, v i) - μ a • (v a + ∑ i ∈ s, v i) ∈ W :=
        sub_mem (hW _ hsum) (Submodule.smul_mem _ _ hsum)
      have e : Jj (v a + ∑ i ∈ s, v i) - μ a • (v a + ∑ i ∈ s, v i) = ∑ i ∈ s, (μ i - μ a) • v i := by
        rw [map_add, map_sum, hv a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum]
        rw [Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem hi)]
        simp only [sub_smul, Finset.sum_sub_distrib]
        abel
      rwa [e] at h1
    have hs' := ih (fun i => (μ i - μ a) • v i) μ
      (fun i hi => by rw [map_smul, hv i (Finset.mem_insert_of_mem hi), smul_comm])
      (hμ.mono (Finset.coe_subset.2 (Finset.subset_insert a s))) hJs
    have hvs : ∀ i ∈ s, v i ∈ W := by
      intro i hi
      have hne : μ i - μ a ≠ 0 := sub_ne_zero.2 fun h =>
        ha (hμ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) h ▸ hi)
      have := Submodule.smul_mem W (μ i - μ a)⁻¹ (hs' i hi)
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · have := sub_mem hsum (Submodule.sum_mem W hvs)
      rwa [add_sub_cancel_right] at this
    · exact hvs i hi

end GL2Classical

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

def raiseMat : Matrix (Fin 2) (Fin 2) ℂ := !![-I, 1; 1, I]

def lowerMat : Matrix (Fin 2) (Fin 2) ℂ := !![I, 1; 1, -I]

def rotMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem rot_raise : rotMat * raiseMat - raiseMat * rotMat = (2 * I) • raiseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, raiseMat] <;> ring_nf <;> simp only [I_sq] <;> ring

theorem rot_lower : rotMat * lowerMat - lowerMat * rotMat = (-2 * I) • lowerMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, lowerMat] <;> ring_nf <;> simp only [I_sq] <;> ring

theorem lower_raise : lowerMat * raiseMat - raiseMat * lowerMat = (4 * I) • rotMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, lowerMat, raiseMat] <;> ring_nf

def cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ (cuspForms ℚ 2) :=
  (gkModuleCusp ℚ 2).ρ (lieOfRealMat (reMat B)) + I • (gkModuleCusp ℚ 2).ρ (lieOfRealMat (imMat B))

def cuspToArch (ψ : cuspForms ℚ 2) : archSmooth ℚ 2 :=
  ⟨ψ, ψ.2.1.isSmooth.1⟩

theorem coe_cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : cuspForms ℚ 2) :
    ((cuspOp B ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) = (complexOpGL2 B (cuspToArch ψ) : AdelicGL ℚ 2 → ℂ) :=
  rfl

theorem cuspToArch_cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) (ψ : cuspForms ℚ 2) :
    cuspToArch (cuspOp B ψ) = complexOpGL2 B (cuspToArch ψ) :=
  Subtype.ext (coe_cuspOp B ψ)

theorem cuspToArch_injective : Function.Injective cuspToArch := fun a b h =>
  Subtype.ext (by have := congrArg Subtype.val h; exact this)

theorem cuspOp_add (B C : Matrix (Fin 2) (Fin 2) ℂ) : cuspOp (B + C) = cuspOp B + cuspOp C := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [LinearMap.add_apply, cuspToArch_cuspOp, complexOpGL2_add]
  apply Subtype.ext
  rfl

theorem cuspOp_smul (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : cuspOp (c • B) = c • cuspOp B := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [LinearMap.smul_apply, cuspToArch_cuspOp, complexOpGL2_smul]
  apply Subtype.ext
  rfl

theorem cuspOp_lie (B C : Matrix (Fin 2) (Fin 2) ℂ) :
    cuspOp (B * C - C * B) = cuspOp B * cuspOp C - cuspOp C * cuspOp B := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [cuspToArch_cuspOp, complexOpGL2_lie, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  apply Subtype.ext
  change _ = ((complexOpGL2 B (cuspToArch (cuspOp C ψ)) - complexOpGL2 C (cuspToArch (cuspOp B ψ)) :
    archSmooth ℚ 2) : AdelicGL ℚ 2 → ℂ)
  rw [cuspToArch_cuspOp, cuspToArch_cuspOp]

theorem gkModuleCusp_ρ_eq_cuspOp (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) :
    (gkModuleCusp ℚ 2).ρ X = cuspOp ((lieRealMat X).map (↑)) := by
  ext ψ : 1
  apply cuspToArch_injective
  rw [cuspToArch_cuspOp, complexOpGL2_map_ofReal, realOpGL2, lieOfRealMat_lieRealMat]
  rfl

theorem cuspOp_finRepCusp (B : Matrix (Fin 2) (Fin 2) ℂ) (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) :
    cuspOp B (finRepCusp ℚ 2 g ψ) = finRepCusp ℚ 2 g (cuspOp B ψ) := by
  simp only [cuspOp, LinearMap.add_apply, LinearMap.smul_apply, gkModuleCusp_ρ_finRepCusp, map_add, map_smul]

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem cuspOp_liftCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {B : Matrix (Fin 2) (Fin 2) ℂ}
    (hB : gl2HolCoeff B = 0) : cuspOp B (liftCusp f) = gl2WeightChar k B • liftCusp f := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn f.toSlashInvariantForm γ hγ
  apply cuspToArch_injective
  rw [cuspToArch_cuspOp]
  have e : cuspToArch (liftCusp f) = ⟨adelicLift N k f, isArchSmooth_adelicLift hf f.holo'⟩ := rfl
  rw [e, ← gl2ArchRep_ι, gl2ArchRep_ι_adelicLift_of_holCoeff hf f.holo' hB]
  rfl

theorem cuspOp_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : gl2HolCoeff B = 0) {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) :
    cuspOp B t = gl2WeightChar k B • t := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [cuspOp_finRepCusp, cuspOp_liftCusp f hB, map_smul]
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

theorem holCoeff_lowerMat : gl2HolCoeff lowerMat = 0 := by
  simp [gl2HolCoeff, lowerMat]; ring_nf; simp [I_sq]

theorem holCoeff_rotMat : gl2HolCoeff rotMat = 0 := by
  simp [gl2HolCoeff, rotMat]

theorem holCoeff_one : gl2HolCoeff (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [gl2HolCoeff]

theorem weightChar_lowerMat : gl2WeightChar k lowerMat = 0 := by
  simp [gl2WeightChar, lowerMat]

theorem weightChar_rotMat : gl2WeightChar k rotMat = I * k := by
  simp [gl2WeightChar, rotMat]
  ring

theorem weightChar_one : gl2WeightChar k (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [gl2WeightChar]
  ring

abbrev kMat (x : archCompact ℚ 2) : GL (Fin 2) ℝ := archToReal (x : archGroup ℚ 2)

theorem realPart_realEmb (h : GL (Fin 2) ℝ) : realPart (realEmb h) = h := by
  apply realInf_injective
  rw [realInf_realPart, prodEquiv_realEmb]

theorem exists_kGL_of_mem_archCompact (x : archCompact ℚ 2) :
    ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ (kMat x = kGL w hw ∨ kMat x = toReal epsilon * kGL w hw) := by
  have hx : infEmb ℚ 2 (x : archGroup ℚ 2) ∈ Reduction.maxCompact := x.2
  rw [infEmb_eq_realEmb] at hx
  obtain ⟨h1, h2, h3⟩ := realPart_orthogonal hx
  rw [realPart_realEmb] at h1 h2 h3
  exact exists_eq_kGL_of_orthogonal _ h1 h2 h3

theorem archCompactRepCusp_apply_coe (x : archCompact ℚ 2) (ψ : cuspForms ℚ 2) (g : AdelicGL ℚ 2) :
    ((archCompactRepCusp ℚ 2 x ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) g =
      (ψ : AdelicGL ℚ 2 → ℂ) (g * realEmb (kMat x)) := by
  change (ψ : AdelicGL ℚ 2 → ℂ) (g * infEmb ℚ 2 (x : archGroup ℚ 2)) = _
  rw [infEmb_eq_realEmb]

theorem archCompactRepCusp_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (x : archCompact ℚ 2) {w : ℂ} (hw : w ≠ 0) (h1 : ‖w‖ = 1) (hK : kMat x = kGL w hw)
    {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : archCompactRepCusp ℚ 2 x t = w ^ (-k) • t := by
  apply Subtype.ext
  funext g
  rw [archCompactRepCusp_apply_coe, hK, right_kGL_of_mem_translateSpan (liftEquiv N k f.toSlashInvariantForm).2.right_kGL
    (coe_mem_translateSpan f ht), h1]
  simp

theorem archRealEquiv_coe (g : archGroup ℚ 2) :
    archRealEquiv ((g : (ArchMatrix ℚ 2)ˣ) : ArchMatrix ℚ 2) = (archToReal g : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rfl

theorem archToReal_inv (g : archGroup ℚ 2) : archToReal g⁻¹ = (archToReal g)⁻¹ := by
  simp [archToReal, map_inv]

theorem archCompactRepCusp_rho (x : archCompact ℚ 2) (A : Matrix (Fin 2) (Fin 2) ℝ) (ψ : cuspForms ℚ 2) :
    archCompactRepCusp ℚ 2 x ((gkModuleCusp ℚ 2).ρ (lieOfRealMat A) ψ) =
      (gkModuleCusp ℚ 2).ρ (lieOfRealMat ((kMat x : Matrix (Fin 2) (Fin 2) ℝ) * A *
        ((kMat x)⁻¹ : GL (Fin 2) ℝ))) (archCompactRepCusp ℚ 2 x ψ) := by
  have key := (gkModuleCusp ℚ 2).map_ρ x ⟨archRealEquiv.symm A, Submodule.mem_top⟩ ψ
  have e1 : (isExpLieAlgebra ℚ 2).toLie ⟨archRealEquiv.symm A, Submodule.mem_top⟩ = lieOfRealMat A := rfl
  have e2 : (isExpLieAlgebra ℚ 2).toLie ((isExpLieAlgebra ℚ 2).Ad (x : archGroup ℚ 2)
      ⟨archRealEquiv.symm A, Submodule.mem_top⟩) =
      lieOfRealMat ((kMat x : Matrix (Fin 2) (Fin 2) ℝ) * A * ((kMat x)⁻¹ : GL (Fin 2) ℝ)) := by
    apply Subtype.ext
    change (((x : archGroup ℚ 2) : (ArchMatrix ℚ 2)ˣ) : ArchMatrix ℚ 2) * archRealEquiv.symm A *
      ((((x : archGroup ℚ 2)⁻¹ : archGroup ℚ 2) : (ArchMatrix ℚ 2)ˣ) : ArchMatrix ℚ 2) =
        archRealEquiv.symm _
    apply archRealEquiv.injective
    rw [RingEquiv.apply_symm_apply, map_mul, map_mul, RingEquiv.apply_symm_apply, archRealEquiv_coe,
      archRealEquiv_coe, archToReal_inv]
  rw [e1, e2] at key
  exact key

theorem reMat_conj (K : GL (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    reMat ((K : Matrix (Fin 2) (Fin 2) ℝ).map (↑) * B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑)) =
      (K : Matrix (Fin 2) (Fin 2) ℝ) * reMat B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp [reMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem imMat_conj (K : GL (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    imMat ((K : Matrix (Fin 2) (Fin 2) ℝ).map (↑) * B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑)) =
      (K : Matrix (Fin 2) (Fin 2) ℝ) * imMat B * ((K⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp [imMat, Matrix.mul_apply, Fin.sum_univ_two]

abbrev kMatC (x : archCompact ℚ 2) : Matrix (Fin 2) (Fin 2) ℂ := (kMat x : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

theorem archCompactRepCusp_cuspOp (x : archCompact ℚ 2) {B B' : Matrix (Fin 2) (Fin 2) ℂ}
    (h : kMatC x * B = B' * kMatC x) (ψ : cuspForms ℚ 2) :
    archCompactRepCusp ℚ 2 x (cuspOp B ψ) = cuspOp B' (archCompactRepCusp ℚ 2 x ψ) := by
  have hKK : (kMat x : Matrix (Fin 2) (Fin 2) ℝ) * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKi : kMatC x * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑) = 1 := by
    rw [kMatC, show ((kMat x : Matrix (Fin 2) (Fin 2) ℝ).map ((↑) : ℝ → ℂ)) *
        (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑) =
        ((kMat x : Matrix (Fin 2) (Fin 2) ℝ) * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).map
          Complex.ofRealHom from (Matrix.map_mul (f := Complex.ofRealHom)).symm, hKK]
    ext i j
    simp [Matrix.one_apply]
  have hB' : B' = kMatC x * B * (((kMat x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (↑) := by
    rw [h, Matrix.mul_assoc, hKi, Matrix.mul_one]
  rw [hB']
  simp only [cuspOp, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, archCompactRepCusp_rho]
  rw [kMatC, reMat_conj, imMat_conj]

abbrev kgc (w : ℂ) (hw : w ≠ 0) : Matrix (Fin 2) (Fin 2) ℂ := (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

abbrev epsC : Matrix (Fin 2) (Fin 2) ℂ := (toReal epsilon : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

theorem kgc_lowerMat (w : ℂ) (hw : w ≠ 0) : kgc w hw * lowerMat = w • lowerMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, lowerMat, Matrix.mul_apply, Complex.ext_iff]

theorem lowerMat_kgc (w : ℂ) (hw : w ≠ 0) : lowerMat * kgc w hw = (starRingEnd ℂ w) • lowerMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, lowerMat, Matrix.mul_apply, Complex.ext_iff]

theorem kgc_raiseMat (w : ℂ) (hw : w ≠ 0) : kgc w hw * raiseMat = (starRingEnd ℂ w) • raiseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, raiseMat, Matrix.mul_apply, Complex.ext_iff]

theorem raiseMat_kgc (w : ℂ) (hw : w ≠ 0) : raiseMat * kgc w hw = w • raiseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, raiseMat, Matrix.mul_apply, Complex.ext_iff]

theorem kgc_rotMat (w : ℂ) (hw : w ≠ 0) : kgc w hw * rotMat = rotMat * kgc w hw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgc, coe_kGL, rotMat, Matrix.mul_apply]

theorem epsC_lowerMat : epsC * lowerMat = -(raiseMat * epsC) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsC, coe_toReal_epsilon, lowerMat, raiseMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

theorem epsC_raiseMat : epsC * raiseMat = -(lowerMat * epsC) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsC, coe_toReal_epsilon, lowerMat, raiseMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

theorem epsC_rotMat : epsC * rotMat = -(rotMat * epsC) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsC, coe_toReal_epsilon, rotMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

theorem conj_ne_zero' {w : ℂ} (hw : w ≠ 0) : starRingEnd ℂ w ≠ 0 := (map_ne_zero _).2 hw

theorem plus_lowerMat (w : ℂ) (hw : w ≠ 0) :
    kgc w hw * lowerMat = ((w / starRingEnd ℂ w) • lowerMat) * kgc w hw := by
  rw [Matrix.smul_mul, lowerMat_kgc, smul_smul, div_mul_cancel₀ _ (conj_ne_zero' hw), kgc_lowerMat]

theorem plus_raiseMat (w : ℂ) (hw : w ≠ 0) :
    kgc w hw * raiseMat = ((starRingEnd ℂ w / w) • raiseMat) * kgc w hw := by
  rw [Matrix.smul_mul, raiseMat_kgc, smul_smul, div_mul_cancel₀ _ hw, kgc_raiseMat]

theorem minus_lowerMat (w : ℂ) (hw : w ≠ 0) :
    epsC * kgc w hw * lowerMat = ((-(w / starRingEnd ℂ w)) • raiseMat) * (epsC * kgc w hw) := by
  have hRe : raiseMat * epsC = -(epsC * lowerMat) := by rw [epsC_lowerMat, neg_neg]
  rw [Matrix.mul_assoc, kgc_lowerMat, Matrix.mul_smul, epsC_lowerMat, Matrix.smul_mul, ← Matrix.mul_assoc, hRe,
    Matrix.neg_mul, Matrix.mul_assoc, lowerMat_kgc, Matrix.mul_smul, epsC_lowerMat]
  simp only [smul_neg, neg_neg, smul_smul]
  rw [neg_mul, div_mul_cancel₀ _ (conj_ne_zero' hw)]
  exact (_root_.neg_smul w _).symm

theorem minus_raiseMat (w : ℂ) (hw : w ≠ 0) :
    epsC * kgc w hw * raiseMat = ((-(starRingEnd ℂ w / w)) • lowerMat) * (epsC * kgc w hw) := by
  have hLe : lowerMat * epsC = -(epsC * raiseMat) := by rw [epsC_raiseMat, neg_neg]
  rw [Matrix.mul_assoc, kgc_raiseMat, Matrix.mul_smul, epsC_raiseMat, Matrix.smul_mul, ← Matrix.mul_assoc, hLe,
    Matrix.neg_mul, Matrix.mul_assoc, raiseMat_kgc, Matrix.mul_smul, epsC_raiseMat]
  simp only [smul_neg, neg_neg, smul_smul]
  rw [neg_mul, div_mul_cancel₀ _ hw]
  exact (_root_.neg_smul _ _).symm

theorem minus_rotMat (w : ℂ) (hw : w ≠ 0) :
    epsC * kgc w hw * rotMat = ((-1 : ℂ) • rotMat) * (epsC * kgc w hw) := by
  rw [Matrix.mul_assoc, kgc_rotMat, ← Matrix.mul_assoc, epsC_rotMat, neg_one_smul, Matrix.neg_mul,
    Matrix.neg_mul, Matrix.mul_assoc]

theorem kMatC_of_plus {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = kGL w hw) :
    kMatC x = kgc w hw := by
  rw [kMatC, hK]

theorem kMatC_of_minus {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw) :
    kMatC x = epsC * kgc w hw := by
  rw [kMatC, hK, Units.val_mul]
  exact Matrix.map_mul (f := Complex.ofRealHom)

theorem archCompactRepCusp_cuspOp_one (x : archCompact ℚ 2) (ψ : cuspForms ℚ 2) :
    archCompactRepCusp ℚ 2 x (cuspOp 1 ψ) = cuspOp 1 (archCompactRepCusp ℚ 2 x ψ) :=
  archCompactRepCusp_cuspOp x (by rw [Matrix.mul_one, Matrix.one_mul]) ψ

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter MeasureTheory
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm CuspidalSpectrum

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem finite_range_of_isOpen_stabilizer {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) {v : V}
    (hv : IsOpen (stabilizerOf ρ v : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    (Set.range fun k : K => ρ k v).Finite := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : G => (fun x => c⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G))
    (fun c => hv.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, show x⁻¹ * x ∈ (stabilizerOf ρ v : Set G) by
      rw [inv_mul_cancel]; exact one_mem _⟩)
  refine ((t.finite_toSet).image fun c => ρ c v).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨c, hc, hck⟩ := Set.mem_iUnion₂.1 (ht k.2)
  refine ⟨c, hc, ?_⟩
  have h1 : ρ (c⁻¹ * k) v = v := hck
  change ρ c v = ρ k v
  conv_lhs => rw [← h1]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem translateSpanCusp_le_smoothVectors (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    translateSpanCusp f ≤ smoothVectors (finRepCusp ℚ 2) := by
  rw [translateSpanCusp, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  refine smooth_apply_mem _ ?_ g
  refine Subgroup.isOpen_mono (H₁ := Gamma0Level N) (fun u hu => ?_) (isOpen_Gamma0Level N)
  rw [mem_stabilizerOf]
  refine Subtype.ext (funext fun x => ?_)
  exact (liftEquiv N k f.toSlashInvariantForm).2.right_level x u hu

theorem coe_finRepCusp_apply (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) (x : AdelicGL ℚ 2) :
    ((finRepCusp ℚ 2 g ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) x = (ψ : AdelicGL ℚ 2 → ℂ) (x * finEmb ℚ 2 g) :=
  rfl

theorem coe_rightTranslate_apply (y : AdelicGL ℚ 2) (ψ : AdelicGL ℚ 2 → ℂ) (x : AdelicGL ℚ 2) :
    Automorphic.rightTranslate y ψ x = ψ (x * y) :=
  rfl

variable (μ : Measure (Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure]

theorem cuspToL2_finRepCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (g : FiniteAdelicGL ℚ 2) :
    ∃ y : Reduction.normOneGL ℚ 2, ∀ ψ ∈ translateSpanCusp f,
      cuspToL2 μ (finRepCusp ℚ 2 g ψ) = cuspRep μ y (cuspToL2 μ ψ) := by
  have hex : ∃ (s : {r : ℝ // 0 < r}) (y : AdelicGL ℚ 2), y ∈ Reduction.normOneGL ℚ 2 ∧
      AutomorphicForm.finEmb ℚ 2 g = Reduction.centralSection ℚ 2 s * y :=
    CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL _
  obtain ⟨s, y, hy, hxy⟩ := hex
  refine ⟨⟨y, hy⟩, fun ψ hψ => ?_⟩
  refine cuspToL2_rightTranslate μ ⟨y, hy⟩ ψ (finRepCusp ℚ 2 g ψ) ?_
  funext x
  rw [coe_finRepCusp_apply, coe_rightTranslate_apply]
  change (ψ : AdelicGL ℚ 2 → ℂ) (x * finEmb ℚ 2 g) = (ψ : AdelicGL ℚ 2 → ℂ) (x * y)
  rw [hxy, ← mul_assoc, ← Reduction.centralSection_mul_comm, mul_assoc,
    centralSection_of_mem_translateSpanCusp f hψ]

theorem eq_zero_of_cuspFormLp_eq_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {v : cuspForms ℚ 2} (hv : v ∈ translateSpanCusp f) (h0 : cuspToL2 μ v = 0) : v = 0 :=
  injOn_cuspToL2 μ (fun s x => centralSection_of_mem_translateSpanCusp f hv s x)
    (fun _ _ => rfl) (h0.trans (map_zero _).symm)

variable (k) in

def descendL : cuspForms ℚ 2 →ₗ[ℂ] (ℍ → ℂ) where
  toFun ψ := descend k ψ
  map_add' ψ ψ' := by funext z; simp [descend, mul_add]
  map_smul' c ψ := by funext z; simp [descend]; ring

def cuspFormCoeL : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun F := F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finRightRep_eq_of_mem_invariants {ψ : cuspForms ℚ 2}
    (hψ : ψ ∈ Representation.invariants ((finRepCusp ℚ 2).comp (Gamma0Level N).subtype)) :
    ∀ u ∈ Gamma0Level N, finRightRep u (ψ : AdelicGL ℚ 2 → ℂ) = ψ := fun u hu =>
  congrArg Subtype.val (hψ ⟨u, hu⟩)

theorem finiteDimensional_translateSpanCusp_fixed (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    FiniteDimensional ℂ ↥(translateSpanCusp f ⊓
      Representation.invariants ((finRepCusp ℚ 2).comp (Gamma0Level N).subtype)) := by
  set M := translateSpanCusp f ⊓ Representation.invariants ((finRepCusp ℚ 2).comp (Gamma0Level N).subtype)
  have hmem : ∀ ψ ∈ M, descendL k ψ ∈ LinearMap.range (cuspFormCoeL (N := N) (k := k)) := by
    intro ψ hψ
    obtain ⟨F, hF⟩ := exists_cuspForm_of_mem_translateSpan f (coe_mem_translateSpan f hψ.1)
      (finRightRep_eq_of_mem_invariants hψ.2)
    refine ⟨F, ?_⟩
    change (F : ℍ → ℂ) = descend k ψ
    rw [← hF, liftEquiv_apply,
      descend_adelicLift (fun γ hγ => SlashInvariantForm.slash_action_eqn F.toSlashInvariantForm γ hγ)]
    rfl
  let Φ : M →ₗ[ℂ] LinearMap.range (cuspFormCoeL (N := N) (k := k)) :=
    (descendL k ∘ₗ M.subtype).codRestrict _ (fun ψ => hmem ψ ψ.2)
  have hinj : Function.Injective Φ := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 (fun (ψ : M) (hψ : Φ ψ = 0) => ?_))
    have h0 : descend k (ψ : AdelicGL ℚ 2 → ℂ) = 0 := congrArg Subtype.val hψ
    have hW : IsWeightLevel N k (ψ : AdelicGL ℚ 2 → ℂ) :=
      isWeightLevel_of_mem_translateSpan f.toSlashInvariantForm (coe_mem_translateSpan f ψ.2.1)
        (finRightRep_eq_of_mem_invariants ψ.2.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [← adelicLift_descend hW, h0]
    funext x
    simp [adelicLift, archLift]
  exact Module.Finite.of_injective Φ hinj

open Classical in

def heckeFin (N p : ℕ) [NeZero p] : Finset (FiniteAdelicGL ℚ 2) :=
  (heckeReps N p).image (finiteDiagonal ℚ 2)

theorem coe_sum_heckeFin (p : ℕ) [NeZero p] [Fact p.Prime] (ψ : cuspForms ℚ 2) :
    ((∑ g ∈ heckeFin N p, finRepCusp ℚ 2 g ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) = heckeSum N p ψ := by
  classical
  rw [heckeFin, Finset.sum_image (fun a ha b hb hab => eq_of_inv_mul_mem_Gamma0Level N p ha hb
    (by rw [hab, inv_mul_cancel]; exact one_mem _))]
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem liftCusp_mem_of_le_translateSpanCusp_alt (μ : Measure (Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (ev : ℕ → ℂ) (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) (Y : Submodule ℂ (cuspForms ℚ 2)) (hYT : Y ≤ translateSpanCusp f)
    (hY : ∀ g, ∀ y ∈ Y, finRepCusp ℚ 2 g y ∈ Y) (hY0 : Y ≠ ⊥) : liftCusp f ∈ Y := by
  have hex : ∀ g : FiniteAdelicGL ℚ 2, ∃ y : Reduction.normOneGL ℚ 2, ∀ ψ ∈ translateSpanCusp f,
      cuspToL2 μ (finRepCusp ℚ 2 g ψ) = cuspRep μ y (cuspToL2 μ ψ) := fun g => cuspToL2_finRepCusp μ f g
  have hφS : ∀ j : {p : ℕ // p.Prime}, ∑ g ∈ @heckeFin N j.1 ⟨j.2.ne_zero⟩, finRepCusp ℚ 2 g (liftCusp f) =
      (heckeConst j.1 k * ev j.1) • liftCusp f := by
    rintro ⟨p, hp⟩
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    apply Subtype.ext
    rw [coe_sum_heckeFin]
    change heckeSum N p (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) = _
    rw [heckeSum_liftEquiv, ← heckeCusp_toSlashInvariantForm, hf p]
    have e : (ev p • f).toSlashInvariantForm = ev p • f.toSlashInvariantForm := rfl
    rw [e, map_smul, Submodule.coe_smul, Submodule.coe_smul, mul_smul]
    rfl
  have hP : ∀ z ∈ translateSpanCusp f, (∀ u : Gamma0Level N, finRepCusp ℚ 2 u z = z) →
      (∀ j : {p : ℕ // p.Prime}, ∑ g ∈ @heckeFin N j.1 ⟨j.2.ne_zero⟩, finRepCusp ℚ 2 g z =
        (heckeConst j.1 k * ev j.1) • z) → ∃ c : ℂ, z = c • liftCusp f := by
    intro z hzT hzK hzE
    obtain ⟨F, hF⟩ := exists_cuspForm_of_mem_translateSpan f (coe_mem_translateSpan f hzT)
      (fun u hu => congrArg Subtype.val (hzK ⟨u, hu⟩))
    have hFe : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k F = ev p • F := by
      intro p hp
      have : NeZero p := ⟨hp.out.ne_zero⟩
      have h1 : heckeSum N p (z : AdelicGL ℚ 2 → ℂ) = (heckeConst p k * ev p) • (z : AdelicGL ℚ 2 → ℂ) := by
        rw [← coe_sum_heckeFin]
        have := congrArg Subtype.val (hzE ⟨p, hp.out⟩)
        exact this
      rw [← hF, heckeSum_liftEquiv, mul_smul] at h1
      have h2 := smul_right_injective _ (heckeConst_ne_zero (k := k) p) h1
      have h3 : liftEquiv N k (heckeSlash N p k F.toSlashInvariantForm) =
          liftEquiv N k (ev p • F.toSlashInvariantForm) := by
        apply Subtype.ext
        rw [map_smul, Submodule.coe_smul]
        exact h2
      have h4 := (liftEquiv N k).injective h3
      ext w
      exact congrArg (fun G : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => G w) h4
    obtain ⟨c, hc⟩ : ∃ c : ℂ, F = c • f := ⟨_, eq_smul_of_eigen f F ev hf hFe hf1⟩
    subst hc
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hF]
    have e : (c • f).toSlashInvariantForm = c • f.toSlashInvariantForm := rfl
    rw [e, map_smul, Submodule.coe_smul, Submodule.coe_smul]
    rfl
  have key := mem_of_stable_of_eigen (ρ := finRepCusp ℚ 2) (ι := cuspToL2 μ) (T := translateSpanCusp f)
    (φ := liftCusp f) (K := Gamma0Level N) (J := {p : ℕ // p.Prime})
    (S := fun j => @heckeFin N j.1 ⟨j.2.ne_zero⟩) (ev := fun j => heckeConst j.1 k * ev j.1)
  have k2 := key rfl (fun v hv h0 => eq_zero_of_cuspFormLp_eq_zero μ f hv h0)
  have hunit : ∀ g : FiniteAdelicGL ℚ 2, ∀ v ∈ translateSpanCusp f, ∀ w ∈ translateSpanCusp f,
      @inner ℂ (cuspidalL2 μ) InnerProductSpace.toInner (cuspToL2 μ (finRepCusp ℚ 2 g v))
        (cuspToL2 μ (finRepCusp ℚ 2 g w)) =
      @inner ℂ (cuspidalL2 μ) InnerProductSpace.toInner (cuspToL2 μ v) (cuspToL2 μ w) := by
    intro g v hv w hw
    have hy := (hex g).choose_spec
    exact (congrArg₂ (fun a b : cuspidalL2 μ => @inner ℂ (cuspidalL2 μ) InnerProductSpace.toInner a b)
      (hy v hv) (hy w hw)).trans (UnitaryRep.inner_map_map _ _ _ _)
  exact k2 hunit (fun u => Subtype.ext (funext fun x => (liftEquiv N k f.toSlashInvariantForm).2.right_level x u u.2))
    (fun v hv => finite_range_of_isOpen_stabilizer _ (mem_smoothVectors.1 (translateSpanCusp_le_smoothVectors f hv)) _
      (isCompact_Gamma0Level N))
    (finiteDimensional_translateSpanCusp_fixed f) hφS hP Y hYT hY hY0

theorem liftCusp_mem_of_le_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (ev : ℕ → ℂ) (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) (Y : Submodule ℂ (cuspForms ℚ 2)) (hYT : Y ≤ translateSpanCusp f)
    (hY : ∀ g, ∀ y ∈ Y, finRepCusp ℚ 2 g y ∈ Y) (hY0 : Y ≠ ⊥) : liftCusp f ∈ Y :=
  liftCusp_mem_of_le_translateSpanCusp_alt Measure.haar f ev hf hf1 Y hYT hY hY0

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

def IsGKFStable (W : Submodule ℂ (cuspForms ℚ 2)) : Prop :=
  (∀ X, ∀ v ∈ W, (gkModuleCusp ℚ 2).ρ X v ∈ W) ∧ (∀ x, ∀ v ∈ W, (gkModuleCusp ℚ 2).σ x v ∈ W) ∧
    ∀ g, ∀ v ∈ W, finRepCusp ℚ 2 g v ∈ W

def gkfSpan (φ : cuspForms ℚ 2) : Submodule ℂ (cuspForms ℚ 2) :=
  sInf {W | IsGKFStable W ∧ φ ∈ W}

theorem mem_gkfSpan_self (φ : cuspForms ℚ 2) : φ ∈ gkfSpan φ :=
  Submodule.mem_sInf.2 fun _ hW => hW.2

theorem gkfSpan_le {φ : cuspForms ℚ 2} {W : Submodule ℂ (cuspForms ℚ 2)} (hW : IsGKFStable W) (hφ : φ ∈ W) :
    gkfSpan φ ≤ W :=
  sInf_le ⟨hW, hφ⟩

theorem isGKFStable_gkfSpan (φ : cuspForms ℚ 2) : IsGKFStable (gkfSpan φ) :=
  ⟨fun X v hv => Submodule.mem_sInf.2 fun W hW => hW.1.1 X v (Submodule.mem_sInf.1 hv W hW),
    fun x v hv => Submodule.mem_sInf.2 fun W hW => hW.1.2.1 x v (Submodule.mem_sInf.1 hv W hW),
    fun g v hv => Submodule.mem_sInf.2 fun W hW => hW.1.2.2 g v (Submodule.mem_sInf.1 hv W hW)⟩

theorem IsGKFStable.cuspOp_mem {W : Submodule ℂ (cuspForms ℚ 2)} (hW : IsGKFStable W) (B : Matrix (Fin 2) (Fin 2) ℂ)
    {v : cuspForms ℚ 2} (hv : v ∈ W) : cuspOp B v ∈ W :=
  add_mem (hW.1 _ v hv) (Submodule.smul_mem _ _ (hW.1 _ v hv))

def IsRot (x : archCompact ℚ 2) : Prop :=
  ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ kMat x = kGL w hw

def IsRefl (x : archCompact ℚ 2) : Prop :=
  ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ kMat x = toReal epsilon * kGL w hw

theorem isRot_or_isRefl (x : archCompact ℚ 2) : IsRot x ∨ IsRefl x := by
  obtain ⟨w, hw, h1, h | h⟩ := exists_kGL_of_mem_archCompact x
  · exact Or.inl ⟨w, hw, h1, h⟩
  · exact Or.inr ⟨w, hw, h1, h⟩

theorem IsRot.det_pos {x : archCompact ℚ 2} (hx : IsRot x) : 0 < (kMat x).det.val := by
  obtain ⟨w, hw, -, h⟩ := hx
  rw [h]
  exact det_kGL_pos w hw

theorem IsRefl.det_neg {x : archCompact ℚ 2} (hx : IsRefl x) : (kMat x).det.val < 0 := by
  obtain ⟨w, hw, -, h⟩ := hx
  rw [h, map_mul, Units.val_mul, det_toReal_epsilon]
  have := det_kGL_pos w hw
  linarith

theorem kMat_mul (x y : archCompact ℚ 2) : kMat (x * y) = kMat x * kMat y :=
  archToReal_mul _ _

theorem isRot_of_det_pos {x : archCompact ℚ 2} (h : 0 < (kMat x).det.val) : IsRot x :=
  (isRot_or_isRefl x).resolve_right fun hr => absurd hr.det_neg (not_lt.2 h.le)

theorem isRefl_of_det_neg {x : archCompact ℚ 2} (h : (kMat x).det.val < 0) : IsRefl x :=
  (isRot_or_isRefl x).resolve_left fun hr => absurd hr.det_pos (not_lt.2 h.le)

theorem IsRefl.mul_isRot {x y : archCompact ℚ 2} (hx : IsRot x) (hy : IsRefl y) : IsRefl (x * y) := by
  apply isRefl_of_det_neg
  rw [kMat_mul, map_mul, Units.val_mul]
  exact mul_neg_of_pos_of_neg hx.det_pos hy.det_neg

theorem IsRefl.mul_isRefl {x y : archCompact ℚ 2} (hx : IsRefl x) (hy : IsRefl y) : IsRot (x * y) := by
  apply isRot_of_det_pos
  rw [kMat_mul, map_mul, Units.val_mul]
  exact mul_pos_of_neg_of_neg hx.det_neg hy.det_neg

abbrev Rop : Module.End ℂ (cuspForms ℚ 2) := cuspOp raiseMat

abbrev Lop : Module.End ℂ (cuspForms ℚ 2) := cuspOp lowerMat

abbrev Jop : Module.End ℂ (cuspForms ℚ 2) := cuspOp rotMat

abbrev Zop : Module.End ℂ (cuspForms ℚ 2) := cuspOp 1

theorem cuspOp_zero : cuspOp 0 = 0 := by
  have := cuspOp_smul 0 0
  rwa [zero_smul, zero_smul] at this

theorem Jop_Rop : Jop * Rop - Rop * Jop = (2 * I) • Rop := by
  rw [← cuspOp_lie, rot_raise, cuspOp_smul]

theorem Lop_Rop : Lop * Rop - Rop * Lop = (4 * I) • Jop := by
  rw [← cuspOp_lie, lower_raise, cuspOp_smul]

theorem Jop_Lop_apply (ψ : cuspForms ℚ 2) : Jop (Lop ψ) - Lop (Jop ψ) = -((2 * I) • Lop ψ) := by
  have := congrArg (fun F : Module.End ℂ (cuspForms ℚ 2) => F ψ) (cuspOp_lie rotMat lowerMat)
  rw [rot_lower, cuspOp_smul] at this
  simpa using this.symm

theorem Lop_Rop_apply (ψ : cuspForms ℚ 2) : Lop (Rop ψ) - Rop (Lop ψ) = (4 * I) • Jop ψ := by
  have := congrArg (fun F : Module.End ℂ (cuspForms ℚ 2) => F ψ) Lop_Rop
  simpa using this

theorem negJop_Lop : -Jop * Lop - Lop * -Jop = (2 * I) • Lop := by
  ext ψ : 1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, map_neg, LinearMap.smul_apply]
  rw [show -(Jop (Lop ψ)) - -(Lop (Jop ψ)) = -(Jop (Lop ψ) - Lop (Jop ψ)) by abel, Jop_Lop_apply, neg_neg]

theorem Rop_Lop : Rop * Lop - Lop * Rop = (4 * I) • -Jop := by
  ext ψ : 1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply]
  rw [show Rop (Lop ψ) - Lop (Rop ψ) = -(Lop (Rop ψ) - Rop (Lop ψ)) by abel, Lop_Rop_apply, smul_neg]

theorem Zop_commute (B : Matrix (Fin 2) (Fin 2) ℂ) : Commute Zop (cuspOp B) := by
  have := cuspOp_lie 1 B
  rw [Matrix.one_mul, Matrix.mul_one, sub_self, cuspOp_zero] at this
  exact sub_eq_zero.1 this.symm

abbrev σc (x : archCompact ℚ 2) : Module.End ℂ (cuspForms ℚ 2) := archCompactRepCusp ℚ 2 x

theorem σc_Rop_rot {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = kGL w hw) (ψ : cuspForms ℚ 2) :
    σc x (Rop ψ) = (starRingEnd ℂ w / w) • Rop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (starRingEnd ℂ w / w) • raiseMat)
    (by rw [kMatC_of_plus hK]; exact plus_raiseMat w hw), cuspOp_smul, LinearMap.smul_apply]

theorem σc_Lop_rot {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = kGL w hw) (ψ : cuspForms ℚ 2) :
    σc x (Lop ψ) = (w / starRingEnd ℂ w) • Lop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (w / starRingEnd ℂ w) • lowerMat)
    (by rw [kMatC_of_plus hK]; exact plus_lowerMat w hw), cuspOp_smul, LinearMap.smul_apply]

theorem σc_Rop_refl {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw)
    (ψ : cuspForms ℚ 2) : σc x (Rop ψ) = (-(starRingEnd ℂ w / w)) • Lop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (-(starRingEnd ℂ w / w)) • lowerMat)
    (by rw [kMatC_of_minus hK]; exact minus_raiseMat w hw), cuspOp_smul, LinearMap.smul_apply]

theorem σc_Lop_refl {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw)
    (ψ : cuspForms ℚ 2) : σc x (Lop ψ) = (-(w / starRingEnd ℂ w)) • Rop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (-(w / starRingEnd ℂ w)) • raiseMat)
    (by rw [kMatC_of_minus hK]; exact minus_lowerMat w hw), cuspOp_smul, LinearMap.smul_apply]

theorem σc_Jop_refl {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw)
    (ψ : cuspForms ℚ 2) : σc x (Jop ψ) = (-1 : ℂ) • Jop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (-1 : ℂ) • rotMat)
    (by rw [kMatC_of_minus hK]; exact minus_rotMat w hw), cuspOp_smul, LinearMap.smul_apply]

theorem σc_pow {x : archCompact ℚ 2} {B B' : Module.End ℂ (cuspForms ℚ 2)} {c : ℂ}
    (h : ∀ ψ, σc x (B ψ) = c • B' (σc x ψ)) (j : ℕ) (ψ : cuspForms ℚ 2) :
    σc x ((B ^ j) ψ) = c ^ j • (B' ^ j) (σc x ψ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' B j, Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' B' j, Module.End.mul_apply,
      pow_succ' c j]

theorem matrix_eq_combo (B : Matrix (Fin 2) (Fin 2) ℂ) :
    B = (((B 0 1 + B 1 0) / 2 + I * (B 0 0 - B 1 1) / 2) / 2) • raiseMat +
      (((B 0 1 + B 1 0) / 2 - I * (B 0 0 - B 1 1) / 2) / 2) • lowerMat +
      ((B 0 1 - B 1 0) / 2) • rotMat + ((B 0 0 + B 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raiseMat, lowerMat, rotMat] <;> ring_nf <;> simp only [I_sq] <;> ring

theorem cuspOp_eq_combo (B : Matrix (Fin 2) (Fin 2) ℂ) :
    cuspOp B = (((B 0 1 + B 1 0) / 2 + I * (B 0 0 - B 1 1) / 2) / 2) • Rop +
      (((B 0 1 + B 1 0) / 2 - I * (B 0 0 - B 1 1) / 2) / 2) • Lop +
      ((B 0 1 - B 1 0) / 2) • Jop + ((B 0 0 + B 1 1) / 2) • Zop := by
  conv_lhs => rw [matrix_eq_combo B]
  simp only [cuspOp_add, cuspOp_smul]

theorem cuspOp_pow_finRepCusp (B : Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) (g : FiniteAdelicGL ℚ 2)
    (ψ : cuspForms ℚ 2) : (cuspOp B ^ j) (finRepCusp ℚ 2 g ψ) = finRepCusp ℚ 2 g ((cuspOp B ^ j) ψ) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, cuspOp_finRepCusp, Module.End.mul_apply]

theorem σc_finRepCusp (x : archCompact ℚ 2) (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) :
    σc x (finRepCusp ℚ 2 g ψ) = finRepCusp ℚ 2 g (σc x ψ) :=
  gkModuleCusp_σ_finRepCusp x g ψ

theorem σc_mul_apply (x y : archCompact ℚ 2) (ψ : cuspForms ℚ 2) : σc x (σc y ψ) = σc (x * y) ψ := by
  rw [σc, σc, σc, map_mul, Module.End.mul_apply]

section Span

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

theorem Lop_T {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : Lop t = 0 := by
  rw [cuspOp_translateSpanCusp f holCoeff_lowerMat ht, weightChar_lowerMat, zero_smul]

theorem Jop_T {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : Jop t = (I * k) • t := by
  rw [cuspOp_translateSpanCusp f holCoeff_rotMat ht, weightChar_rotMat]

theorem Zop_T {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : Zop t = 0 := by
  rw [cuspOp_translateSpanCusp f holCoeff_one ht, weightChar_one, zero_smul]

def reflSpan : Submodule ℂ (cuspForms ℚ 2) :=
  Submodule.span ℂ {v | ∃ x, IsRefl x ∧ ∃ t ∈ translateSpanCusp f, v = σc x t}

theorem reflSpan_induction {P : cuspForms ℚ 2 → Prop} (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : ℂ) a, P a → P (c • a))
    (hgen : ∀ x, IsRefl x → ∀ t ∈ translateSpanCusp f, P (σc x t)) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) :
    P s := by
  induction hs using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, t, ht, rfl⟩ := hv
    exact hgen x hx t ht
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

theorem Rop_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : Rop s = 0 := by
  refine reflSpan_induction f (P := fun s => Rop s = 0) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    (fun c a ha => by rw [map_smul, ha, smul_zero]) (fun x hx t ht => ?_) hs
  obtain ⟨w, hw, -, hK⟩ := hx
  have h := σc_Lop_refl hK t
  rw [Lop_T f ht, map_zero] at h
  have hc : (-(w / starRingEnd ℂ w)) ≠ 0 := neg_ne_zero.2 (div_ne_zero hw (conj_ne_zero' hw))
  exact (smul_eq_zero.1 h.symm).resolve_left hc

theorem negJop_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : (-Jop) s = (I * k) • s := by
  refine reflSpan_induction f (P := fun s => (-Jop) s = (I * k) • s) (by simp) (fun a b ha hb => by rw [map_add, ha, hb, smul_add])
    (fun c a ha => by rw [map_smul, ha, smul_comm]) (fun x hx t ht => ?_) hs
  obtain ⟨w, hw, -, hK⟩ := hx
  have h := σc_Jop_refl hK t
  rw [Jop_T f ht, map_smul] at h
  rw [LinearMap.neg_apply, h]
  exact (neg_one_smul ℂ _).symm

theorem Zop_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : Zop s = 0 := by
  refine reflSpan_induction f (P := fun s => Zop s = 0) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    (fun c a ha => by rw [map_smul, ha, smul_zero]) (fun x _ t ht => ?_) hs
  rw [← archCompactRepCusp_cuspOp_one, Zop_T f ht, map_zero]

def weightPiece : ℕ ⊕ ℕ → Submodule ℂ (cuspForms ℚ 2)
  | Sum.inl j => (translateSpanCusp f).map (Rop ^ j)
  | Sum.inr j => (reflSpan f).map (Lop ^ j)

def weightSpan : Submodule ℂ (cuspForms ℚ 2) := ⨆ i, weightPiece f i

variable (k) in

def weightEig : ℕ ⊕ ℕ → ℂ
  | Sum.inl j => I * k + 2 * I * j
  | Sum.inr j => -(I * k + 2 * I * j)

theorem Jop_weightPiece {i : ℕ ⊕ ℕ} {v : cuspForms ℚ 2} (hv : v ∈ weightPiece f i) :
    Jop v = weightEig k i • v := by
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    exact J_pow_apply Jop_Rop (Jop_T f ht) j
  · obtain ⟨s, hs, rfl⟩ := hv
    have := J_pow_apply negJop_Lop (negJop_reflSpan f hs) j
    rw [LinearMap.neg_apply, neg_eq_iff_eq_neg, ← _root_.neg_smul] at this
    exact this

theorem weightEig_injective (hk : 0 < k) : Function.Injective (weightEig k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rintro (j | j) (j' | j') h <;> simp only [weightEig, Complex.ext_iff] at h <;>
    simp at h
  · exact congrArg Sum.inl h
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ j' := Nat.cast_nonneg j'
    linarith
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ j' := Nat.cast_nonneg j'
    linarith
  · exact congrArg Sum.inr h

end Span

section Stable

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

theorem mem_weightSpan_of_mem {i : ℕ ⊕ ℕ} {v : cuspForms ℚ 2} (hv : v ∈ weightPiece f i) : v ∈ weightSpan f :=
  (le_iSup (weightPiece f) i) hv

theorem weightSpan_map_mem (op : Module.End ℂ (cuspForms ℚ 2))
    (h : ∀ i, ∀ v ∈ weightPiece f i, op v ∈ weightSpan f) : ∀ v ∈ weightSpan f, op v ∈ weightSpan f := by
  intro v hv
  have : weightSpan f ≤ (weightSpan f).comap op := iSup_le fun i w hw => h i w hw
  exact this hv

theorem Rop_pow_mem (j : ℕ) {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : (Rop ^ j) t ∈ weightSpan f :=
  mem_weightSpan_of_mem f (i := Sum.inl j) ⟨t, ht, rfl⟩

theorem Lop_pow_mem (j : ℕ) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : (Lop ^ j) s ∈ weightSpan f :=
  mem_weightSpan_of_mem f (i := Sum.inr j) ⟨s, hs, rfl⟩

theorem Rop_weightSpan : ∀ v ∈ weightSpan f, Rop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Rop fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    rw [← Module.End.mul_apply, ← pow_succ']
    exact Rop_pow_mem f _ ht
  · obtain ⟨s, hs, rfl⟩ := hv
    cases j with
    | zero =>
      rw [pow_zero, Module.End.one_apply, Rop_reflSpan f hs]
      exact zero_mem _
    | succ m =>
      rw [L_pow_succ_apply negJop_Lop Rop_Lop (negJop_reflSpan f hs) (Rop_reflSpan f hs) m]
      exact Submodule.smul_mem _ _ (Lop_pow_mem f m hs)

theorem Lop_weightSpan : ∀ v ∈ weightSpan f, Lop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Lop fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    cases j with
    | zero =>
      rw [pow_zero, Module.End.one_apply, Lop_T f ht]
      exact zero_mem _
    | succ m =>
      rw [L_pow_succ_apply Jop_Rop Lop_Rop (Jop_T f ht) (Lop_T f ht) m]
      exact Submodule.smul_mem _ _ (Rop_pow_mem f m ht)
  · obtain ⟨s, hs, rfl⟩ := hv
    rw [← Module.End.mul_apply, ← pow_succ']
    exact Lop_pow_mem f _ hs

theorem Jop_weightSpan : ∀ v ∈ weightSpan f, Jop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Jop fun i v hv => ?_
  rw [Jop_weightPiece f hv]
  exact Submodule.smul_mem _ _ (mem_weightSpan_of_mem f hv)

theorem Zop_weightSpan : ∀ v ∈ weightSpan f, Zop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Zop fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    have hc := ((Zop_commute raiseMat).pow_right j).eq
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, Zop_T f ht, map_zero]
    exact zero_mem _
  · obtain ⟨s, hs, rfl⟩ := hv
    have hc := ((Zop_commute lowerMat).pow_right j).eq
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, Zop_reflSpan f hs, map_zero]
    exact zero_mem _

theorem cuspOp_weightSpan (B : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ v ∈ weightSpan f, cuspOp B v ∈ weightSpan f := by
  intro v hv
  rw [cuspOp_eq_combo]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;> refine Submodule.smul_mem _ _ ?_
  · exact Rop_weightSpan f v hv
  · exact Lop_weightSpan f v hv
  · exact Jop_weightSpan f v hv
  · exact Zop_weightSpan f v hv

theorem σc_weightSpan (x : archCompact ℚ 2) : ∀ v ∈ weightSpan f, σc x v ∈ weightSpan f := by
  refine weightSpan_map_mem f (σc x) fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    rcases isRot_or_isRefl x with ⟨w, hw, h1, hK⟩ | ⟨w, hw, h1, hK⟩
    · rw [σc_pow (σc_Rop_rot hK) j t, archCompactRepCusp_translateSpanCusp f x hw h1 hK ht, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Rop_pow_mem f j ht))
    · rw [σc_pow (σc_Rop_refl hK) j t]
      exact Submodule.smul_mem _ _ (Lop_pow_mem f j (Submodule.subset_span ⟨x, ⟨w, hw, h1, hK⟩, t, ht, rfl⟩))
  · obtain ⟨s, hs, rfl⟩ := hv
    refine reflSpan_induction f (P := fun s => σc x ((Lop ^ j) s) ∈ weightSpan f)
      (by rw [map_zero, map_zero]; exact zero_mem _)
      (fun a b ha hb => by rw [map_add, map_add]; exact add_mem ha hb)
      (fun c a ha => by rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ ha) (fun y hy t ht => ?_) hs
    rcases isRot_or_isRefl x with ⟨w, hw, h1, hK⟩ | ⟨w, hw, h1, hK⟩
    · rw [σc_pow (σc_Lop_rot hK) j, σc_mul_apply]
      have hxy : IsRefl (x * y) := IsRefl.mul_isRot ⟨w, hw, h1, hK⟩ hy
      exact Submodule.smul_mem _ _ (Lop_pow_mem f j (Submodule.subset_span ⟨x * y, hxy, t, ht, rfl⟩))
    · rw [σc_pow (σc_Lop_refl hK) j, σc_mul_apply]
      obtain ⟨w', hw', h1', hK'⟩ := IsRefl.mul_isRefl ⟨w, hw, h1, hK⟩ hy
      rw [archCompactRepCusp_translateSpanCusp f (x * y) hw' h1' hK' ht, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Rop_pow_mem f j ht))

theorem finRepCusp_reflSpan (g : FiniteAdelicGL ℚ 2) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) :
    finRepCusp ℚ 2 g s ∈ reflSpan f := by
  refine reflSpan_induction f (P := fun s => finRepCusp ℚ 2 g s ∈ reflSpan f)
    (by rw [map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) (fun y hy t ht => ?_) hs
  rw [← σc_finRepCusp]
  exact Submodule.subset_span ⟨y, hy, _, finRepCusp_mem_translateSpanCusp f g ht, rfl⟩

theorem finRepCusp_weightSpan (g : FiniteAdelicGL ℚ 2) :
    ∀ v ∈ weightSpan f, finRepCusp ℚ 2 g v ∈ weightSpan f := by
  refine weightSpan_map_mem f (finRepCusp ℚ 2 g) fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    rw [← cuspOp_pow_finRepCusp]
    exact Rop_pow_mem f j (finRepCusp_mem_translateSpanCusp f g ht)
  · obtain ⟨s, hs, rfl⟩ := hv
    rw [← cuspOp_pow_finRepCusp]
    exact Lop_pow_mem f j (finRepCusp_reflSpan f g hs)

theorem isGKFStable_weightSpan : IsGKFStable (weightSpan f) :=
  ⟨fun X v hv => by rw [gkModuleCusp_ρ_eq_cuspOp]; exact cuspOp_weightSpan f _ v hv,
    fun x v hv => σc_weightSpan f x v hv, fun g v hv => finRepCusp_weightSpan f g v hv⟩

theorem liftCusp_mem_translateSpanCusp : liftCusp f ∈ translateSpanCusp f :=
  Submodule.subset_span ⟨1, by show finRepCusp ℚ 2 1 (liftCusp f) = _; rw [map_one, Module.End.one_apply]⟩

theorem liftCusp_mem_weightSpan : liftCusp f ∈ weightSpan f := by
  have := Rop_pow_mem f 0 (liftCusp_mem_translateSpanCusp f)
  rwa [pow_zero, Module.End.one_apply] at this

theorem gkfSpan_le_weightSpan : gkfSpan (liftCusp f) ≤ weightSpan f :=
  gkfSpan_le (isGKFStable_weightSpan f) (liftCusp_mem_weightSpan f)

end Stable

section Extract

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

theorem σc_inv_apply (y : archCompact ℚ 2) (ψ : cuspForms ℚ 2) : σc y⁻¹ (σc y ψ) = ψ := by
  rw [σc_mul_apply, inv_mul_cancel, σc, map_one, Module.End.one_apply]

theorem σc_refl_reflSpan {y : archCompact ℚ 2} (hy : IsRefl y) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) :
    σc y s ∈ translateSpanCusp f := by
  refine reflSpan_induction f (P := fun s => σc y s ∈ translateSpanCusp f)
    (by rw [map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) (fun x hx t ht => ?_) hs
  rw [σc_mul_apply]
  obtain ⟨w, hw, h1, hK⟩ := IsRefl.mul_isRefl hy hx
  rw [archCompactRepCusp_translateSpanCusp f (y * x) hw h1 hK ht]
  exact Submodule.smul_mem _ _ ht

theorem exists_isRefl_of_mem_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) (hs0 : s ≠ 0) :
    ∃ y, IsRefl y := by
  by_contra h
  have h' : ∀ y, ¬ IsRefl y := fun y hy => h ⟨y, hy⟩
  have hbot : reflSpan f = ⊥ := by
    rw [reflSpan, Submodule.span_eq_bot]
    rintro v ⟨x, hx, -⟩
    exact absurd hx (h' x)
  rw [hbot] at hs
  exact hs0 ((Submodule.mem_bot ℂ).1 hs)

theorem IsGKFStable.cuspOp_pow_mem {W : Submodule ℂ (cuspForms ℚ 2)} (hW : IsGKFStable W)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) {v : cuspForms ℚ 2} (hv : v ∈ W) :
    (GL2Classical.cuspOp B ^ j) v ∈ W := by
  induction j with
  | zero => simpa using hv
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hW.cuspOp_mem B ih

theorem exists_ne_zero_mem_translateSpanCusp (hk : 0 < k) {W : Submodule ℂ (cuspForms ℚ 2)}
    (hW : IsGKFStable W) (hWV : W ≤ weightSpan f) (hW0 : W ≠ ⊥) :
    ∃ t ∈ translateSpanCusp f, t ≠ 0 ∧ t ∈ W := by
  classical
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨F, hF, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp (weightPiece f) w).1 (hWV hwW)
  have hJW : ∀ v ∈ W, Jop v ∈ W := fun v hv => hW.cuspOp_mem rotMat hv
  have hcomp := mem_of_sum_mem_of_eigen hJW F.support F (weightEig k)
    (fun i _ => Jop_weightPiece f (hF i)) ((weightEig_injective hk).injOn)
    (by rw [← hsum] at hwW; exact hwW)
  obtain ⟨i, hi⟩ : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hw0
    rw [← hsum, Finsupp.sum, he, Finset.sum_empty]
  have hFiW := hcomp i hi
  have hFi0 : F i ≠ 0 := Finsupp.mem_support_iff.1 hi
  rcases i with j | j
  · have hFj : F (Sum.inl j) ∈ (translateSpanCusp f).map (Rop ^ j) := hF (Sum.inl j)
    obtain ⟨t, ht, hte⟩ := hFj
    rw [← hte] at hFiW hFi0
    have h1 := L_pow_R_pow_apply Jop_Rop Lop_Rop (Jop_T f ht) (Lop_T f ht) j
    have hc := prod_ne_zero_of_pos hk j
    have ht0 : t ≠ 0 := fun h => hFi0 (by rw [h, map_zero])
    refine ⟨t, ht, ht0, ?_⟩
    have h2 := hW.cuspOp_pow_mem lowerMat j hFiW
    rw [h1] at h2
    have h3 := Submodule.smul_mem W (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m)))⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  · have hFj : F (Sum.inr j) ∈ (reflSpan f).map (Lop ^ j) := hF (Sum.inr j)
    obtain ⟨s, hs, hse⟩ := hFj
    rw [← hse] at hFiW hFi0
    have h1 := L_pow_R_pow_apply negJop_Lop Rop_Lop (negJop_reflSpan f hs) (Rop_reflSpan f hs) j
    have hc := prod_ne_zero_of_pos hk j
    have hs0 : s ≠ 0 := fun h => hFi0 (by rw [h, map_zero])
    have h2 := hW.cuspOp_pow_mem raiseMat j hFiW
    rw [h1] at h2
    have h3 := Submodule.smul_mem W (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m)))⁻¹ h2
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
    obtain ⟨y, hy⟩ := exists_isRefl_of_mem_reflSpan f hs hs0
    refine ⟨σc y s, σc_refl_reflSpan f hy hs, fun h => hs0 ?_, hW.2.1 y s h3⟩
    rw [← σc_inv_apply y s, h, map_zero]

end Extract

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

local notation "𝕢₁" => Function.Periodic.qParam 1

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem weight_pos_of_coeff_one (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) : 0 < k := by
  by_contra hk
  have hk' : k ≤ 0 := not_lt.1 hk
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ τ : ℍ, f τ = c := by
    rcases lt_or_eq_of_le hk' with hlt | rfl
    · have h0 := ModularForm.isZero_of_neg_weight hlt (CuspForm.toModularFormₗ f)
      exact ⟨0, fun τ => congrArg (fun F : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => F τ) h0⟩
    · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (CuspForm.toModularFormₗ f)
      exact ⟨c, fun τ => congrFun hc τ⟩
  have h1 := qExpansion_coeff_eq_of_hasSum f (b := fun n => if n = 0 then c else 0) (fun τ => by
    rw [hc τ]
    convert hasSum_ite_eq 0 c using 2 with n
    split_ifs with h
    · subst h; simp
    · simp) 1
  rw [hf1] at h1
  simp at h1

theorem liftCusp_ne_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) : liftCusp f ≠ 0 := by
  intro h
  have h1 : liftEquiv N k f.toSlashInvariantForm = 0 := by
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have h2 : f.toSlashInvariantForm = 0 := (liftEquiv N k).map_eq_zero_iff.1 h1
  have h3 : f = 0 := by
    ext τ
    exact congrArg (fun F : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => F τ) h2
  rw [h3] at hf1
  have h4 := qExpansion_coeff_eq_of_hasSum (0 : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (b := fun _ => 0) (fun τ => by simp) 1
  rw [hf1] at h4
  exact one_ne_zero h4

theorem gkfSpan_liftCusp_irreducible (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeCusp N p k f = c • f)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) :
    gkfSpan (liftCusp f) ≠ ⊥ ∧ ∀ W : Submodule ℂ (cuspForms ℚ 2), IsGKFStable W →
      W ≤ gkfSpan (liftCusp f) → W = ⊥ ∨ W = gkfSpan (liftCusp f) := by
  classical
  let ev : ℕ → ℂ := fun p => if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; Classical.choose (hf p)) else 0
  have hev : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f := by
    intro p hp
    have h := Classical.choose_spec (@hf p ⟨hp.out⟩)
    simp only [ev, dif_pos hp.out]
    exact h
  have hk := weight_pos_of_coeff_one f hf1
  refine ⟨fun h => liftCusp_ne_zero f hf1 ?_, fun W hW hWle => ?_⟩
  · have := mem_gkfSpan_self (liftCusp f)
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · right
      obtain ⟨t, htT, ht0, htW⟩ :=
        exists_ne_zero_mem_translateSpanCusp f hk hW (hWle.trans (gkfSpan_le_weightSpan f)) hW0
      have hY : liftCusp f ∈ W ⊓ translateSpanCusp f :=
        liftCusp_mem_of_le_translateSpanCusp f ev hev hf1 (W ⊓ translateSpanCusp f) inf_le_right
          (fun g y hy => ⟨hW.2.2 g y hy.1, finRepCusp_mem_translateSpanCusp f g hy.2⟩)
          (fun h => ht0 ((Submodule.mem_bot ℂ).1 (h ▸ ⟨htW, htT⟩)))
      exact le_antisymm hWle (gkfSpan_le hW hY.1)

end GL2Classical

end

end GroundTheory.Automorphic
end
