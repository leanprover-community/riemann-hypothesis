import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAlmostOntoOfLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorPropertiesStatement

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  first | exact @GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | exact GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | (intros; apply GlobalTheory.Cyc.Decomp.lam_mul_of_isMat <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem act_eq_of_mem_intC {l : ℕ} [Fact l.Prime]
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ intC F) : act σ y = y := by
  simp only [intC, inC, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe] at hy
  obtain ⟨⟨x, hxF, rfl⟩, -⟩ := hy
  rw [ha.1 σ x, (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ x hxF]

theorem isDec_of_matrix : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  intro l _ act χ K m d M D g ha hg hMc hMmul hMfix hD hDinv hInt hH hgclose
  obtain ⟨Y, hY, hDY⟩ := hDinv
  have hl : (l : PadicComplex l) ≠ 0 := by
    exact_mod_cast (Fact.out : l.Prime).ne_zero

  have hright : D * ((l : PadicComplex l)⁻¹ • Y) = 1 := by
    rw [Matrix.mul_smul, hDY, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hdet : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hright
  have hinv : D⁻¹ = (l : PadicComplex l)⁻¹ • Y := Matrix.inv_eq_right_inv hright
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hdet
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hdet

  have hmapmul : ∀ (e : PadicComplex l ≃+* PadicComplex l) (A B : Matrix (Fin d) (Fin d) (PadicComplex l)),
      (A * B).map e = A.map e * B.map e := by
    intro e A B
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  have hmapcomp : ∀ σ τ : GQ l, D.map (act (σ * τ)) = (D.map (act τ)).map (act σ) := by
    intro σ τ
    ext i j
    simp only [Matrix.map_apply, map_mul]
    rfl

  refine ⟨fun σ => D⁻¹ * (M σ * D.map (act σ)), hdet, hD, ?_, ⟨hg, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    rw [hinv, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl, one_mul]
    exact hY a b
  · intro a b
    simp only [Matrix.mul_apply, Matrix.map_apply]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hMc k j).mul ?_
    exact (IsActC.continuous_orbit l act ha (D j b)).continuousOn
  · intro σ hσ a b
    obtain ⟨X, hX, hMX⟩ := hInt σ hσ
    show (D⁻¹ * (M σ * D.map (act σ))) a b ∈ intC (Ks K m)
    rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    exact hX a b
  · intro σ hσ τ hτ
    obtain ⟨X, hX, hMX⟩ := hInt τ hτ
    have hUτ : D⁻¹ * (M τ * D.map (act τ)) = X := by
      rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]

    have hXfix : X.map (act σ) = X := by
      ext i j
      exact act_eq_of_mem_intC ha (show σ ∈ (Ks K m).fixingSubgroup from hσ) (hX i j)
    show D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
      = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ)))
    calc D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
        = D⁻¹ * (M σ * (M τ * D.map (act τ)).map (act σ)) := by
          rw [hMmul σ hσ τ hτ, hmapmul, hMfix σ hσ τ hτ, hmapcomp]
          simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (M σ * (D.map (act σ) * X)) := by rw [hMX, hmapmul, hXfix]
      _ = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ))) := by
          rw [hUτ]
          simp only [Matrix.mul_assoc]
  · intro σ hσ
    show D⁻¹ * (M σ * D.map (act σ)) = 1
    rw [hH σ hσ, hDD]
  · intro a b
    obtain ⟨X, hX, hMX⟩ := hgclose
    have hU : D⁻¹ * (M g * D.map (act g)) - 1 = X := by
      rw [← hDD, ← Matrix.mul_sub, hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    show ‖(D⁻¹ * (M g * D.map (act g)) - 1) a b‖ < rho1 l
    rw [hU]
    exact hX a b
  · intro σ hσ
    show D * (D⁻¹ * (M σ * D.map (act σ))) = M σ * D.map (act σ)
    rw [← Matrix.mul_assoc, hDD', Matrix.one_mul]

end GlobalTheory.Cyc.Decomp
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompletion_frame_of_matrix_form : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.isDec_of_matrix
end

section
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem ringHom_padicInt_OC_ext (f g : ℤ_[l] →+* OC l) (x : ℤ_[l]) : f x = g x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn : ‖((l : ℕ) : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
    have h := norm_zC ((l : ℕ) : ℤ_[l])
    rw [PadicInt.norm_p] at h
    rw [← h]
    simp [zC]
  have key : ∀ k : ℕ, ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ ((l : ℝ)⁻¹) ^ k := by
    intro k
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + y * (l : ℤ_[l]) ^ k := by rw [hy]; ring
    have h1 : f x - g x = (f y - g y) * ((l : ℕ) : OC l) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    have h2 : ((f x - g x : OC l) : PadicComplex l) =
        ((f y - g y : OC l) : PadicComplex l) * ((l : ℕ) : PadicComplex l) ^ k := by
      rw [h1]; push_cast; rfl
    rw [h2, norm_mul, norm_pow, hn]
    exact mul_le_of_le_one_left (by positivity) ((mem_OC _).1 (f y - g y).2)
  have h0 : ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hl)) key
  have h3 : f x - g x = 0 := Subtype.ext (norm_le_zero_iff.1 h0)
  exact sub_eq_zero.1 h3

theorem map_frobeniusEquiv_symm_OCb (e : OCb l →+* OCb l) (x : OCb l) :
    e ((frobeniusEquiv (OCb l) l).symm x) = (frobeniusEquiv (OCb l) l).symm (e x) := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]

theorem exists_thetaShift_ringHom {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) :
    ∃ θ : Ainf l →+* OC l,
      (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
        AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
      ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n) := by
  induction n with
  | zero =>
    obtain ⟨θ, -, -, h1, -, h2⟩ := exists_isTheta l P AI
    exact ⟨θ, h1, h2⟩
  | succ n ih =>
    obtain ⟨θ, h1, h2⟩ := ih
    refine ⟨θ.comp (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom), fun g a => ?_,
      fun j => ?_⟩
    · have e : WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.actW g a) =
          AI.actW g (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom a) :=
        WittVector.ext fun k =>
          (map_frobeniusEquiv_symm_OCb (AI.actT g).toRingHom (a.coeff k)).symm
      rw [RingHom.comp_apply, RingHom.comp_apply, e, h1]
    · have e : (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.εroot j) = AI.εroot (j + 1) := by
        rw [LocAinf.εroot, LocAinf.εroot, Function.iterate_succ_apply']
        rfl
      rw [RingHom.comp_apply, WittVector.map_teichmuller, e, h2, add_assoc, add_comm 1 n]

theorem exists_isThetaShift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ),
    ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  intro l _ P AI n
  obtain ⟨θ, h1, h2⟩ := exists_thetaShift_ringHom AI n
  exact ⟨{ toRingHom := θ
           commutes' := fun x => ringHom_padicInt_OC_ext (θ.comp (algebraMap ℤ_[l] (Ainf l)))
             (algebraMap ℤ_[l] (OC l)) x }, fun g a => h1 g a, h2⟩

end GlobalTheory.Cyc.Decomp
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fontaineTheta_frobeniusInverse_shift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ), ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.exists_isThetaShift
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

variable {l : ℕ} [Fact l.Prime]

theorem coe_emb_algebraMap (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (x : ℤ_[l]) :
    algebraMap (Om l) (PadicComplex l) (τ ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1)) = zC x := by
  have h : ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (x : ℚ_[l]) := by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl
  rw [h, AlgHom.commutes]; rfl

theorem exists_evEmb (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) :
    ∃ ev : OCO LL →+* PadicComplex l, ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)) := by
  letI : Algebra ℤ_[l] (PadicComplex l) :=
    ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).toAlgebra
  let u : OC l →ₐ[ℤ_[l]] PadicComplex l :=
    { (PadicComplexInt l).subtype with commutes' := fun x => rfl }
  let v : ↥(OL LL) →ₐ[ℤ_[l]] PadicComplex l :=
    { (algebraMap (Om l) (PadicComplex l)).comp (τ.toRingHom.comp (OL LL).val.toRingHom) with
      commutes' := fun x => coe_emb_algebraMap LL τ x }
  exact ⟨(Algebra.TensorProduct.productMap u v).toRingHom, fun c a => rfl⟩

theorem evEmb_eq_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (ev : OCO LL →+* PadicComplex l)
    (hev : ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)))
    (x : OCO LL) :
    ev x = ∑ k, kap o x k * algebraMap (Om l) (PadicComplex l) (τ (o k : ↥LL.1)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero, zero_mul, Finset.sum_const_zero]
  | add x y hx hy => simp only [map_add, kap_add, hx, hy, add_mul, Finset.sum_add_distrib]
  | tmul c a =>
    rw [hev]
    simp only [kap_tmul, mul_assoc, ← Finset.mul_sum]
    congr 1
    conv_lhs => rw [← o.sum_repr a]
    simp only [Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
      map_mul, coe_emb_algebraMap]

theorem exists_emb_det_ne_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) :
    ∃ τ : Fin f → (↥LL.1 →ₐ[ℚ_[l]] Om l),
      (Matrix.of fun i j => τ j (o i : ↥LL.1) : Matrix (Fin f) (Fin f) (Om l)).det ≠ 0 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  haveI := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  let b := o.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) ↥LL.1
  have hb : ∀ i, b i = (o i : ↥LL.1) := fun i =>
    Module.Basis.localizationLocalization_apply _ _ _ _ i
  have hc : Fintype.card (Fin f) = Fintype.card (↥LL.1 →ₐ[ℚ_[l]] Om l) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hc
  refine ⟨e, fun h0 => ?_⟩
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ_[l] (Om l) b e
  have h2 : Algebra.embeddingsMatrixReindex ℚ_[l] (Om l) b e =
      Matrix.of fun i j => e j (o i : ↥LL.1) := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, hb]
  rw [h2, h0, zero_pow two_ne_zero, map_eq_zero] at h1
  exact Algebra.discr_not_zero_of_basis ℚ_[l] b h1

theorem kap_idem_algebraic {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (e : OCO LL) (he : IsIdempotentElem e) (k : Fin f) :
    ∃ x : Om l, algebraMap (Om l) (PadicComplex l) x = kap o e k := by
  obtain ⟨τ, hτ⟩ := exists_emb_det_ne_zero o
  set M : Matrix (Fin f) (Fin f) (Om l) := Matrix.of fun i j => τ j (o i : ↥LL.1) with hM
  have hy : ∀ j, ∃ y : Om l, algebraMap (Om l) (PadicComplex l) y =
      ∑ k, kap o e k * algebraMap (Om l) (PadicComplex l) (M k j) := by
    intro j
    obtain ⟨ev, hev⟩ := exists_evEmb LL (τ j)
    have h1 := evEmb_eq_sum o (τ j) ev hev e
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map ev) with h | h
    · exact ⟨0, by rw [map_zero, ← h, h1]; rfl⟩
    · exact ⟨1, by rw [map_one, ← h, h1]; rfl⟩
  choose y hy using hy
  refine ⟨∑ j, y j * M⁻¹ j k, ?_⟩
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (Ne.isUnit hτ)
  simp only [map_sum, map_mul, hy, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← map_mul, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply]
  simp [apply_ite (algebraMap (Om l) (PadicComplex l))]

theorem kap_idem_mem_inC (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l))
    (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL)
    (hact : IsActC act) (he : IsIdempotentElem e)
    (hfix : ∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) (k : Fin f) : kap o e k ∈ inC K.1 := by
  obtain ⟨x, hx⟩ := kap_idem_algebraic o e he k
  refine ⟨x, ?_, hx⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
  rintro ⟨g, hg⟩
  have h1 := hfix g hg k
  rw [← hx] at h1
  apply (algebraMap (Om l) (PadicComplex l)).injective
  exact (hact.1 g x).symm.trans h1

end GlobalTheory.Cyc.Decomp
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kap_mem_inC_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL), IsActC act → IsIdempotentElem e → (∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) → ∀ k, kap o e k ∈ inC K.1 := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.kap_idem_mem_inC
end

section
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp.Coord

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem inC_zero (F : IntermediateField ℚ_[l] (Om l)) : (0 : PadicComplex l) ∈ inC F :=
  ⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩

theorem inC_add {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x + y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u + v, F.add_mem hu hv, UniformSpace.Completion.coe_add _ _⟩

theorem inC_mul {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x * y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, F.mul_mem hu hv, UniformSpace.Completion.coe_mul _ _⟩

theorem inC_zC (F : IntermediateField ℚ_[l] (Om l)) (x : ℤ_[l]) : zC x ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) (x : ℚ_[l]), F.algebraMap_mem _, rfl⟩

theorem inC_sum {F : IntermediateField ℚ_[l] (Om l)} {ι : Type} (s : Finset ι)
    (g : ι → PadicComplex l) (h : ∀ i ∈ s, g i ∈ inC F) : ∑ i ∈ s, g i ∈ inC F :=
  Finset.sum_induction g (· ∈ inC F) (fun _ _ => inC_add) (inC_zero F) h

theorem kap_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {ι : Type}
    (s : Finset ι) (g : ι → OCO LL) (k : Fin f) :
    kap o (∑ i ∈ s, g i) k = ∑ i ∈ s, kap o (g i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, kap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kap_add, ih]

theorem kap_mul_one_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (x : OCO LL) (a : ↥(OL LL)) (k : Fin f) :
    kap o (x * ((1 : OC l) ⊗ₜ[ℤ_[l]] a)) k = ∑ j, kap o x j * zC (o.repr (o j * a) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (OC l) o).sum_repr x]
  rw [Finset.sum_mul, kap_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul,
    kap_tmul, smul_eq_mul, mul_one, mul_one]
  rfl

theorem let_split {O : Type} [CommRing O] {n : ℕ} [NeZero n] (a : LetA O n) :
    ∃ a' : LetA O n, a = ∑ i, letE i * algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i))
      + letπ * a' := by
  refine ⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun j => ?_⟩
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [letE, letπ, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.algebraMap_apply]
    rw [add_comm]
    exact PowerSeries.eq_X_mul_shift_add_const (a j)
  · intro i _ hij
    simp [letE, Pi.single_eq_of_ne hij.symm]
  · simp

theorem coord (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n]
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l)
    (hO : ∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a)
    (hπ : φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) (hc : ‖(c : PadicComplex l)‖ < 1)
    (hcF : (c : PadicComplex l) ∈ inC (Ks K m))
    (hE : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) :
    ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  haveI := GlobalTheory.TateDecomp.finite_Ks K m
  have hcl : IsClosed (intC (Ks K m)) := (GlobalTheory.TateDecomp.isCompact_intC (Ks K m)).isClosed
  have key : ∀ (N : ℕ) (k : Fin f) (a : LetA ↥(OL LL) n), ∃ s ∈ inC (Ks K m),
      ∃ r : PadicComplex l, ‖r‖ ≤ 1 ∧ kap o (φ a) k = s + (c : PadicComplex l) ^ N * r := by
    intro N k
    induction N with
    | zero => exact fun a => ⟨0, inC_zero _, kap o (φ a) k, norm_kap_le _ _ _, by simp⟩
    | succ N ih =>
      intro a
      obtain ⟨a', ha⟩ := let_split a
      obtain ⟨s, hs, r, hr, h⟩ := ih a'
      refine ⟨∑ i, kap o (φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))) k
        + (c : PadicComplex l) * s, inC_add (inC_sum _ _ fun i _ => ?_) (inC_mul hcF hs), r, hr, ?_⟩
      · rw [kap_mul_one_tmul]
        exact inC_sum _ _ fun j _ => inC_mul (hE i j) (inC_zC _ _)
      · have e : φ a = ∑ i, φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))
            + (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * φ a' := by
          refine (congrArg φ ha).trans ((φ.map_add _ _).trans ?_)
          refine congrArg₂ (· + ·) ((map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)) ?_
          · exact (φ.map_mul _ _).trans (congrArg (φ (letE i) * ·) (hO _))
          · exact (φ.map_mul _ _).trans (congrArg (· * φ a') hπ)
        rw [e, kap_add, kap_sum, kap_tmul_one_mul, h, pow_succ', mul_add, mul_assoc, add_assoc]
  intro a k
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hc
  obtain ⟨s, hs, r, hr, h⟩ := key N k a
  have hb : ‖(c : PadicComplex l) ^ N * r‖ ≤ ‖(c : PadicComplex l)‖ ^ N := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) hr
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · have e : s = kap o (φ a) k + -((c : PadicComplex l) ^ N * r) := by rw [h]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_kap_le _ _ _) ?_)
    rw [norm_neg]
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hc.le)
  · rw [dist_eq_norm, h, add_sub_cancel_left]
    exact hb.trans_lt hN

end GlobalTheory.Cyc.Decomp.Coord
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n] (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l), (∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a) → φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ‖(c : PadicComplex l)‖ < 1 → (c : PadicComplex l) ∈ inC (Ks K m) → (∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) → ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.Coord.coord
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem exists_map_eq_of_mem_sq_sup_pow {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (l N : ℕ) (π : A) (z u : B) (hπ : φ π = z) (hu : (l : B) = z * u) (a : A)
    (ha : a ∈ Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) :
    ∃ x y : B, φ a = (l : B) ^ 2 * x + z ^ N * y := by
  have hsub : Ideal.span {(l : B), z} ≤ Ideal.span {z} := by
    rw [Ideal.span_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · rw [SetLike.mem_coe, hu]
      exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mem_span_singleton_self z
  have hmap : Ideal.map φ (Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) ≤
      Ideal.span {(l : B) ^ 2, z ^ N} := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_pair]
    simp only [map_pow, map_natCast, hπ]
    refine sup_le (Ideal.span_mono (by simp)) ?_
    calc Ideal.span {(l : B), z} ^ N ≤ Ideal.span {z} ^ N := Ideal.pow_right_mono hsub N
      _ = Ideal.span {z ^ N} := Ideal.span_singleton_pow z N
      _ ≤ _ := Ideal.span_mono (by simp)
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp (hmap (Ideal.mem_map_of_mem φ ha))
  exact ⟨x, y, by rw [← hxy]; ring⟩

theorem norm_kap_lt_rho1_of_mem_sq_sup_pow :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  intro l _ LL j n f o φ ζ hj hζ hφ a ha k
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hζn : ‖(ζ : PadicComplex l) - 1‖ =
      (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) :=
    norm_primitiveRoot_sub_one l j hj _ hζ
  have hlnorm : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := norm_natCast_prime_padicComplex l
  have hz0 : (ζ : PadicComplex l) - 1 ≠ 0 := by
    rw [← norm_pos_iff, hζn]
    positivity
  have hle : ‖(l : PadicComplex l)‖ ≤ ‖(ζ : PadicComplex l) - 1‖ := by
    rw [hlnorm, hζn, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hl.le
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) := one_le_pow₀ hl.le
    have h2 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by nlinarith
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]
    exact h2
  let u : OC l := ⟨(l : PadicComplex l) / ((ζ : PadicComplex l) - 1), by
    rw [mem_OC, norm_div]
    exact div_le_one_of_le₀ hle (norm_nonneg _)⟩
  have hu : ((l : ℕ) : OC l) = (ζ - 1) * u := by
    apply Subtype.ext
    push_cast
    change (l : PadicComplex l) =
      ((ζ : PadicComplex l) - 1) * ((l : PadicComplex l) / ((ζ : PadicComplex l) - 1))
    field_simp
  have huO : ((l : ℕ) : OCO LL) =
      ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * (u ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hu,
      ← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]
  obtain ⟨x, y, hxy⟩ := exists_map_eq_of_mem_sq_sup_pow φ l (l ^ j) letπ _ _ hφ huO a ha
  have e1 : ((l : ℕ) : OCO LL) ^ 2 = (((l : ℕ) : OC l) ^ 2) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_pow, map_natCast]
  have e2 : ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) ^ (l ^ j) =
      ((ζ - 1) ^ (l ^ j)) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [hxy, kap_add, e1, e2, kap_tmul_one_mul, kap_tmul_one_mul]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hlnorm]
    calc ((l : ℝ)⁻¹) ^ 2 * ‖kap o x k‖ ≤ ((l : ℝ)⁻¹) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o x k) (by positivity)
      _ = (l : ℝ) ^ (-(2 : ℝ)) := by
          rw [mul_one, inv_pow, Real.rpow_neg (by positivity)]
          norm_cast
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl]
          have h3 : -1 ≤ -(1 : ℝ) / ((l : ℝ) - 1) := by
            rw [neg_div, neg_le_neg_iff, div_le_one hq]
            linarith
          linarith
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hζn]
    calc ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * ‖kap o y k‖
        ≤ ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o y k) (by positivity)
      _ = (l : ℝ) ^ (-(l : ℝ) / ((l : ℝ) - 1)) := by
          rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1
          have hp : (0 : ℝ) < (l : ℝ) ^ (j - 1) := by positivity
          have hpow : ((l ^ j : ℕ) : ℝ) = (l : ℝ) * (l : ℝ) ^ (j - 1) := by
            rw [Nat.cast_pow, ← pow_succ']
            congr 1
            omega
          rw [hpow]
          field_simp
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl, div_lt_div_iff_of_pos_right hq]
          linarith

end GlobalTheory.Cyc.Decomp
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_lt_rho1_of_mem_ideal_power : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.io_equivariant_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  first | exact @GlobalTheory.Cyc.Decomp.io_equivariant | exact GlobalTheory.Cyc.Decomp.io_equivariant | (intros; apply GlobalTheory.Cyc.Decomp.io_equivariant <;> assumption)
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

theorem card_eq_finrank_mul_card {Z O R T : Type} [CommRing Z] [Nontrivial Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing R] [Nontrivial R] [Algebra O R]
    [AddCommGroup T] [Module O T] [Module.Free O T] [Module Z T] [IsScalarTower Z O T]
    {d : ℕ} (b : Module.Basis (Fin d) Z T) {ι : Type} [Fintype ι] (v : ι → R ⊗[O] T)
    (h1 : LinearIndependent R v) (h2 : Submodule.span R (Set.range v) = ⊤) :
    d = Module.finrank Z O * Fintype.card ι := by
  have e1 : Module.finrank Z T = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have e2 : Module.finrank R (R ⊗[O] T) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk h1 h2.ge)
  rw [← e1, ← e2, Module.finrank_baseChange, Module.finrank_mul_finrank]

theorem nontrivial_tensor_of_free {Z O S : Type} [CommRing Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing S] [Nontrivial S] [Algebra Z S] :
    Nontrivial (O ⊗[Z] S) := by
  haveI : Module.FaithfullyFlat Z O := inferInstance
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem rank_count : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  intro l _ K LL T d M A ι _ v hM h1 h2
  haveI := freeOL LL
  haveI := finiteOL LL
  letI := zlMod LL T
  obtain ⟨b, -, -⟩ := hM
  haveI : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  haveI : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : Nontrivial (RW LL) := nontrivial_tensor_of_free
  have h := card_eq_finrank_mul_card (R := RW LL) b v h1 h2
  refine ⟨Module.finrank ℤ_[l] ↥(OL LL), Module.finBasis _ _, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simpa using h

end GlobalTheory.Cyc.Decomp
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_and_equiv_fin_prod_of_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.rank_count
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  first | exact @GlobalTheory.Cyc.Decomp.grp_GKs_H | exact GlobalTheory.Cyc.Decomp.grp_GKs_H | (intros; apply GlobalTheory.Cyc.Decomp.grp_GKs_H <;> assumption)
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_pow_n0_mul (l : ℕ) [hl : Fact l.Prime] (H : ℕ) : H ≤ l ^ (n0 l H) * (l - 1) := by
  unfold n0
  apply Nat.sInf_mem (s := {n | H ≤ l ^ n * (l - 1)})
  have h2 : 2 ≤ l := hl.out.two_le
  refine ⟨H, ?_⟩
  show H ≤ l ^ H * (l - 1)
  calc H ≤ l ^ H := (Nat.lt_pow_self (by omega : 1 < l)).le
    _ ≤ l ^ H * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem exists_prime_eq_mul_primitiveRoot_sub_one_pow (l : ℕ) [hl : Fact l.Prime] (H : ℕ)
    (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ (1 + n0 l H))) :
    ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hH : (H : ℝ) ≤ (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have h := le_pow_n0_mul l H
    have h1 : 1 ≤ l := hl.out.one_lt.le
    calc (H : ℝ) ≤ ((l ^ n0 l H * (l - 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by push_cast [Nat.cast_sub h1]; ring
  have hDpos : 0 < (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    positivity
  have hnorm := norm_primitiveRoot_sub_one l (1 + n0 l H) (by omega) ζ hζ
  rw [Nat.add_sub_cancel_left] at hnorm
  have hpos : 0 < ‖ζ - 1‖ := by rw [hnorm]; positivity
  have hne : ζ - 1 ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨(l : PadicComplex l) / (ζ - 1) ^ H, ?_, (div_mul_cancel₀ _ (pow_ne_zero H hne)).symm⟩
  rw [norm_div, norm_pow, norm_natCast_prime_padicComplex, div_le_one (pow_pos hpos H), hnorm,
    ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul, div_le_one hDpos]
  exact hH

end GlobalTheory.Cyc.Decomp
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' : ∀ (l : ℕ) [Fact l.Prime] (H : ℕ) (ζ : PadicComplex l), IsPrimitiveRoot ζ (l ^ (1 + n0 l H)) → ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  atlas_forward_decl GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow
end

section
namespace GlobalTheory

theorem sq_dvd_choose_prime_pow (l : ℕ) (hl : l.Prime) (b k : ℕ) (hb : 1 ≤ b) (hk0 : k ≠ 0)
    (hk : k < l ^ (b - 1)) : l ^ 2 ∣ (l ^ b).choose k := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨m, hm⟩ : ∃ m, l ^ b = m + 1 := Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'
  have hkb : j + 1 ≤ l ^ b := le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))
  have hC : (l ^ b).choose (j + 1) ≠ 0 := (Nat.choose_pos hkb).ne'

  have hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1) := by
    rw [hm]; exact Nat.add_one_mul_choose_eq m j

  have hv : padicValNat l (j + 1) < b - 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : l ^ padicValNat l (j + 1) ≤ j + 1 :=
      Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd
    have h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1) := Nat.pow_le_pow_right hl.pos hcon
    omega
  have hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1) := by
    rw [← hid]; exact dvd_mul_right _ _
  have hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0 := mul_ne_zero hC (Nat.succ_ne_zero j)
  rw [padicValNat_dvd_iff_le hne, padicValNat.mul hC (by omega : j + 1 ≠ 0)] at hdiv
  exact (padicValNat_dvd_iff_le hC).mpr (by omega)

theorem one_add_X_pow_prime_pow_sub_one_mem_span (l : ℕ) [Fact l.Prime] (b : ℕ) (hb : 1 ≤ b) :
    ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) ∈
      Ideal.span {((l : Polynomial ℤ)) ^ 2, Polynomial.X ^ (l ^ (b - 1))} := by

  have key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) =
      ∑ i ∈ Finset.range (l ^ b),
        Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i + 1 < l ^ (b - 1)
  ·
    obtain ⟨c, hc⟩ := sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  ·
    push_neg at hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end GlobalTheory
end

section
section
namespace GlobalTheory

theorem semilinear_sub_mem_pow_succ_smul {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N)
    (hx : x ∈ n ^ k • (⊤ : Submodule A N)) :
    Y x - x ∈ n ^ (k + 1) • (⊤ : Submodule A N) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have e : Y (a • y) - a • y = γ a • (Y y - y) + (γ a - a) • y := by
      rw [hY, smul_sub, sub_smul]; abel
    have hga : γ a ∈ n ^ k := by
      have h2 : γ a - a ∈ n ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) (hγ k a ha)
      simpa using (n ^ k).add_mem h2 ha
    rw [e]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul (hγ k a ha) trivial)
    rw [pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hga (h1 y)
  · intro y z hy hz
    have e : Y (y + z) - (y + z) = (Y y - y) + (Y z - z) := by
      rw [map_add]; abel
    rw [e]
    exact Submodule.add_mem _ hy hz

theorem semilinear_sub_one_pow_mem {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N) :
    ((Y.toIntLinearMap - 1 : Module.End ℤ N) ^ k) x ∈ n ^ k • (⊤ : Submodule A N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (Y.toIntLinearMap - 1 : Module.End ℤ N), Module.End.mul_apply]
    exact semilinear_sub_mem_pow_succ_smul n γ Y hY hγ h1 k _ ih

theorem semilinear_iterate_prime_pow_sub_mem :
    ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  intro l _ A N _ _ _ n γ Y hY hγ h1 b hb x
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (GlobalTheory.one_add_X_pow_prime_pow_sub_one_mem_span l b hb)
  set D : Module.End ℤ N := Y.toIntLinearMap - 1 with hD
  have h := congrArg (Polynomial.aeval D) huv
  rw [mul_comm u, mul_comm v] at h
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_natCast, Polynomial.aeval_X] at h
  have hYD : (1 + D) = Y.toIntLinearMap := by rw [hD]; abel
  rw [hYD] at h
  have h' := congrArg (fun f : Module.End ℤ N => f x) h
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] at h'
  have e : (Y.toIntLinearMap ^ (l ^ b)) x = Y^[l ^ b] x := by
    rw [Module.End.pow_apply]; rfl
  rw [e] at h'
  rw [← h']
  refine Submodule.add_mem _ ?_ ?_
  · have e2 : ∀ y : N, (((l : Module.End ℤ N)) ^ 2) y = ((l : A) ^ 2) • y := by
      intro y
      rw [← Nat.cast_pow, ← Nat.cast_pow, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    rw [e2]
    exact Submodule.smul_mem_smul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) trivial
  · exact Submodule.smul_mono_left le_sup_right
      (semilinear_sub_one_pow_mem n γ Y hY hγ h1 _ _)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  atlas_forward_decl GlobalTheory.semilinear_iterate_prime_pow_sub_mem
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.GamFilt

theorem sub_mem_pow_succ {A : Type*} [CommRing A] (f : A →+* A) (I : Ideal A)
    (h0 : ∀ a, f a - a ∈ I) (h1 : ∀ a ∈ I, f a - a ∈ I ^ 2) :
    ∀ k : ℕ, ∀ a ∈ I ^ k, f a - a ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro a _; simpa using h0 a
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      have hfy : f y ∈ I := by
        have := I.add_mem (h0 y) hy
        simpa using this
      have e : f (x * y) - x * y = (f x - x) * f y + x * (f y - y) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih x hx) hfy
      · rw [show k + 1 + 1 = k + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hx (h1 y hy)
    · intro x y hx hy
      have e : f (x + y) - (x + y) = (f x - x) + (f y - y) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ hx hy

theorem sub_mem_pow_succ_pair {A : Type*} [CommRing A] (f : A →+* A) (p t : A)
    (h0 : ∀ a, f a - a ∈ Ideal.span {p, t}) (hp : f p = p)
    (ht : f t - t ∈ Ideal.span {p, t} ^ 2) :
    ∀ k : ℕ, ∀ a ∈ Ideal.span {p, t} ^ k, f a - a ∈ Ideal.span {p, t} ^ (k + 1) := by
  refine sub_mem_pow_succ f _ h0 ?_
  intro y hy
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  have e : f (a * p + b * t) - (a * p + b * t) =
      (f a - a) * p + (f b - b) * t + f b * (f t - t) := by
    rw [map_add, map_mul, map_mul, hp]; ring
  rw [e]
  have hpm : p ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  have htm : t ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ ht)
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 a) hpm
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 b) htm

theorem X_dvd_sub {O : Type*} [CommRing O] (g : PowerSeries O →ₐ[O] PowerSeries O)
    (hg : PowerSeries.constantCoeff (g PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.X ∣ g a - a := by
  have h1 : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  obtain ⟨b, hb⟩ := h1
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_apply]; simp
  rw [PowerSeries.X_dvd_iff, ha, map_add, AlgHom.commutes, map_mul]
  simp [hg]

theorem exists_X_sub {O : Type*} [CommRing O] (F : PowerSeries O) (p : ℕ) (c : O)
    (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = 1 + p * c) :
    ∃ h : PowerSeries O, F - PowerSeries.X =
      PowerSeries.X * ((p : PowerSeries O) * PowerSeries.C c + PowerSeries.X * h) := by
  have : PowerSeries.X ^ 2 ∣ F - PowerSeries.X - PowerSeries.X * (PowerSeries.C ((p : O) * c)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [h0]
    · rw [map_sub, map_sub, h1, PowerSeries.coeff_succ_X_mul]
      simp
  obtain ⟨h, hh⟩ := this
  refine ⟨h, ?_⟩
  rw [map_mul, map_natCast] at hh
  linear_combination hh

theorem letγ_sub_mem {O : Type} [CommRing O] {n : ℕ} (g : PowerSeries O →ₐ[O] PowerSeries O) (p : ℕ)
    (c : O) (h0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (g PowerSeries.X) = 1 + p * c) :
    ∀ k : ℕ, ∀ a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ k,
      letγ g a - a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ (k + 1) := by
  have hpm : ((p : ℕ) : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  have htm : (letπ : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  refine sub_mem_pow_succ_pair (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom _ _ ?_ (map_natCast _ _) ?_
  · intro a
    choose b hb using fun i => X_dvd_sub g h0 (a i)
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom a - a = letπ * b := funext hb
    rw [e]
    exact Ideal.mul_mem_right _ _ htm
  · obtain ⟨h, hh⟩ := exists_X_sub _ p c h0 h1
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom letπ - letπ =
        letπ * (((p : ℕ) : LetA O n) * (fun _ => PowerSeries.C c) + letπ * (fun _ => h)) :=
      funext fun _ => hh
    rw [e, pow_two]
    exact Ideal.mul_mem_mul htm (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpm)
      (Ideal.mul_mem_right _ _ htm))

theorem exists_eq_one_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (u : ↥(OL LL))
    (hu : (1 : WithTop ℚ) ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 u - 1)) :
    ∃ c : ↥(OL LL), u = 1 + (l : ↥(OL LL)) * c := by
  have hl : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := (algebraMap ↥(OL LL) ↥LL.1 u - 1) / (l : ↥LL.1) with hy
  have e : algebraMap ↥(OL LL) ↥LL.1 u - 1 = (l : ↥LL.1) * y := by
    rw [hy]; field_simp
  rw [e, AddValuation.map_mul, P.v_l] at hu
  have h0 : 0 ≤ P.v LL y := by
    have : (1 : WithTop ℚ) + 0 ≤ 1 + P.v LL y := by simpa using hu
    exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).1 this
  refine ⟨⟨y, (P.v_O LL y).1 h0⟩, Subtype.ext ?_⟩
  have : (u : ↥LL.1) - 1 = (l : ↥LL.1) * y := e
  push_cast
  linear_combination this

theorem gamma_sub_mem_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h W g hg
  have h1 := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at h1
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := exists_eq_one_add (D.loc l) LL _ (hs.trans h1)
  exact letγ_sub_mem (W.γ₀ (W.resΓ g)) l c (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)

end GlobalTheory.GamFilt
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaAction_sub_mem_span_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  atlas_forward_decl GlobalTheory.GamFilt.gamma_sub_mem_pow_succ
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  first | exact @GlobalTheory.Cyc.isMat_exists_and_props | exact GlobalTheory.Cyc.isMat_exists_and_props | (intros; apply GlobalTheory.Cyc.isMat_exists_and_props <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_sandwich_Ainf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD T)), WClauses S E T M0 h0 N → (∀ y ∈ N, (S.inclR (E.io S.W.X)) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T)) ∧ ∀ t : ↥T.L.T, (S.inclR (E.io S.W.X)) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈ Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y} := by
  first | exact @GlobalTheory.Sandwich.sandwich | exact GlobalTheory.Sandwich.sandwich | (intros; apply GlobalTheory.Sandwich.sandwich <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

section Lift

variable (S : Sit) (E : S.Comparison₂) (T : LocLat S.G S.Qp S.LL S.O)
  (N : Submodule (LetA S.O S.n) (S.W.DD T))

theorem jD_smulA (a : LetA S.O S.n) (y : S.W.DD T) :
    E.jD T (a • y) = S.inclR (E.io a) • E.jD T y := by
  rw [← E.ioE_ext, ← E.jD_smul, algebraMap_smul]

theorem γD_smulA (g : S.W.Gam) (a : LetA S.O S.n) (y : S.W.DD T) :
    S.W.γD T g (a • y) = S.W.γA g a • S.W.γD T g y := by
  have := S.W.γD_smul T g (algebraMap (LetA S.O S.n) S.W.EE a) y
  rw [algebraMap_smul, S.W.γE_ext, algebraMap_smul] at this
  exact this

theorem exists_lift (x : S.RA) (M0 h0 : ℕ) (hinj : Function.Injective S.inclR)
    (h1 : ∀ y ∈ N, (S.inclR x) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T))
    (h2 : ∀ t : ↥T.L.T, (S.inclR x) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈
      Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y}) :
    ∃ z : ↥N →+ TW S.RA T, (∀ (a : LetA S.O S.n) (y : ↥N), z (a • y) = E.io a • z y) ∧
      (∀ (g : S.G) (u : S.RA →ₐ[S.O] S.RA), (∀ r, S.inclR (u r) = S.gR g (S.inclR r)) →
        ∀ y y' : ↥N, (y' : S.W.DD T) = S.W.γD T (S.W.resΓ g) y →
          x ^ M0 • TWact u T g (z y) = u x ^ M0 • z y') ∧
      ∀ t : ↥T.L.T, x ^ (M0 + h0) • ((1 : S.RA) ⊗ₜ[S.O] t) ∈
        AddSubgroup.closure {w : TW S.RA T | ∃ (r : S.RA) (y : ↥N), w = r • z y} := by
  have hi := TWincl_injective S.inclR hinj T
  choose z hz using fun y : ↥N => LinearMap.mem_range.1 (h1 y y.2)
  refine ⟨AddMonoidHom.mk' z (fun y y' => hi ?_), fun a y => hi ?_, fun g u hu y y' hy => hi ?_,
    fun t => ?_⟩
  · rw [map_add, hz, hz, hz, Submodule.coe_add, map_add, smul_add]
  · rw [AddMonoidHom.mk'_apply, TWincl_smul, hz, hz, Submodule.coe_smul,
      jD_smulA, smul_comm]
  · rw [AddMonoidHom.mk'_apply, TWincl_smul, TWincl_smul,
      TWincl_act S.inclR u (S.gR g) hu, hz, hz, TWact_smul, hy, E.jD_act, map_pow, map_pow, map_pow,
      hu, smul_comm]
  · have key : ∀ v ∈ Submodule.span S.O
        {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y}, ∀ r : S.RA,
        ∃ w ∈ AddSubgroup.closure {w : TW S.RA T | ∃ (r : S.RA) (y : ↥N), w = r • z y},
          TWincl S.inclR T w = S.inclR r • S.inclR x ^ M0 • v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, y, hy, rfl⟩ := hv
        intro r
        refine ⟨(r * a) • z ⟨y, hy⟩, AddSubgroup.subset_closure ⟨_, _, rfl⟩, ?_⟩
        rw [TWincl_smul, hz, map_mul, mul_smul, smul_comm (S.inclR a)]
      | zero => intro r; exact ⟨0, zero_mem _, by simp⟩
      | add v v' _ _ ih ih' =>
        intro r
        obtain ⟨w, hw, e⟩ := ih r
        obtain ⟨w', hw', e'⟩ := ih' r
        exact ⟨w + w', add_mem hw hw', by rw [map_add, e, e', smul_add, smul_add]⟩
      | smul c v _ ih =>
        intro r
        obtain ⟨w, hw, e⟩ := ih (r * algebraMap S.O S.RA c)
        refine ⟨w, hw, ?_⟩
        rw [e, map_mul, AlgHom.commutes, mul_smul, ← algebraMap_smul S.RW c v,
          smul_comm (S.inclR x ^ M0)]
    obtain ⟨w, hw, e⟩ := key _ (h2 t) 1
    have : x ^ (M0 + h0) • ((1 : S.RA) ⊗ₜ[S.O] t) = w := by
      apply hi
      rw [e, TWincl_smul, TWincl_one_tmul, map_one, one_smul, map_pow, pow_add, mul_smul]
    rw [this]
    exact hw

theorem γD_iterate (g : S.W.Gam) (k : ℕ) (y : S.W.DD T) :
    (S.W.γD T g)^[k] y = S.W.γD T (g ^ k) y := by
  induction k with
  | zero => simp [S.W.γD_one]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', S.W.γD_mul]

theorem γD_pow_sub (l : ℕ) [Fact l.Prime] (g : S.W.Gam)
    (hN : ∀ x ∈ N, S.W.γD T g x ∈ N)
    (hπ : ∀ x ∈ N, S.W.γD T g x - x ∈ (Ideal.span {(letπ : LetA S.O S.n)}) • N)
    (hA : ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ k,
      S.W.γA g a - a ∈ (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ (k + 1))
    (j : ℕ) (y : ↥N) :
    ∃ y' : ↥N, (y' : S.W.DD T) = S.W.γD T (g ^ l ^ (j + 1)) y ∧
      y' - y ∈ (Ideal.span {((l : ℕ) : LetA S.O S.n) ^ 2} ⊔
        (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ (l ^ j)) • (⊤ : Submodule (LetA S.O S.n) ↥N) := by
  let Y : ↥N →+ ↥N := AddMonoidHom.mk' (fun x => ⟨S.W.γD T g x, hN x x.2⟩)
    (fun x x' => Subtype.ext (by simp))
  have hY : ∀ k (x : ↥N), ((Y^[k] x : ↥N) : S.W.DD T) = (S.W.γD T g)^[k] x := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
  refine ⟨Y^[l ^ (j + 1)] y, by rw [hY, γD_iterate], ?_⟩
  refine GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration l (LetA S.O S.n) ↥N _ (S.W.γA g).toRingHom Y
    (fun a x => Subtype.ext (γD_smulA S T g a x)) hA (fun x => ?_) (j + 1) (by omega) y
  rw [Submodule.mem_smul_top_iff]
  exact Submodule.smul_mono_left (Ideal.span_mono (by simp)) (hπ x x.2)

theorem one_add_X : 1 + S.W.X = (1 + letπ) ^ (S.PD.p ^ (S.W.s - 1)) := by
  have h1 : S.W.φA (1 + letπ) = (1 + letπ) ^ S.PD.p := by
    rw [map_add, map_one, S.W.φA_π]
    funext i
    simp [letπ, LocWach.q, S.W.q₀_def]
  have h2 : ∀ k, (S.W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (S.PD.p ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgHom.mul_apply, h1, map_pow, ih, ← pow_mul, pow_succ]
  rw [← h2, map_add, map_one]
  rfl

theorem γA_letE (g : S.W.Gam) (i : ZMod S.n) : S.W.γA g (letE i) = letE i := by
  funext j
  change S.W.γ₀ g (letE (O := S.O) i j) = letE (O := S.O) i j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

end Lift

section Assemble

variable {l : ℕ} [Fact l.Prime]

theorem assemble (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (K LL : FinExt l) (m d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l))
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (R N ι : Type) [CommRing R] [AddCommGroup N]
    [Module R N] [Fintype ι] (b : Module.Basis ι R N) (e : Fin d ≃ Fin f × ι) (α : ↥(OL LL) → R)
    (φ : R →+* OCO LL) (Ψ : N →+ (Fin d → PadicComplex l)) (J : Ideal R) (g : GQ l)
    (hact : IsActC act) (hgen : IsGen χ K m g)
    (hM1 : ∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m))
    (hM2 : ∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ)
    (hM3 : ∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ)
    (hΨ : ∀ a y, Ψ (a • y) = (lam o A (φ a)).mulVec (Ψ y))
    (hα : ∀ a, lam o A (φ (α a)) = A a)
    (hc : ∀ a k, kap o (φ a) k ∈ intC (Ks K m))
    (hs : ∀ a ∈ J, ∀ k, ‖kap o (φ a) k‖ < rho1 l)
    (hn : ∀ y i, ‖Ψ y i‖ ≤ 1)
    (hσ : ∀ σ ∈ Gj K m, ∀ y, ∃ y', Ψ y' = (M σ).mulVec (fun i => act σ (Ψ y i)))
    (hH : ∀ σ ∈ Hinf K, ∀ y, Ψ y = (M σ).mulVec (fun i => act σ (Ψ y i)))
    (hg : ∀ y, ∃ y', y' - y ∈ J • (⊤ : Submodule R N) ∧
      Ψ y' = (M g).mulVec (fun i => act g (Ψ y i)))
    (c u : PadicComplex l) (hu : ‖u‖ ≤ 1) (hcu : (l : PadicComplex l) = u * c)
    (hl : ∀ j, c • (Pi.single j 1 : Fin d → PadicComplex l) ∈
      AddSubgroup.closure {v | ∃ (x : OCO LL) (y : N), v = (lam o A x).mulVec (Ψ y)}) :
    ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l))
      (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec act χ K m M Dm U g ∧
      ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K m) := by
  classical
  let y₀ : Fin d → N := fun j => α (o (e j).1) • b (e j).2
  let D : Matrix (Fin d) (Fin d) (PadicComplex l) := Matrix.of fun i j => Ψ (y₀ j) i
  let co : N → Fin d → PadicComplex l := fun y j => kap o (φ (b.repr y (e j).2)) (e j).1
  have hA : ∀ a y, Ψ (α a • y) = (A a).mulVec (Ψ y) := fun a y => by rw [hΨ, hα]
  have core : ∀ y, Ψ y = D.mulVec (co y) := by
    intro y
    conv_lhs => rw [← b.sum_repr y, map_sum]
    have h1 : D.mulVec (co y) = ∑ j, co y j • Ψ (y₀ j) := by
      funext i
      simp [D, Matrix.mulVec, dotProduct, mul_comm]
    have h2 : ∑ j, co y j • Ψ (y₀ j) = ∑ p : Fin f × ι,
        kap o (φ (b.repr y p.2)) p.1 • Ψ (α (o p.1) • b p.2) :=
      Equiv.sum_comp e (fun p : Fin f × ι => kap o (φ (b.repr y p.2)) p.1 • Ψ (α (o p.1) • b p.2))
    rw [h1, h2, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΨ, lam, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, Matrix.smul_mulVec]
  have cols : ∀ (B : Matrix (Fin d) (Fin d) (PadicComplex l)) (v : Fin d → Fin d → PadicComplex l),
      (∀ j, (fun i => B i j) = D.mulVec (v j)) → B = D * Matrix.of fun i j => v j i := by
    intro B v h
    ext i j
    exact congrFun (h j) i
  have hball : ∀ v ∈ AddSubgroup.closure
      {v | ∃ (x : OCO LL) (y : N), v = (lam o A x).mulVec (Ψ y)},
      ∃ w : Fin d → PadicComplex l, (∀ i, ‖w i‖ ≤ 1) ∧ v = D.mulVec w := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨x, y, rfl⟩ := hv
      refine ⟨∑ k, kap o x k • co (α (o k) • y), fun i => ?_, ?_⟩
      · rw [Finset.sum_apply]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_one₀ (norm_kap_le _ _ _) (norm_nonneg _) (norm_kap_le _ _ _)
      · rw [lam, Matrix.sum_mulVec, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← core, hA]
    | zero => exact ⟨0, by simp, by simp⟩
    | add v v' _ _ ih ih' =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨w', hw', rfl⟩ := ih'
      exact ⟨w + w', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hw i) (hw' i)),
        (Matrix.mulVec_add _ _ _).symm⟩
    | neg v _ ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      exact ⟨-w, fun i => by simpa using hw i, (Matrix.mulVec_neg _ _).symm⟩
  have hcol : ∀ σ j, (fun i => (M σ * D.map (act σ)) i j) =
      (M σ).mulVec (fun i => act σ (Ψ (y₀ j) i)) := fun σ j => rfl
  obtain ⟨U, hU⟩ := GlobalTheory.T.decompletion_frame_of_matrix_form l act χ K m d M D g hact hgen hM1 hM2 hM3 (fun i j => hn _ _)
    (by
      choose w hw hw' using fun j => hball _ (hl j)
      refine ⟨Matrix.of fun i j => (u • w j) i, fun i j => ?_, (cols _ _ fun j => ?_).symm⟩
      · rw [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_one₀ hu (norm_nonneg _) (hw j i)
      · rw [Matrix.mulVec_smul, ← hw', smul_smul, ← hcu]
        funext i
        simp [Matrix.one_apply, Pi.single_apply])
    (fun σ hσ' => by
      choose y' hy' using fun j => hσ σ hσ' (y₀ j)
      exact ⟨Matrix.of fun i j => co (y' j) i, fun i j => hc _ _,
        cols _ _ fun j => by rw [hcol, ← hy', core]⟩)
    (fun σ hσ' => by
      ext i j
      exact (congrFun (hcol σ j) i).trans (congrFun (hH σ hσ' (y₀ j)).symm i))
    (by
      choose y' hy hy' using fun j => hg (y₀ j)
      refine ⟨Matrix.of fun i j => co (y' j - y₀ j) i, fun i j => hs _ ?_ _, cols _ _ fun j => ?_⟩
      · have := hy j
        generalize y' j - y₀ j = x at this
        refine Submodule.smul_induction_on this (fun r hr n _ => ?_) (fun x y hx hy => ?_)
        · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
          exact J.mul_mem_right _ hr
        · rw [map_add, Finsupp.add_apply]
          exact J.add_mem hx hy
      · rw [← core, map_sub, hy', ← hcol]
        rfl)
  refine ⟨D, U, g, hU, fun a i j => ?_⟩
  have h1 : A a * D = D * Matrix.of fun i j => co (α a • y₀ j) i :=
    cols _ _ fun j => by rw [← core, hA]; rfl
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU.1, Matrix.one_mul]
  exact hc _ _

end Assemble

section Roots

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem zeta_pow (j k : ℕ) : AI.ζ (j + k) ^ l ^ k = AI.ζ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem zeta_prim (j : ℕ) (hj : 1 ≤ j) :
    IsPrimitiveRoot ((AI.ζ j : OC l) : PadicComplex l) (l ^ j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hnot : ¬ AI.ζ (1 + i) ^ l ^ i = 1 := by rw [zeta_pow]; exact AI.ζ_one
  have hfin : AI.ζ (1 + i) ^ l ^ (i + 1) = 1 := by
    rw [pow_succ, pow_mul, zeta_pow, AI.ζ_succ 0, AI.ζ_zero]
  have h := IsPrimitiveRoot.orderOf (AI.ζ (1 + i))
  rw [orderOf_eq_prime_pow hnot hfin, add_comm i 1] at h
  exact h.map_of_injective (f := (PadicComplexInt l).subtype) Subtype.val_injective

include AI in
theorem zetaQ_mem (K : FinExt l) {j m : ℕ} (hj : j ≤ m) : P.ζQ j ∈ Ks K m := by
  refine AlmostTrace.Ks_mono K hj ?_
  refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
  change P.ζQ j ^ l ^ j = 1
  apply (algebraMap (Om l) (PadicComplex l)).injective
  have h := congrArg (fun x : OC l => (x : PadicComplex l)) (zeta_pow AI 0 j)
  rw [map_pow, map_one, ← PadicComplex.coe_eq, ← AI.ζ_eq]
  simpa [AI.ζ_zero] using h

theorem act_zeta (K : FinExt l) {j m : ℕ} (hj : j ≤ m) (σ : GQ l) (hσ : σ ∈ Gj K m) :
    AI.actC σ ((AI.ζ j : OC l) : PadicComplex l) = ((AI.ζ j : OC l) : PadicComplex l) := by
  rw [AI.ζ_eq, AI.actC_ext]
  exact congrArg _ (hσ ⟨_, zetaQ_mem AI K hj⟩)

theorem zeta_sub_one_mem (K : FinExt l) {j m : ℕ} (hj : j ≤ m) :
    ((AI.ζ j - 1 : OC l) : PadicComplex l) ∈ inC (Ks K m) := by
  refine ⟨P.ζQ j - 1, sub_mem (zetaQ_mem AI K hj) (one_mem _), ?_⟩
  change algebraMap (Om l) (PadicComplex l) (P.ζQ j - 1) = ((AI.ζ j : OC l) : PadicComplex l) - 1
  rw [map_sub, map_one, AI.ζ_eq]
  rfl

theorem norm_zeta_sub_one_lt (j : ℕ) (hj : 1 ≤ j) :
    ‖((AI.ζ j - 1 : OC l) : PadicComplex l)‖ < 1 := by
  change ‖((AI.ζ j : OC l) : PadicComplex l) - 1‖ < 1
  rw [GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj _ (zeta_prim AI j hj)]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  apply Real.rpow_lt_one_of_one_lt_of_neg hl
  apply div_neg_of_neg_of_pos (by norm_num)
  exact mul_pos (pow_pos (by linarith) _) (by linarith)

theorem tmul_one_pow (LL : FinExt l) (c : OC l) (k : ℕ) :
    (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) : OCO LL) ^ k = (c ^ k) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow]

theorem one_add_pow_sub (LL : FinExt l) (w : Ainf l) (k : ℕ) :
    (1 + ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w - 1) : RA LL)) ^ k =
      1 + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w ^ k - 1) := by
  have h : ∀ v : Ainf l, (1 + ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (v - 1) : RA LL)) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] v := fun v => by
    rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_add, add_sub_cancel]
  rw [h, h, Algebra.TensorProduct.tmul_pow, one_pow]

end Roots

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem exists_decompletion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec (D.locA l).actC (D.loc l).χQ K (mN l s (M0 + h0)) M Dm U g ∧ ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K (mN l s (M0 + h0))) := by
  intro D HW F l _ K s LL h S E T M0 h0 hW d M A hM
  obtain ⟨-, -, N, hN⟩ := hW
  obtain ⟨hsw1, hsw2⟩ := GlobalTheory.T.wach_lattice_sandwich_Ainf D HW F l K s LL h T M0 h0 N hN
  obtain ⟨⟨ι, _, b, hli, hsp⟩, -, -, hW2, hW3, -⟩ := hN
  obtain ⟨f, o, ⟨e⟩⟩ := GlobalTheory.T.exists_basis_and_equiv_fin_prod_of_basis l K LL T d M A ι _ hM hli hsp
  generalize hn : n0 l (M0 + h0) = n
  have hm : mN l s (M0 + h0) = s + (s + n + 1) := by rw [mN, hn]; ring
  generalize mN l s (M0 + h0) = m at hm ⊢
  have hs1 : 1 ≤ s := h.1
  let AI := D.locA l
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hcyc : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_fontaineTheta_frobeniusInverse_shift l (D.loc l) AI n
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := GlobalTheory.T.exists_ainf_tensor_lattice_specialisation l (D.loc l) AI K LL T d f n M A o θ hM hθ
  obtain ⟨hl1, hA1, -, -⟩ := GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative l K LL T d f M A o hM
  obtain ⟨hM1, hM2, -, -⟩ := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).2 d M A hM
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_lift S E T N (E.io S.W.X) M0 h0 (inclR_injective LL) hsw1 hsw2
  have hgrp := GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups l (D.loc l) AI K s LL h ((HW l).W K s LL h) ((HW l).W_s K s LL h)
  have hGs : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_antitone h.2.2.1
  have hms : Gj K m ≤ Gj K s :=
    IntermediateField.fixingSubgroup_antitone (AlmostTrace.Ks_mono K (by omega))
  obtain ⟨⟨g₀, hg₀⟩, hgen⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l AI.actC (D.loc l).χQ hact hcyc K s ⟨h.1, h.2.1⟩
  have hg := (hgen g₀ hg₀).1 (s + n + 1)
  rw [← hm] at hg
  let φ : LetA S.O S.n →+* OCO LL := (thR LL θ).comp E.io.toRingHom
  have hφ : ∀ a, φ a = thR LL θ (E.io a) := fun a => rfl
  have hφa : ∀ a : ↥(OL LL), φ (algebraMap S.O (LetA S.O S.n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a := by
    intro a
    exact (congrArg (thR LL θ) (E.io.commutes a)).trans ((thR_tmul LL θ a 1).trans (by rw [map_one]))
  have hφπ : φ letπ = (AI.ζ (s + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [hφ, E.io_π]
    exact (thR_tmul LL θ 1 _).trans (by rw [map_sub, map_one, hθ.2])
  let w : Ainf l := WittVector.teichmuller l (AI.εroot s) ^ l ^ (s - 1) - 1
  have hx : E.io S.W.X = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RA LL) := by
    have h1 := congrArg E.io (one_add_X S)
    have h2 : S.PD.p = l := (D.loc l).PD_p K
    have h3 : S.W.s = s := (HW l).W_s K s LL h
    rw [map_add, map_one, map_pow, map_add, map_one, E.io_π, h2, h3] at h1
    exact add_left_cancel (h1.trans (one_add_pow_sub LL _ _))
  have hθw : θ w = AI.ζ (1 + n) - 1 := by
    rw [map_sub, map_one, map_pow, hθ.2, show s + n = (1 + n) + (s - 1) by omega, zeta_pow]
  let c : PadicComplex l := ((AI.ζ (1 + n) : OC l) : PadicComplex l) - 1
  have hprim := zeta_prim AI (1 + n) (by omega)
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' l (M0 + h0) _ (by rw [hn]; exact hprim)
  have hc0 : c ≠ 0 := sub_ne_zero.2 (hprim.ne_one
    (Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt))
  have hsc : ∀ (r : RA LL) (k : ℕ) (v : TW (RA LL) (show LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) from T)),
      thR LL θ r = (AI.ζ (1 + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → Φ (r ^ k • v) = c ^ k • Φ v := by
    intro r k v hr
    rw [hΦ1, map_pow, hr, tmul_one_pow, hl1, hA1, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  let x : RA LL := E.io S.W.X
  have hx' : x = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w := hx
  have hx1 : thR LL θ x = (AI.ζ (1 + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [hx', thR_tmul, hθw]
  have hx2 : ∀ σ ∈ Gj K m, thR LL θ (gRA AI LL σ x) =
      (AI.ζ (1 + n) - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    intro σ hσ
    have h1 : θ (AI.actWHom σ w) = AI.ζ (1 + n) - 1 := by
      apply Subtype.ext
      rw [hθ.1, hθw]
      change AI.actC σ (((AI.ζ (1 + n) : OC l) : PadicComplex l) - 1) =
        ((AI.ζ (1 + n) : OC l) : PadicComplex l) - 1
      rw [map_sub, map_one, act_zeta AI K (by omega) σ hσ]
    rw [hx', ← h1]
    rfl
  let Ψ : ↥N →+ (Fin d → PadicComplex l) := Φ.comp z
  have hΨ : ∀ y, Ψ y = Φ (z y) := fun y => rfl
  have hmain : ∀ (σ : ↥(GK K)), (σ : GQ l) ∈ Gj K m → ∀ y y' : ↥N,
      (y' : S.W.DD T) = S.W.γD T (S.W.resΓ σ) y →
      Ψ y' = (M σ).mulVec (fun i => AI.actC σ (Ψ y i)) := by
    intro σ hσ y y' hy
    have h1 := congrArg Φ (hz2 σ (gRA AI LL σ) (inclR_gRA AI LL σ) y y' hy)
    have h2 := (hsc _ M0 _ hx1).symm.trans (h1.trans (hsc _ M0 _ (hx2 σ hσ)))
    have h3 := smul_right_injective (Fin d → PadicComplex l) (pow_ne_zero M0 hc0) h2
    exact h3.symm.trans (hΦ3 σ (z y))
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    haveI := K.2
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hidem : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m) := by
    intro i k
    have h1 : IsIdempotentElem (letE i : LetA S.O S.n) := by
      change letE i * letE i = letE i
      rw [letE, ← Pi.single_mul, mul_one]
    have h2 := GlobalTheory.T.kap_mem_inC_of_invariant l AI.actC K LL f o (φ (letE i)) hact (h1.map φ) (fun σ hσ k => by
      have h3 := GlobalTheory.T.io_equivariant_alt l (D.loc l) AI K s LL h _ ((F l).E K s LL h) ⟨σ, hσ⟩ (letE i)
      let r : RA LL := E.io (letE i)
      have h4 : gRA AI LL σ r = r := by
        apply inclR_injective LL
        rw [inclR_gRA]
        exact h3.symm.trans (congrArg (fun a => inclR LL (E.io a)) (γA_letE S _ i))
      exact (kap_thR_gRA AI o hθ σ _ k).symm.trans
        (congrArg (fun r => kap o (thR LL θ r) k) h4)) k
    exact Set.image_mono (h.2.2.1.trans (AlmostTrace.Ks_mono K (show s ≤ m by omega))) h2
  refine assemble AI.actC (D.loc l).χQ K LL m d f M A o (LetA S.O S.n) ↥N ι b e
    (algebraMap S.O (LetA S.O S.n)) φ Ψ
    (Ideal.span {((l : ℕ) : LetA S.O S.n) ^ 2} ⊔
      (Ideal.span {((l : ℕ) : LetA S.O S.n), letπ}) ^ (l ^ (s + n))) (g₀ ^ l ^ (s + n + 1)) hact hg
    (fun i j => (hM1 i j).mono fun σ hσ => hGs (hms hσ))
    (fun σ hσ τ hτ => hM2 σ (hGs (hms hσ)) τ (hGs (hms hτ))) (fun σ _ τ hτ => ?_)
    (fun a y => ?_) (fun a => ?_)
    (GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries l K LL m (Module.finrank ℚ_[l] ↥(K0 K)) f o φ _ hφa hφπ (norm_zeta_sub_one_lt AI _ (by omega))
      (zeta_sub_one_mem AI K (by omega)) hidem)
    (GlobalTheory.T.norm_lt_rho1_of_mem_ideal_power l LL (s + n) _ f o φ _ (by omega) (zeta_prim AI _ (by omega)) hφπ)
    (fun y i => hΦ2 _ i) (fun σ hσ y => ?_) (fun σ hσ y => ?_) (fun y => ?_)
    (c ^ (M0 + h0)) u hu hlu (fun j => ?_)
  · obtain ⟨b', hb', -⟩ := hM
    ext i j
    have := hb' ⟨τ, hGs (hms hτ)⟩ i j
    rw [Matrix.map_apply]
    exact (congrArg _ this).trans ((act_zC hact σ _).trans this.symm)
  · exact (congrArg Φ (hz1 a y)).trans (hΦ1 _ _)
  · rw [hφa, hl1]
    exact one_smul _ _
  · exact ⟨⟨_, hW2 ⟨σ, hGs (hms hσ)⟩ ((hgrp _).1 (hms hσ)) y y.2⟩, hmain ⟨σ, hGs (hms hσ)⟩ hσ y _ rfl⟩
  · have hσ' := AlmostTrace.Hinf_le_Gj K m hσ
    refine hmain ⟨σ, hGs (hms hσ')⟩ hσ' y y ?_
    have h1 : S.W.resΓ ⟨σ, hGs (hms hσ')⟩ = 1 := (hgrp _).2 hσ
    rw [h1, S.W.γD_one]
  · have h1 : (⟨g₀, hGs hg₀.1⟩ : ↥(GK K)) ∈ S.W.GKs := (hgrp _).1 hg₀.1
    obtain ⟨y', hy', hy''⟩ := γD_pow_sub S T N l (S.W.resΓ ⟨g₀, hGs hg₀.1⟩) (hW2 _ h1) (hW3 _ h1)
      (GlobalTheory.T.gammaAction_sub_mem_span_pow_succ D HW l K s LL h _ h1) (s + n) y
    refine ⟨y', hy'', hmain ((⟨g₀, hGs hg₀.1⟩ : ↥(GK K)) ^ l ^ (s + n + 1)) hg.1 y y' ?_⟩
    exact hy'.trans (congrArg (fun γ => S.W.γD T γ y) (S.W.resΓ.map_pow _ _).symm)
  · obtain ⟨t, ht⟩ := hΦ4 j
    rw [← ht, ← hsc _ _ _ hx1]
    have h1 : ∀ v ∈ AddSubgroup.closure {w : TW S.RA T | ∃ (r : S.RA) (y : ↥N), w = r • z y},
        Φ v ∈ AddSubgroup.closure
          {v | ∃ (x : OCO LL) (y : ↥N), v = (lam o A x).mulVec (Ψ y)} := by
      intro v hv
      induction hv using AddSubgroup.closure_induction with
      | mem v hv =>
        obtain ⟨r, y, rfl⟩ := hv
        exact AddSubgroup.subset_closure ⟨thR LL θ r, y, hΦ1 r (z y)⟩
      | zero => exact (Φ.map_zero).symm ▸ zero_mem _
      | add v v' _ _ ih ih' => exact (Φ.map_add v v').symm ▸ add_mem ih ih'
      | neg v _ ih => exact (Φ.map_neg v).symm ▸ neg_mem ih
    exact h1 _ (hz3 t)

end GlobalTheory.Cyc.Decomp
end
end
