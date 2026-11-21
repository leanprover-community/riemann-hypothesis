import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice

section
namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

section Core

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem core_inner_self_im (h : InnerProductSpace.Core ℂ V) (x : V) : (h.inner x x).im = 0 := by
  have := h.conj_inner_symm x x
  exact Complex.conj_eq_iff_im.mp this

theorem core_eq_zero_of_re (h : InnerProductSpace.Core ℂ V) (x : V)
    (hx : (h.inner x x).re = 0) : x = 0 :=
  h.definite x (Complex.ext hx (core_inner_self_im h x))

@[instance_reducible]
def coreComap (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    InnerProductSpace.Core ℂ V where
  inner x y := h.inner (f x) (f y)
  conj_inner_symm x y := h.conj_inner_symm (f x) (f y)
  re_inner_nonneg x := h.re_inner_nonneg (f x)
  add_left x y z := by simp only [map_add, h.add_left]
  smul_left x y r := by simp only [map_smul, h.smul_left]
  definite x hx := hf (by rw [map_zero]; exact h.definite _ hx)

theorem coreComap_inner (h : InnerProductSpace.Core ℂ W) (f : V →ₗ[ℂ] W)
    (hf : Function.Injective f) (x y : V) :
    (coreComap h f hf).inner x y = h.inner (f x) (f y) := rfl

@[instance_reducible]
def coreProd (hV : InnerProductSpace.Core ℂ V) (hW : InnerProductSpace.Core ℂ W) :
    InnerProductSpace.Core ℂ (V × W) where
  inner x y := hV.inner x.1 y.1 + hW.inner x.2 y.2
  conj_inner_symm x y := by
    rw [map_add, hV.conj_inner_symm, hW.conj_inner_symm]
  re_inner_nonneg x := by
    rw [map_add]
    exact add_nonneg (hV.re_inner_nonneg _) (hW.re_inner_nonneg _)
  add_left x y z := by
    simp only [Prod.fst_add, Prod.snd_add, hV.add_left, hW.add_left]
    ring
  smul_left x y r := by
    simp only [Prod.smul_fst, Prod.smul_snd, hV.smul_left, hW.smul_left]
    ring
  definite x hx := by
    have h1 := hV.re_inner_nonneg x.1
    have h2 := hW.re_inner_nonneg x.2
    have hre : (hV.inner x.1 x.1).re + (hW.inner x.2 x.2).re = 0 := by
      rw [← Complex.add_re, hx, Complex.zero_re]
    have e1 : (hV.inner x.1 x.1).re = 0 := by
      change 0 ≤ (hV.inner x.1 x.1).re at h1
      change 0 ≤ (hW.inner x.2 x.2).re at h2
      linarith
    have e2 : (hW.inner x.2 x.2).re = 0 := by
      change 0 ≤ (hV.inner x.1 x.1).re at h1
      change 0 ≤ (hW.inner x.2 x.2).re at h2
      linarith
    exact Prod.ext (core_eq_zero_of_re hV _ e1) (core_eq_zero_of_re hW _ e2)

theorem coreProd_inner (hV : InnerProductSpace.Core ℂ V) (hW : InnerProductSpace.Core ℂ W)
    (x y : V × W) : (coreProd hV hW).inner x y = hV.inner x.1 y.1 + hW.inner x.2 y.2 := rfl

end Core

variable {K : Type*} [Field K]

section Split

variable (σ : K →+* ℂ) (E F : Type*) [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup F]
  [Module (𝓞 K) F]

def fibreProd : Fibre σ (E × F) ≃ₗ[ℂ] Fibre σ E × Fibre σ F :=
  (prodRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) E F).restrictScalars ℂ

variable {σ E F}

@[simp]
theorem fibreProd_tmul (z : ComplexAt σ) (e : E) (f : F) :
    fibreProd σ E F (z ⊗ₜ (e, f)) = (z ⊗ₜ e, z ⊗ₜ f) := rfl

theorem fibreProd_conjMap (x : Fibre σ (E × F)) :
    fibreProd (conjugate σ) E F (conjMap σ (E × F) x) =
      (conjMap σ E (fibreProd σ E F x).1, conjMap σ F (fibreProd σ E F x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero]
  | tmul z v => rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, Prod.fst_add, Prod.snd_add, map_add, map_add,
      Prod.mk_add_mk]

end Split

variable [NumberField K]

variable {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

def HermitianMetric.prod (hE : HermitianMetric K E) (hF : HermitianMetric K F) :
    HermitianMetric K (E × F) where
  form σ := coreComap (coreProd (hE.form σ) (hF.form σ)) (fibreProd σ E F).toLinearMap
    (fibreProd σ E F).injective
  form_conj σ x y := by
    simp only [coreComap_inner, coreProd_inner, LinearEquiv.coe_coe, fibreProd_conjMap,
      hE.form_conj, hF.form_conj, map_add]

def HermitianBundle.prod (A B : HermitianBundle K) : HermitianBundle K :=
  ⟨A.carrier × B.carrier, A.metric.prod B.metric⟩

example : HermitianBundle GaussianField := gaussianIntegers.prod (gaussianStandard 2)

end

end GroundTheory.Heights₂.Heights
end

section
namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section RealToFibre

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

def realToComplexAt : ℝ →ₗ[ℤ] ComplexAt σ :=
  ((ofComplex σ).toRingHom.comp Complex.ofRealHom).toAddMonoidHom.toIntLinearMap

def realToFibre : ℝ ⊗[ℤ] E →ₗ[ℤ] Fibre σ E :=
  TensorProduct.lift
    (((TensorProduct.mk (𝓞 K) (ComplexAt σ) E).restrictScalars₁₂ ℤ ℤ).compl₁₂
      (realToComplexAt σ) LinearMap.id)

variable {σ E}

@[simp]
theorem realToFibre_tmul (r : ℝ) (e : E) :
    realToFibre σ E (r ⊗ₜ e) = ofComplex σ (r : ℂ) ⊗ₜ e := rfl

theorem realToFibre_smul (r : ℝ) (x : ℝ ⊗[ℤ] E) :
    realToFibre σ E (r • x) = (r : ℂ) • realToFibre σ E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s e =>
    rw [smul_tmul', realToFibre_tmul, realToFibre_tmul, smul_tmul', complex_smul_def, smul_eq_mul,
      Complex.ofReal_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem realToFibre_lTensor {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] (φ : E →ₗ[𝓞 K] F)
    (x : ℝ ⊗[ℤ] E) :
    realToFibre σ F (LinearMap.lTensor ℝ (φ.restrictScalars ℤ) x) =
      LinearMap.lTensor (ComplexAt σ) φ (realToFibre σ E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end RealToFibre

variable [NumberField K]

theorem realToFibre_integers_eq_zero (x : ℝ ⊗[ℤ] 𝓞 K)
    (hx : ∀ σ : K →+* ℂ, realToFibre σ (𝓞 K) x = 0) : x = 0 := by
  classical
  set b := RingOfIntegers.basis K
  set B := Algebra.TensorProduct.basis ℝ b
  have hxB : x = ∑ i, B.repr x i • B i := (B.sum_repr x).symm
  have hli := (canonicalEmbedding.latticeBasis K).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have key : ∀ i, B.repr x i = 0 := by
    intro i
    have h0 := hli (fun j ↦ (B.repr x j : ℂ)) ?_ i
    · exact_mod_cast h0
    funext σ
    have hσ := congrArg (integersCoord K σ) (hx σ)
    rw [hxB, map_sum, map_sum, map_zero] at hσ
    simp only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply,
      canonicalEmbedding.apply_at, integralBasis_apply, Pi.zero_apply, smul_eq_mul]
    rw [← hσ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [realToFibre_smul, map_smul, Algebra.TensorProduct.basis_apply, realToFibre_tmul,
      integersCoord_tmul, smul_eq_mul]
    rw [Complex.ofReal_one, map_one, map_one, mul_one]
  rw [hxB]
  simp only [key, zero_smul, Finset.sum_const_zero]

theorem finite_int (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] : Module.Finite ℤ E :=
  Module.Finite.trans (𝓞 K) E

theorem free_int (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] : Module.Free ℤ E := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Flat ℤ E := Module.Flat.trans ℤ (𝓞 K) E
  infer_instance

section General

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

theorem realToFibre_eq_zero (x : ℝ ⊗[ℤ] E) (hx : ∀ σ : K →+* ℂ, realToFibre σ E x = 0) :
    x = 0 := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) E
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let φ : Fin n → (E →ₗ[𝓞 K] 𝓞 K) := fun i ↦ LinearMap.proj i ∘ₗ s
  let g : Fin n → E := fun i ↦ f (fun j ↦ if i = j then 1 else 0)
  have hdecomp : ∀ e : E, ∑ i, φ i e • g i = e := by
    intro e
    have h1 : f (s e) = e := by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
    conv_rhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ f (s e)]
    rfl
  have hdec : ∀ y : ℝ ⊗[ℤ] E, ∑ i, LinearMap.lTensor ℝ
      ((LinearMap.toSpanSingleton (𝓞 K) E (g i)).restrictScalars ℤ)
      (LinearMap.lTensor ℝ ((φ i).restrictScalars ℤ) y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, Finset.sum_const_zero]
    | tmul r e =>
      simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply]
      rw [← tmul_sum, hdecomp]
    | add y z hy hz =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [hy, hz]
  have hφ : ∀ i, LinearMap.lTensor ℝ ((φ i).restrictScalars ℤ) x = 0 := by
    intro i
    refine realToFibre_integers_eq_zero _ fun σ ↦ ?_
    rw [realToFibre_lTensor, hx σ, map_zero]
  rw [← hdec x]
  simp only [hφ, map_zero, Finset.sum_const_zero]

variable (h : HermitianMetric K E)

def RealSpace (_h : HermitianMetric K E) : Type _ := ℝ ⊗[ℤ] E

namespace RealSpace

instance : AddCommGroup (RealSpace h) := inferInstanceAs (AddCommGroup (ℝ ⊗[ℤ] E))

instance : Module ℝ (RealSpace h) := inferInstanceAs (Module ℝ (ℝ ⊗[ℤ] E))

def equivTensor : RealSpace h ≃ₗ[ℝ] ℝ ⊗[ℤ] E := LinearEquiv.refl ℝ _

@[instance_reducible]
def traceCore : InnerProductSpace.Core ℝ (RealSpace h) where
  inner x y := ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
    (realToFibre σ E (equivTensor h y))).re
  conj_inner_symm x y := by
    rw [conj_trivial]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [← (h.form σ).conj_inner_symm, Complex.conj_re]
  re_inner_nonneg x := by
    rw [RCLike.re_to_real]
    exact Finset.sum_nonneg fun σ _ ↦ (h.form σ).re_inner_nonneg _
  add_left x y z := by
    simp only [map_add, (h.form _).add_left, Complex.add_re, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [map_smul, realToFibre_smul, (h.form _).smul_left, conj_trivial,
      Complex.conj_ofReal, Complex.re_ofReal_mul, Finset.mul_sum]
  definite x hx := by
    have hnn : ∀ σ ∈ Finset.univ, 0 ≤ ((h.form σ).inner (realToFibre σ E (equivTensor h x))
        (realToFibre σ E (equivTensor h x))).re := fun σ _ ↦ (h.form σ).re_inner_nonneg _
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hx
    have := realToFibre_eq_zero (equivTensor h x) fun σ ↦
      core_eq_zero_of_re _ _ (h0 σ (Finset.mem_univ σ))
    exact (equivTensor h).injective (by rw [this, map_zero])

instance : NormedAddCommGroup (RealSpace h) := (traceCore h).toNormedAddCommGroup

instance : InnerProductSpace ℝ (RealSpace h) := InnerProductSpace.ofCore _

theorem inner_def (x y : RealSpace h) :
    inner ℝ x y = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h y))).re := rfl

theorem norm_sq_eq (x : RealSpace h) :
    ‖x‖ ^ 2 = ∑ σ, ((h.form σ).inner (realToFibre σ E (equivTensor h x))
      (realToFibre σ E (equivTensor h x))).re := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

def ofModule : E →+ RealSpace h := (TensorProduct.mk ℤ ℝ E 1).toAddMonoidHom

def lattice : Submodule ℤ (RealSpace h) := LinearMap.range (ofModule h).toIntLinearMap

theorem exists_basis_lattice_eq :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ (RealSpace h)),
      lattice h = Submodule.span ℤ (Set.range b) := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Free ℤ E := free_int K E
  set bZ := Module.finBasis ℤ E
  refine ⟨_, (Algebra.TensorProduct.basis ℝ bZ).map (equivTensor h).symm, ?_⟩
  have hb : ⇑((Algebra.TensorProduct.basis ℝ bZ).map (equivTensor h).symm) =
      (ofModule h).toIntLinearMap ∘ bZ := by
    funext i
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [hb, Set.range_comp, ← Submodule.map_span, bZ.span_eq, Submodule.map_top]
  rfl

instance : FiniteDimensional ℝ (RealSpace h) := by
  obtain ⟨n, b, -⟩ := exists_basis_lattice_eq h
  exact Module.Finite.of_basis b

instance : DiscreteTopology (lattice h) := by
  obtain ⟨n, b, hb⟩ := exists_basis_lattice_eq h
  rw [hb]
  infer_instance

instance : IsZLattice ℝ (lattice h) where
  span_top := by
    obtain ⟨n, b, hb⟩ := exists_basis_lattice_eq h
    rw [hb, Submodule.span_span_of_tower, b.span_eq]

theorem ofModule_injective : Function.Injective (ofModule h) := by
  have : Module.Finite ℤ E := finite_int K E
  have : Module.Free ℤ E := free_int K E
  set bZ := Module.finBasis ℤ E
  intro e e' he
  have h1 := congrArg (Algebra.TensorProduct.basis ℝ bZ).repr
    (show (1 : ℝ) ⊗ₜ[ℤ] e = (1 : ℝ) ⊗ₜ[ℤ] e' from he)
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul] at h1
  exact bZ.repr.injective
    (Finsupp.mapRange_injective _ _ (algebraMap ℤ ℝ).injective_int h1)

end RealSpace

end General

abbrev HermitianBundle.RealSpace (A : HermitianBundle K) : Type _ := Heights.RealSpace A.metric

example : IsZLattice ℝ (RealSpace.lattice (HermitianMetric.standard GaussianField (Fin 2))) :=
  inferInstance

end

end GroundTheory.Heights₂.Heights
end

section
namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section SMul

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

theorem fibre_smul_eq (a : ComplexAt σ) (x : Fibre σ E) :
    a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

instance (F : Type*) [AddCommGroup F] [Module (𝓞 K) F] :
    CompatibleSMul ℂ (ComplexAt σ) (Fibre σ E) (Fibre σ F) where
  smul_tmul a x y := by
    rw [fibre_smul_eq, fibre_smul_eq σ F, TensorProduct.smul_tmul]

instance (F : Type*) [AddCommGroup F] [Module (𝓞 K) F] :
    CompatibleSMul (ComplexAt σ) ℂ (Fibre σ E) (Fibre σ F) where
  smul_tmul c x y := by
    rw [show c • x = (ofComplex σ c) • x from (fibre_smul_eq σ E _ x).symm,
      show c • y = (ofComplex σ c) • y from (fibre_smul_eq σ F _ y).symm, TensorProduct.smul_tmul]

end SMul

variable [NumberField K]

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

def FibreSpace (_h : HermitianMetric K E) (σ : K →+* ℂ) : Type _ := Fibre σ E

namespace FibreSpace

variable (h : HermitianMetric K E) (σ : K →+* ℂ)

instance : AddCommGroup (FibreSpace h σ) := inferInstanceAs (AddCommGroup (Fibre σ E))

instance : Module ℂ (FibreSpace h σ) := inferInstanceAs (Module ℂ (Fibre σ E))

instance : NormedAddCommGroup (FibreSpace h σ) :=
  letI : InnerProductSpace.Core ℂ (FibreSpace h σ) := h.form σ
  this.toNormedAddCommGroup

instance : InnerProductSpace ℂ (FibreSpace h σ) := InnerProductSpace.ofCore _

def equiv : Fibre σ E ≃ₗ[ℂ] FibreSpace h σ := LinearEquiv.refl ℂ _

theorem inner_equiv (x y : Fibre σ E) :
    inner ℂ (equiv h σ x) (equiv h σ y) = (h.form σ).inner x y := rfl

end FibreSpace

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

def tensorCoord (hE : HermitianMetric K E) (hF : HermitianMetric K F) (σ : K →+* ℂ) :
    Fibre σ (E ⊗[𝓞 K] F) ≃ₗ[ℂ] FibreSpace hE σ ⊗[ℂ] FibreSpace hF σ :=
  ((AlgebraTensorModule.distribBaseChange (𝓞 K) (ComplexAt σ) E F).restrictScalars ℂ).trans
    ((equivOfCompatibleSMul ℂ (ComplexAt σ) ℂ (Fibre σ E) (Fibre σ F)).trans
      (TensorProduct.congr (FibreSpace.equiv hE σ) (FibreSpace.equiv hF σ)))

theorem tensorCoord_tmul (hE : HermitianMetric K E) (hF : HermitianMetric K F) (σ : K →+* ℂ)
    (z : ComplexAt σ) (e : E) (f : F) :
    tensorCoord hE hF σ (z ⊗ₜ (e ⊗ₜ f)) =
      FibreSpace.equiv hE σ (z ⊗ₜ e) ⊗ₜ FibreSpace.equiv hF σ (1 ⊗ₜ f) := rfl

variable (hE : HermitianMetric K E) (hF : HermitianMetric K F)

theorem tensorCoord_inner_tmul (σ : K →+* ℂ) (z w : ComplexAt σ) (e e' : E) (f f' : F) :
    inner ℂ (tensorCoord hE hF σ (z ⊗ₜ (e ⊗ₜ f))) (tensorCoord hE hF σ (w ⊗ₜ (e' ⊗ₜ f'))) =
      (hE.form σ).inner (z ⊗ₜ e) (w ⊗ₜ e') * (hF.form σ).inner (1 ⊗ₜ f) (1 ⊗ₜ f') := by
  rw [tensorCoord_tmul, tensorCoord_tmul, TensorProduct.inner_tmul]
  rfl

theorem tensorCoord_inner_conjMap (σ : K →+* ℂ) (x y : Fibre σ (E ⊗[𝓞 K] F)) :
    inner ℂ (tensorCoord hE hF (conjugate σ) (conjMap σ _ x))
        (tensorCoord hE hF (conjugate σ) (conjMap σ _ y)) =
      starRingEnd ℂ (inner ℂ (tensorCoord hE hF σ x) (tensorCoord hE hF σ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, inner_zero_left]
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
  | tmul z t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero, inner_zero_left]
    | add t t' ht ht' => simp only [tmul_add, map_add, inner_add_left, ht, ht']
    | tmul e f =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, inner_zero_right]
      | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
      | tmul w s =>
        induction s using TensorProduct.induction_on with
        | zero => simp only [tmul_zero, map_zero, inner_zero_right]
        | add s s' hs hs' => simp only [tmul_add, map_add, inner_add_right, hs, hs']
        | tmul e' f' =>
          rw [conjMap_tmul, conjMap_tmul, tensorCoord_inner_tmul, tensorCoord_inner_tmul, map_mul,
            ← hE.form_conj, ← hF.form_conj, conjMap_tmul, conjMap_tmul, conjMap_tmul,
            conjMap_tmul, map_one]

def HermitianMetric.tensor : HermitianMetric K (E ⊗[𝓞 K] F) where
  form σ := coreOfInjective (tensorCoord hE hF σ).toLinearMap (tensorCoord hE hF σ).injective
  form_conj σ x y := tensorCoord_inner_conjMap hE hF σ x y

def HermitianBundle.tensor (A B : HermitianBundle K) : HermitianBundle K :=
  ⟨A.carrier ⊗[𝓞 K] B.carrier, A.metric.tensor B.metric⟩

example : HermitianBundle GaussianField := (gaussianStandard 2).tensor (gaussianStandard 3)

end

end GroundTheory.Heights₂.Heights
end
