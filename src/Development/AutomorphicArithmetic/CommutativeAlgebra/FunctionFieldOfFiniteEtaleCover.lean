import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GermComapEqAlgebraMapGermOfFiniteEtale

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace UpperTheory.DeRhamTrace

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

private noncomputable abbrev beta : L ⊗[K] Ω[K⁄k] →ₗ[L] L ⊗[K] DR k K :=
  LinearMap.baseChange L (ι1 (R := k) (B := K))

private theorem beta_anti (x y : L ⊗[K] Ω[K⁄k]) :
    beta k K L x * beta k K L y + beta k K L y * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, add_mul, mul_add]
    calc _ = (beta k K L a * beta k K L y + beta k K L y * beta k K L a) +
          (beta k K L b * beta k K L y + beta k K L y * beta k K L b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  | tmul a ω =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd =>
      rw [map_add, add_mul, mul_add]
      calc _ = (beta k K L (a ⊗ₜ ω) * beta k K L c + beta k K L c * beta k K L (a ⊗ₜ ω)) +
            (beta k K L (a ⊗ₜ ω) * beta k K L d + beta k K L d * beta k K L (a ⊗ₜ ω)) := by abel
        _ = 0 := by rw [hc, hd, add_zero]
    | tmul b ω' =>
      simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm b a, ← TensorProduct.tmul_add]
      have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω' +
          ι1 (R := k) (B := K) ω' * ι1 (R := k) (B := K) ω = 0 :=
        ExteriorAlgebra.ι_add_mul_swap ω ω'
      rw [this, TensorProduct.tmul_zero]

private theorem beta_sq (x : L ⊗[K] Ω[K⁄k]) : beta k K L x * beta k K L x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero]
    exact beta_anti k K L a b
  | tmul a ω =>
    simp only [beta, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have : ι1 (R := k) (B := K) ω * ι1 (R := k) (B := K) ω = 0 := ExteriorAlgebra.ι_sq_zero ω
    rw [this, TensorProduct.tmul_zero]

variable [Algebra.FormallyEtale K L]

private noncomputable def phi : Ω[L⁄k] →ₗ[L] L ⊗[K] DR k K :=
  beta k K L ∘ₗ (KaehlerDifferential.isBaseChange_of_formallyEtale k K L).equiv.symm.toLinearMap

private theorem phi_sq (x : Ω[L⁄k]) : phi k K L x * phi k K L x = 0 := beta_sq k K L _

private noncomputable def psi : DR k L →ₐ[L] L ⊗[K] DR k K :=
  ExteriorAlgebra.lift L ⟨phi k K L, phi_sq k K L⟩

private theorem psi_mapDR (ω : DR k K) : psi k K L (GlobalTheory.W1.mapDR k K L ω) = 1 ⊗ₜ ω := by
  have key : ((psi k K L).restrictScalars K).comp (GlobalTheory.W1.mapDR k K L) =
      Algebra.TensorProduct.includeRight := by
    apply ExteriorAlgebra.hom_ext
    refine LinearMap.ext fun η ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply]
    simp only [GlobalTheory.W1.map1, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [psi, ExteriorAlgebra.lift_ι_apply]
    simp only [phi, LinearMap.comp_apply, LinearEquiv.coe_coe, IsBaseChange.equiv_symm_apply,
      beta, LinearMap.baseChange_tmul]
  exact congrArg (fun f ↦ f ω) key

end UpperTheory.DeRhamTrace

open UpperTheory.DeRhamTrace in
theorem UpperTheory.exists_deRhamTrace_of_separable :
    ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], ∃ T : DR k L →ₗ[k] DR k K, GlobalTheory.W1.IsTrDR k K L T := by
  intro k K L _ _ _ _ _ _ _ _ _
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let Tr : (L ⊗[K] DR k K) →ₗ[K] DR k K :=
    (TensorProduct.lid K (DR k K)).toLinearMap ∘ₗ LinearMap.rTensor (DR k K) (Algebra.trace K L)
  refine ⟨(Tr.restrictScalars k) ∘ₗ ((psi k K L).toLinearMap.restrictScalars k), ?_⟩
  intro b ω
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]
  rw [map_smul, psi_mapDR, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [Tr]
end

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem mDR_alg_eq_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] (w : DR k K) :
    (semiHom_algebraMap k K L).mDR w = GlobalTheory.W1.mapDR k K L w := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [SemiHom.mDR_algebraMap, AlgHom.commutes]
    rfl
  | ι x =>
    have h1 := SemiHom.mDR_ι (semiHom_algebraMap k K L) x
    simp only [ι1] at h1
    rw [h1, SemiHom.oneFormMap_eq_kaehlerDifferential_map _ (fun _ => rfl)]
    simp only [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply, GlobalTheory.W1.map1, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, ι1]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem mDR_square {k B B' K L : Type} [Field k] [Field K] [Field L] [CommRing B] [CommRing B']
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k B] [Algebra k B']
    {α : B →+* K} {β : B →+* B'} {γ : B' →+* L} (hα : SemiHom (RingHom.id k) α)
    (hβ : SemiHom (RingHom.id k) β) (hγ : SemiHom (RingHom.id k) γ)
    (h : ∀ b, γ (β b) = algebraMap K L (α b)) {j : ℕ} (x : Om k B j) :
    hγ.mDR (hβ.mDR (x : DR k B)) = GlobalTheory.W1.mapDR k K L (hα.mDR (x : DR k B)) := by
  rw [← SemiHom.coe_mOm hβ, ← SemiHom.coe_mOm hγ, ← mDR_alg_eq_mapDR, ← SemiHom.coe_mOm hα,
    ← SemiHom.coe_mOm (semiHom_algebraMap k K L),
    SemiHom.mOm_mOm hβ hγ (hβ.comp hγ) (fun _ => rfl),
    SemiHom.mOm_mOm hα (semiHom_algebraMap k K L) (hβ.comp hγ) (fun b => (h b).symm)]

private theorem formGerm_toOm {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k) (j : ℕ)
    {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) (x : OmU s V j) :
    letI := algΓ s; letI := ffAlg s
    formGerm s j hV hη (toOm s j V x) = (semiHom_germSec s hη).mDR (x : DR k (Sec s V)) := by
  letI := algΓ s; letI := ffAlg s
  change (semiHom_germSec s hη).mDR (((toOmEquiv s j hV).symm (toOm s j V x) : OmU s V j) : DR k (Sec s V)) = _
  rw [← toOmEquiv_apply s j hV, LinearEquiv.symm_apply_apply]

theorem UpperTheory.functionField_of_finite_etale_cover :
    ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p'), (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) → FiniteDimensional Z.functionField Y.functionField → ∀ (a : ℕ) (V : Z.Opens) (hV : IsAffineOpen V) (hη : genericPoint Z ∈ V) (hη' : genericPoint Y ∈ c ⁻¹ᵁ V) (y : Γ(Omega p' a, c ⁻¹ᵁ V)), letI := algΓ p; letI := algΓ p'; formGermI p a hV hη hinst ((omegaTrace hc a).app V y) = GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField (formGermI p' a (hV.preimage c) hη' hinst' y) := by
  intro Z Y _ _ p p' c hc _ _ inst inst' _ _ hinst hinst' hg hfd a V hV hη hη' y
  subst hinst hinst'
  letI := ffAlg p; letI := ffAlg p'
  haveI : CharZero Z.functionField := charZero_of_injective_algebraMap (algebraMap ℂ Z.functionField).injective
  haveI : Algebra.IsSeparable Z.functionField Y.functionField := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hT := UpperTheory.exists_deRhamTrace_of_separable ℂ Z.functionField Y.functionField
  have hspec : GlobalTheory.W1.IsTrDR ℂ Z.functionField Y.functionField (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField) := by
    unfold GlobalTheory.W1.trDR; rw [dif_pos hT]; exact hT.choose_spec
  obtain ⟨z, rfl⟩ := toOm_surjective (s := p') (j := a) (hV.preimage c) y
  change formGerm p a hV hη _ = GlobalTheory.W1.trDR ℂ _ _ (formGerm p' a (hV.preimage c) hη' _)
  rw [omegaTrace_app_toOm hc a hV, formGerm_toOm, formGerm_toOm]
  refine formOm_induction (P := fun z ↦ (semiHom_germSec p hη).mDR
      ((formTraceU hc hV a z : OmU p V a) : DR ℂ (Sec p V)) =
    GlobalTheory.W1.trDR ℂ _ _ ((semiHom_germSec p' hη').mDR (z : DR ℂ (Sec p' (c ⁻¹ᵁ V))))) hc hV ?_ ?_ ?_ z
  · simp only [map_zero, ZeroMemClass.coe_zero]
  · intro y z hy hz
    simp only [map_add, Submodule.coe_add, hy, hz]
  · intro b' x
    have e : ((formPull hc V a x : OmU p' (c ⁻¹ᵁ V) a) : DR ℂ (Sec p' (c ⁻¹ᵁ V))) =
        (semiHom_appSec hc V).mDR (x : DR ℂ (Sec p V)) := SemiHom.coe_mOm _ x
    rw [formTraceU_smul_formPull, Submodule.coe_smul, Submodule.coe_smul, SemiHom.mDR_smul,
      SemiHom.mDR_smul, e, mDR_square (semiHom_germSec p hη) (semiHom_appSec hc V)
        (semiHom_germSec p' hη') (fun b ↦ hg V hη hη' b), hspec]
    exact congrArg (· • _) (UpperTheory.Cb.germ_comap_eq_algebraMap_germ_of_finite_etale Z Y p p' c hc hg V hV hη hη' b')
end
