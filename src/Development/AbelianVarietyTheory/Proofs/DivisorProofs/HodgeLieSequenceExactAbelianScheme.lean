import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_tangent_eq_of_crystallineValues_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w → (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  first | exact @GlobalTheory.LieInj.tangent_eq_of_tanVal_eq | exact GlobalTheory.LieInj.tangent_eq_of_tanVal_eq | (intros; apply GlobalTheory.LieInj.tangent_eq_of_tanVal_eq <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVector_functional_globalForms_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ φ : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, (∀ f, GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ v : epsR R ⟶ A, IsTangent v ∧ ∀ f, tanVal v f = φ f := by
  first | exact @GlobalTheory.LieDual.exists_tangent_of_functional | exact GlobalTheory.LieDual.exists_tangent_of_functional | (intros; apply GlobalTheory.LieDual.exists_tangent_of_functional <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem exists_extend_hodgeFiltration_functional_split {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hO : Function.Injective (cmpO s)) (h1 : Function.Surjective (cmp1 s))
    (hsurj : Function.Surjective (toHO1 s)) [Module.Projective R (HO1 s)]
    (ψ : F1 s →ₗ[R] R) : ∃ H : FirstDeRham s →ₗ[R] R, ∀ c : F1 s, H c = ψ c := by
  let f : FirstDeRham s →ₗ[R] HO1 s := (toHO1 s).comp (cmp1 s)
  have hf : Function.Surjective f := hsurj.comp h1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s := fun c ↦ by
    change toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0
    rw [structureSheaf_comparison_comm]
    exact ⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  let p : FirstDeRham s →ₗ[R] F1 s := LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by
    rw [← hker]
    have : f (σ (f c)) = f c := LinearMap.congr_fun hσ (f c)
    simp [this]
  refine ⟨ψ.comp p, fun c ↦ ?_⟩
  have hc : f c = 0 := (hker c).2 c.2
  have : p c = c := Subtype.ext (by simp [p, hc])
  simp [this]

end GlobalTheory.CechDR

namespace GlobalTheory.AbelianExtend

open GlobalTheory.CechDR

theorem abelianScheme_hodgeFiltration_functional_extends' : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R,
      ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  intro hC hH R _ A _ g hab hdim ψ
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩ := hH R A g hab hdim
  haveI := hab.smooth
  haveI := hab.proper
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have h1 := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 (Sp R))
  have hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hsurj
  haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj
  exact GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ

end GlobalTheory.AbelianExtend
end
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hodgeFiltration_functional_extends : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  atlas_forward_decl GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends'
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieHodge

theorem lieExact_of_crystallineLift_hodgeDeRham : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LieExact A := by
  intro hC hH R _ A _ g hab hdim
  have hP : AllPrim (dp0 R) (𝟙 _) A :=
    (GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison hC hH) R A g hab hdim).1
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp : Function.Injective (GlobalTheory.CechDR.cmp1 (A.hom ≫ 𝟙 (Sp R))) :=
    (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1.1
  have hcl : Function.Injective (GlobalTheory.CechDR.clForm (A.hom ≫ 𝟙 (Sp R))) :=
    (hH R A g hab hdim).2.2.2.2.1.2.1
  have hcf : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)),
      Form.cl _ f = 0 ↔ GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 := fun f ↦
    ⟨fun h ↦ hcl (by rw [← GlobalTheory.CechDR.comparison_formClass, h, map_zero, map_zero]),
      fun h ↦ hcmp (by rw [GlobalTheory.CechDR.comparison_formClass, h, map_zero, map_zero])⟩
  have hmem : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f ∈ primDR A := fun f ↦ by
    have : primDR A = ⊤ := hP
    rw [this]; exact Submodule.mem_top
  let F : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] primDR A := (Form.cl _).codRestrict _ hmem
  refine ⟨fun h ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨v, hv, hvf⟩ := GlobalTheory.T.exists_tangentVector_functional_globalForms_abelianScheme hC hH R A g hab hdim (h ∘ₗ F) (fun f hf ↦ by
      have e : F f = 0 := Subtype.ext ((hcf f).2 hf)
      rw [LinearMap.comp_apply, e, map_zero])
    refine ⟨v, ⟨hv, fun f hf ↦ (hvf f).symm⟩, fun w hw ↦ GlobalTheory.T.abelianScheme_tangent_eq_of_crystallineValues_eq hC hH R A g hab hdim w v hw.1 hv
      fun f ↦ ((hw.2 f (hmem f)).symm.trans (hvf f).symm)⟩
  · have hfac : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f = 0 → tanVal v f = 0 :=
      fun f h0 ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero R A v f ((hcf f).1 h0)
    have hF1 : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := fun f ↦ by
      rw [hodgeFiltration_eq_range]; exact ⟨f, rfl⟩
    let c1 : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] F1 (A.hom ≫ 𝟙 (Sp R)) := (Form.cl _).codRestrict _ hF1
    have hc1 : Function.Surjective c1 := by
      rintro ⟨c, hc⟩
      rw [hodgeFiltration_eq_range] at hc
      obtain ⟨f, rfl⟩ := hc
      exact ⟨f, rfl⟩
    let e := c1.quotKerEquivOfSurjective hc1
    have hker : LinearMap.ker c1 ≤ LinearMap.ker (tanVal v) :=
      fun f hf ↦ hfac f (congrArg Subtype.val hf)
    let ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R :=
      (LinearMap.ker c1).liftQ (tanVal v) hker ∘ₗ e.symm.toLinearMap
    have hψ : ∀ f, ψ (c1 f) = tanVal v f := fun f ↦ by
      have : e.symm (c1 f) = Submodule.Quotient.mk f := e.symm_apply_eq.2 rfl
      change (LinearMap.ker c1).liftQ (tanVal v) hker (e.symm (c1 f)) = _
      rw [this]; rfl
    obtain ⟨H, hH'⟩ := GlobalTheory.T.abelianScheme_hodgeFiltration_functional_extends hC hH R A g hab hdim ψ
    exact ⟨H ∘ₗ (primDR A).subtype, hv, fun f hf ↦ (hH' (c1 f)).trans (hψ f)⟩

end GlobalTheory.LieHodge
end
end
