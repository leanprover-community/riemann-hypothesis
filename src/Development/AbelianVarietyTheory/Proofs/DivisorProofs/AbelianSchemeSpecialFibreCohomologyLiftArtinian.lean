import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverBaseChangeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocal

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem finrank_HO1_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K L _ _ _ A _ B _ φ hpb hA g hfin hrank
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := flat_baseChange_HO K L A.left B.left A.hom B.hom φ hpb.1 inferInstance inferInstance
  haveI : Module.Finite L (L ⊗[K] HO1 A.hom) := Module.Finite.equiv e.symm
  have hr : Module.rank L (L ⊗[K] HO1 A.hom) = Cardinal.lift (Module.rank K (HO1 A.hom)) :=
    Module.rank_baseChange
  have hfinA : Module.Finite K (HO1 A.hom) := by
    rw [← Module.rank_lt_aleph0_iff]
    have h1 : Module.rank L (L ⊗[K] HO1 A.hom) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [hr] at h1
    simpa using h1
  refine ⟨hfinA, ?_⟩
  rw [← hrank, ← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_h1_rank_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  atlas_forward_decl GlobalTheory.AbCoh.finrank_HO1_descend_field
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem one_tmul_injective_field (K L M : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Function.Injective (fun m : M ↦ (1 : L) ⊗ₜ[K] m) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (fun m : M ↦ (1 : L) ⊗ₜ[K] m) = ((Algebra.linearMap K L).rTensor M) ∘ (TensorProduct.lid K M).symm := by
    funext m; simp
  rw [h2]; exact h1.comp (TensorProduct.lid K M).symm.injective

theorem pullHO_injective_field (K L : Type) [Field K] [Field L] [Algebra K L] (X X' : Scheme.{0}) (s : X ⟶ Sp K)
    (s' : X' ⟶ Sp L) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap K L))) (hs : IsSeparated s)
    (hq : QuasiCompact s) :
    Function.Injective (pullHO1 h.w) ∧ Function.Injective (pullHO2 h.w) := by
  obtain ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩ := GlobalTheory.T.structure_cohomology_flat_base_change K L X X' s s' φ h hs hq
  refine ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩
  · apply one_tmul_injective_field K L
    apply e1.injective
    simp only [he1, hab]
  · apply one_tmul_injective_field K L
    apply e2.injective
    simp only [he2, hab]

theorem noPrimO2_axesO1_descend : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  intro K L _ _ _ A _ B _ φ hφ hA
  have hpA : IsProper A.hom := hA.proper
  have hpAA : IsProper (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨Φ, hΦ, hμ, hf, hs, ha1, ha2⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback K L (algebraMap K L) A B φ hφ
  have injA := pullHO_injective_field K L A.left B.left A.hom B.hom φ hφ.1 inferInstance inferInstance
  have injAA := pullHO_injective_field K L (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom Φ hΦ
    inferInstance inferInstance
  have N := pull_over_baseChange_comm K L (algebraMap K L)
  refine ⟨fun hB z hz ↦ ?_, fun hB y h1 h2 ↦ ?_⟩
  · apply injA.2
    rw [map_zero]
    apply hB
    have e := congrArg (pullHO2 hΦ.w) hz
    rw [map_add] at e
    rw [← (N A (A ⊗ A) B (B ⊗ B) μ[A] μ[B] φ Φ hφ.1.w hΦ.w hμ).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (fst A A) (fst B B) φ Φ hφ.1.w hΦ.w hf).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (snd A A) (snd B B) φ Φ hφ.1.w hΦ.w hs).2]
    exact e
  · apply injAA.1
    rw [map_zero]
    apply hB
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha1).1, h1, map_zero]
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha2).1, h2, map_zero]

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_axes_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  atlas_forward_decl GlobalTheory.AbCoh.noPrimO2_axesO1_descend
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exteriorSquare_equiv_of_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  intro K L _ _ _ M N M' N' _ _ _ _ _ _ _ _ c c' e₁ e₂ hcomp hex
  classical
  obtain ⟨eL, heL⟩ := hex

  have hinj : Function.Injective (TensorProduct.mk K L N 1) := by
    have h1 : Function.Injective ((Algebra.linearMap K L).rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
    intro x y hxy
    apply (TensorProduct.lid K N).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hxy

  have hc : ∀ a, c a a = 0 := by
    intro a
    apply hinj
    apply e₂.injective
    have h0 : exteriorPower.ιMulti L 2 ![e₁ (1 ⊗ₜ a), e₁ (1 ⊗ₜ a)] = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
    simp only [TensorProduct.mk_apply, hcomp, TensorProduct.tmul_zero, map_zero, ← heL, h0]
  let f : M [⋀^Fin 2]→ₗ[K] N :=
    { toFun := fun w => c (w 0) (w 1)
      map_update_add' := by
        intro _ w i x y
        fin_cases i <;> simp
      map_update_smul' := by
        intro _ w i r x
        fin_cases i <;> simp
      map_eq_zero_of_eq' := by
        intro w i j hij hne
        fin_cases i <;> fin_cases j <;> simp_all [hc] }
  let φ := exteriorPower.alternatingMapLinearEquiv f
  have hφ : ∀ w : Fin 2 → M, φ (exteriorPower.ιMulti K 2 w) = c (w 0) (w 1) := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f w
  let b := Module.Basis.ofVectorSpace K M
  letI : LinearOrder (Module.Basis.ofVectorSpaceIndex K M) := linearOrderOfSTO WellOrderingRel
  let B := b.exteriorPower 2
  let b' := (Algebra.TensorProduct.basis L b).map e₁
  have hb' : ∀ i, b' i = e₁ (1 ⊗ₜ b i) := fun i => by
    simp [b', Algebra.TensorProduct.basis_apply]
  let B' := b'.exteriorPower 2
  have key : ∀ s, e₂ (1 ⊗ₜ φ (B s)) = eL (B' s) := by
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_family, hφ, hcomp, ← heL]
    congr 2
    funext i
    fin_cases i <;> simp [hb']
  let V' := B'.map (eL.trans e₂.symm)
  have hV' : ∀ s, V' s = (1 : L) ⊗ₜ[K] φ (B s) := fun s => by
    simp only [V', Module.Basis.map_apply, LinearEquiv.trans_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  have h1 : LinearIndependent L (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := by
    have h := V'.linearIndependent
    rwa [show (⇑V') = fun s => (1 : L) ⊗ₜ[K] φ (B s) from funext hV'] at h
  have h2 : LinearIndependent K (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := h1.restrict_scalars' K
  have h3 : LinearIndependent K (φ ∘ B) := LinearIndependent.of_comp (TensorProduct.mk K L N 1) h2
  let W := Submodule.span K (Set.range (φ ∘ B))
  have hs : Function.Surjective (W.subtype.lTensor L) := by
    have hr : LinearMap.range (W.subtype.baseChange L) = ⊤ := by
      rw [eq_top_iff, ← V'.span_eq, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      rw [hV']
      exact ⟨1 ⊗ₜ ⟨φ (B s), Submodule.subset_span ⟨s, rfl⟩⟩, rfl⟩
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hr x
    exact ⟨y, by rw [← LinearMap.baseChange_eq_ltensor]; exact hy⟩
  have hW : Function.Surjective W.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective K L W.subtype).mp hs
  have hspan : ⊤ ≤ W := fun x _ => by
    obtain ⟨y, rfl⟩ := hW x
    exact y.2
  let V := Module.Basis.mk h3 hspan
  refine ⟨B.equiv V (Equiv.refl _), fun a b => ?_⟩
  have hEq : (B.equiv V (Equiv.refl _)).toLinearMap = φ :=
    B.ext fun s => by simp [V, Module.Basis.mk_apply]
  rw [← LinearEquiv.coe_coe, hEq, hφ]
  rfl

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorSquare_equiv_of_baseChange_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  atlas_forward_decl GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem wedgeO_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → WedgeO (OAff B.hom) → WedgeO (OAff A.hom) := by
  intro K L _ _ _ A _ B _ φ h hA hB
  have hp : IsProper A.hom := hA.proper
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ :=
    GlobalTheory.T.structure_cohomology_flat_base_change K L A.left B.left A.hom B.hom φ h.1 inferInstance inferInstance
  refine GlobalTheory.T.exteriorSquare_equiv_of_baseChange_field K L _ _ _ _ (cup (OAff A.hom)) (cup (OAff B.hom)) e₁ e₂ (fun a b ↦ ?_) hB
  rw [he₁, he₁, he₂]
  exact (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.1 K L A.left B.left A.hom B.hom _ φ h.1.w).1 a b

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_property_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → WedgeO (OAff B.hom) → WedgeO (OAff A.hom) := by
  atlas_forward_decl GlobalTheory.AbCoh.wedgeO_descends_field
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelian_HO_field_any : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧
      Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  intro K _ A _ g hab hsm
  let L := AlgebraicClosure K
  let σ : K →+* L := algebraMap K L
  have hpb : IsPullback (pullback.fst A.hom (spMap σ)) (pullback.snd A.hom (spMap σ)) A.hom (spMap σ) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨inst, hgp, habB, hsmB⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' K L σ A _ _ _ hpb
  have hB := @GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed L _ _ (Over.mk (pullback.snd A.hom (spMap σ))) inst g (habB hab) (hsmB g hsm)
  obtain ⟨hfin, hrk, hw, hnp, hax⟩ := hB
  obtain ⟨hfinA, hrkA⟩ := @GlobalTheory.T.structure_h1_rank_descends_field K L _ _ _ A _ _ inst _ hgp hab g hfin hrk
  obtain ⟨hnpA, haxA⟩ := @GlobalTheory.T.primitive_axes_descend_field K L _ _ _ A _ _ inst _ hgp hab
  exact ⟨hfinA, hrkA, @GlobalTheory.T.wedge_property_descends_field K L _ _ _ A _ _ inst _ hgp hab hw, hnpA hnp, haxA hax⟩

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  atlas_forward_decl GlobalTheory.AbCoh.abelian_HO_field_any
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.FieldSq

theorem axes_noPrim_wedge : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) := by
  intro k _ hk B _ g hab hsm
  letI : Field k := hk.toField
  obtain ⟨-, -, hw, hn, ha⟩ := GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField k B g hab hsm
  exact ⟨ha, hn, hw⟩

end GlobalTheory.AbCoh.FieldSq
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_over_field_axes_wedge : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) := by
  atlas_forward_decl GlobalTheory.AbCoh.FieldSq.axes_noPrim_wedge
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory

theorem artinianLocal_finiteLength_and_socle_element :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R],
      (∃ n : ℕ, Module.length R R = n) ∧
      (¬ IsField R → ∃ t : R, t ≠ 0 ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) ∧
        Module.length (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) < Module.length R R) := by
  intro R _ _ _
  have hfin : IsFiniteLength R R :=
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  have hne : Module.length R R ≠ ⊤ := Module.length_ne_top_iff.2 hfin
  refine ⟨⟨(Module.length R R).toNat, (ENat.natCast_toNat hne).symm⟩, ?_⟩
  intro hnf
  classical
  set m := IsLocalRing.maximalIdeal R with hmdef
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hk
  have hex : ∃ n : ℕ, m ^ n = ⊥ := ⟨k, hk⟩
  have hn : m ^ Nat.find hex = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, Ideal.one_eq_top] at hn
    exact top_ne_bot hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hjne : m ^ j ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hjne
  have hkill : ∀ a ∈ m, a * t = 0 := by
    intro a ha
    have h1 : a * t ∈ m ^ (j + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha htm
    have hj' : Nat.find hex = j + 1 := hj
    rw [← hj', hn] at h1
    exact (Submodule.mem_bot R).1 h1
  refine ⟨t, ht0, hkill, ?_⟩
  set I : Ideal R := Ideal.span {t}
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ I) (M := R ⧸ I)
    Ideal.Quotient.mk_surjective |>.symm]
  have hadd := Module.length_eq_add_of_exact (R := R) I.subtype I.mkQ I.injective_subtype
    I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)
  have hI : Module.length R I ≠ 0 := by
    rw [Ne, Module.length_eq_zero_iff]
    intro hs
    have : (⟨t, Ideal.subset_span rfl⟩ : I) = 0 := Subsingleton.elim _ _
    exact ht0 (congrArg Subtype.val this)
  have hQ : Module.length R (R ⧸ I) ≠ ⊤ := by
    intro h
    rw [hadd, h] at hne
    simp at hne
  rw [hadd]
  lift Module.length R (R ⧸ I) to ℕ using hQ with q
  lift Module.length R I to ℕ using (by
    intro h; rw [hadd, h] at hne; simp at hne) with i
  norm_cast
  norm_cast at hI
  omega

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], (∃ n : ℕ, Module.length R R = n) ∧ (¬ IsField R → ∃ t : R, t ≠ 0 ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) ∧ Module.length (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) < Module.length R R) := by
  atlas_forward_decl GlobalTheory.artinianLocal_finiteLength_and_socle_element
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_h1_surjective_bijective_fibre : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.PrimLift

theorem pO1_comp {R : Type} [CommRing R] {Y A B : Over (Sp R)} (f : Y ⟶ A) (g : A ⟶ B) (a : HO1 B.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) := by
  unfold pO1
  exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R B.left A.left B.hom A.hom (RingHom.id R) g.left (ovw g) R Y.left Y.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (by simp)
    (fun _ => rfl)).1 a).symm

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A).1 a

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := by
    show IsAffine (Sp R)
    infer_instance
  exact (GlobalTheory.AbCoh.Vanish.main.1 R _ _ this).1.elim a 0

theorem primO1_of_axesO1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  intro R _ A _ hax x
  have key : ∀ j : A ⟶ A ⊗ A, pO1 (j ≫ μ[A]) x - pO1 (j ≫ fst A A) x - pO1 (j ≫ snd A A) x =
      pO1 j (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) := by
    intro j
    rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp]
  have hη : pO1 (toUnit A ≫ η[A]) x = 0 := by
    rw [pO1_comp, pO1_unit_eq_zero (pO1 η[A] x), map_zero]
  have h := hax (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x)
    (by
      rw [← key, lift_comp_one_right, lift_fst, lift_snd, pO1_id, hη]
      simp)
    (by
      rw [← key, lift_comp_one_left, lift_fst, lift_snd, pO1_id, hη]
      simp)
  rw [sub_sub, sub_eq_zero] at h
  exact h

end GlobalTheory.AbCoh.PrimLift
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_of_axes_vanishing : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  atlas_forward_decl GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.PullbackCupProduct

open GlobalTheory.CatCoh

universe u v u' v' u'' v''

theorem pull_cup_of_bijective {R R' : Type} [CommRing R] [CommRing R']
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
    {F'' : C'' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F'') (n : CoefMap (RingHom.id R') F' F'')
    (h1 : Function.Bijective n.pull1) (h2 : Function.Bijective n.pull2) (a b : H1 F) :
    (LinearEquiv.ofBijective n.pull2 h2).symm (m.pull2 (cup F a b)) =
      cup F' ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 a))
        ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 b)) := by
  have back : ∀ x, n.pull1 ((LinearEquiv.ofBijective n.pull1 h1).symm x) = x := fun x =>
    (LinearEquiv.ofBijective n.pull1 h1).apply_symm_apply x
  apply (LinearEquiv.ofBijective n.pull2 h2).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, n.pullCohomologyTwo_cup, back, back, m.pullCohomologyTwo_cup]

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : AlgebraicGeometry.Scheme}
  {s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} {s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} {σ : R →+* R'}
  {φ : X' ⟶ X}

theorem pullHO2_cup (h : φ ≫ s = s' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) (a b : GlobalTheory.CechDR.HO1 s) :
    GlobalTheory.AbCoh.pullHO2 h (cup _ a b) = cup _ (GlobalTheory.CechDR.pullHO1 h a) (GlobalTheory.CechDR.pullHO1 h b) := by
  unfold GlobalTheory.AbCoh.pullHO2 GlobalTheory.CechDR.pullHO1 GlobalTheory.CechDR.pairResEquivO
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact pull_cup_of_bijective _ _ _ _ a b

theorem main : ∀ (R R' : Type) [inst : CommRing R] [inst_1 : CommRing R'] (X X' : AlgebraicGeometry.Scheme) (s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : CategoryTheory.CategoryStruct.comp φ s = CategoryTheory.CategoryStruct.comp s' (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ)), Function.Surjective (⇑(GlobalTheory.CechDR.pullHO1 h) : GlobalTheory.CechDR.HO1 s → GlobalTheory.CechDR.HO1 s') → GlobalTheory.AbCoh.WedgeO (GlobalTheory.CechDR.OAff s') → Function.Surjective (⇑(GlobalTheory.AbCoh.pullHO2 h) : GlobalTheory.AbCoh.HO2 s → GlobalTheory.AbCoh.HO2 s') := by
  intro R R' _ _ X X' s s' σ φ h hsurj hwedge
  obtain ⟨e, he⟩ := hwedge

  have key : ∀ x, ∀ r : R', ∃ z, GlobalTheory.AbCoh.pullHO2 h z = e (r • x) := by
    intro x
    have hx : x ∈ Submodule.span R' (Set.range (exteriorPower.ιMulti R' 2)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      intro r
      obtain ⟨a, ha⟩ := hsurj (r • v 0)
      obtain ⟨b, hb⟩ := hsurj (v 1)
      refine ⟨cup _ a b, ?_⟩
      have hv : r • exteriorPower.ιMulti R' 2 v = exteriorPower.ιMulti R' 2 ![r • v 0, v 1] := by
        have hupd : (![r • v 0, v 1] : Fin 2 → _) = Function.update v 0 (r • v 0) := by
          funext i
          fin_cases i <;> simp
        rw [hupd, AlternatingMap.map_update_smul, Function.update_eq_self]
      rw [pullHO2_cup, ha, hb, hv, he]
    | zero =>
      intro r
      exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨z₁, h₁⟩ := hx r
      obtain ⟨z₂, h₂⟩ := hy r
      exact ⟨z₁ + z₂, by rw [map_add, h₁, h₂, smul_add, map_add]⟩
    | smul c x _ hx =>
      intro r
      obtain ⟨z, hz⟩ := hx (r * c)
      exact ⟨z, by rw [hz, smul_smul]⟩
  intro y
  obtain ⟨z, hz⟩ := key (e.symm y) 1
  exact ⟨z, by rw [hz, one_smul, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.PullbackCupProduct
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pullHO2_surjective_of_wedge : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ),
    Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first
  | exact @_root_.GlobalTheory.PullbackCupProduct.main
  | exact _root_.GlobalTheory.PullbackCupProduct.main
  | (apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PullbackCupProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PullbackCupProduct.main ..)

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_pullHO2_of_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  atlas_forward_decl GlobalTheory.AbCoh.pullHO2_surjective_of_wedge
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_of_iso {k : Type} [CommRing k] {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k) (e : X' ≅ X)
    (he : e.hom ≫ s = s') (hW : WedgeO (OAff s)) : WedgeO (OAff s') := by
  have h1 : e.hom ≫ s = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, he]
  have h2 : e.inv ≫ s' = s ≫ spMap (RingHom.id k) := by
    rw [spMap_id, Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have hid : (𝟙 X) ≫ s = s ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have hid' : (𝟙 X') ≫ s' = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have P := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  have c1 := (P.1 k k X X' s s' (RingHom.id k) e.hom h1 k X s (RingHom.id k) e.inv h2 (RingHom.id k) (𝟙 X) hid
    (by simp) (fun _ ↦ rfl))
  have c2 := (P.1 k k X' X s' s (RingHom.id k) e.inv h2 k X' s' (RingHom.id k) e.hom h1 (RingHom.id k) (𝟙 X') hid'
    (by simp) (fun _ ↦ rfl))
  have i1 := P.2.2 k (Over.mk s)
  have i2 := P.2.2 k (Over.mk s')
  have hcup := (P.2.1 k k X X' s s' (RingHom.id k) e.hom h1).1

  let f1 : HO1 s →ₗ[k] HO1 s' := pullHO1 h1
  let g1 : HO1 s' →ₗ[k] HO1 s := pullHO1 h2
  let f2 : HO2 s →ₗ[k] HO2 s' := pullHO2 h1
  let g2 : HO2 s' →ₗ[k] HO2 s := pullHO2 h2
  have fg1 : ∀ a, f1 (g1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c2.1]; exact i2.1 a
  have gf1 : ∀ a, g1 (f1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c1.1]; exact i1.1 a
  have fg2 : ∀ a, f2 (g2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c2.2.1]; exact i2.2.1 a
  have gf2 : ∀ a, g2 (f2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c1.2.1]; exact i1.2.1 a
  let e2 : HO2 s ≃ₗ[k] HO2 s' := LinearEquiv.ofLinear f2 g2 (LinearMap.ext fg2) (LinearMap.ext gf2)
  let eΛ : ⋀[k]^2 (HO1 s') ≃ₗ[k] ⋀[k]^2 (HO1 s) :=
    LinearEquiv.ofLinear (exteriorPower.map 2 g1) (exteriorPower.map 2 f1)
      (by rw [← exteriorPower.map_comp, show g1 ∘ₗ f1 = LinearMap.id from LinearMap.ext gf1,
        exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, show f1 ∘ₗ g1 = LinearMap.id from LinearMap.ext fg1,
        exteriorPower.map_id])
  obtain ⟨E, hE⟩ := hW
  refine ⟨(eΛ.trans E).trans e2, fun a b ↦ ?_⟩
  have hm : (⇑g1 ∘ ![a, b]) = ![g1 a, g1 b] := by
    ext i; fin_cases i <;> rfl
  change f2 (E (exteriorPower.map 2 g1 (exteriorPower.ιMulti k 2 ![a, b]))) = _
  rw [exteriorPower.map_apply_ιMulti, hm, hE]
  simp only [f2]
  rw [hcup]
  rw [show pullHO1 h1 (g1 a) = a from fg1 a, show pullHO1 h1 (g1 b) = b from fg1 b]

end GlobalTheory.AbCohWedgeLift

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_fibre : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  intro hF R _ A _ g hA hg k _ σ X₀ s₀ ψ w
  letI : Algebra R k := σ.toAlgebra
  obtain ⟨B, _, pr, -, hB, hBg, hsq, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R k A g hA hg
  have hsq' : IsPullback pr B.hom A.hom (spMap σ) := hsq
  have hW : WedgeO (OAff B.hom) := (hF k (Field.toIsField k) B g hB hBg).2.2
  let e : X₀ ≅ B.left := IsPullback.isoIsPullback _ _ w hsq'
  exact wedgeO_of_iso B.hom s₀ e (IsPullback.isoIsPullback_hom_snd _ _ w hsq') hW

end GlobalTheory.AbCohWedgeLift
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_fibre_pull_h1_abelian : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  atlas_forward_decl GlobalTheory.AbCohWedgeLift.wedgeO_fibre
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem artinian_pullHO_surjective : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w) := by
  intro R _ _ _ A _ g hA hsm k _ σ hσ X₀ s₀ ψ w
  have FF := GlobalTheory.T.abelian_over_field_axes_wedge
  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], Module.length R R ≤ n →
      ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
        (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R _ _ _ hlen A _ g hA hsm
      by_cases hF : IsField R
      · refine ⟨?_, GlobalTheory.T.primitive_of_axes_vanishing R A (FF R hF A g hA hsm).1⟩
        intro k _ σ hσ X₀ s₀ ψ w
        letI := hF.toField
        exact GlobalTheory.T.pull_h1_surjective_bijective_fibre R k σ ⟨σ.injective, hσ⟩ _ _ X₀ s₀ ψ w
      · obtain ⟨t, ht0, htm, hlt⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).2 hF
        obtain ⟨n0, hn0⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).1
        have htop : Ideal.span {t} ≠ ⊤ := by
          intro h
          have hu : IsUnit t := by simpa [Ideal.span_singleton_eq_top] using h
          apply hF
          have hm : IsLocalRing.maximalIdeal R = ⊥ := by
            rw [eq_bot_iff]; intro a ha
            have := htm a ha
            simpa [hu.mul_left_eq_zero] using this
          exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hm
        haveI : Nontrivial (R ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 htop
        haveI : IsLocalRing (R ⧸ Ideal.span {t}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        obtain ⟨n1, hn1⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem (R ⧸ Ideal.span {t})).1
        have hlt' : n1 < n := by
          rw [hn0, hn1] at hlt; rw [hn0] at hlen
          exact lt_of_lt_of_le (by exact_mod_cast hlt) (by exact_mod_cast hlen)
        have IH := ih n1 hlt' (R ⧸ Ideal.span {t}) (le_of_eq hn1)
        exact ⟨GlobalTheory.T.artinian_lift_axes_wedge R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ IH B g hB hs) A g hA hsm,
          GlobalTheory.T.artinian_lift_axes_wedge_local R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ (IH B g hB hs).2) A g hA hsm⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).1
  have h1 := (key n R (le_of_eq hn) A g hA hsm).1 k σ hσ X₀ s₀ ψ w
  exact ⟨h1, GlobalTheory.T.surjective_pullHO2_of_pullHO1 _ _ _ _ _ _ _ _ w.w h1 (GlobalTheory.T.closed_fibre_pull_h1_abelian FF R A g hA hsm k σ X₀ s₀ ψ w)⟩

end GlobalTheory.AbCoh
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w) := by
  atlas_forward_decl GlobalTheory.AbCoh.artinian_pullHO_surjective
end
