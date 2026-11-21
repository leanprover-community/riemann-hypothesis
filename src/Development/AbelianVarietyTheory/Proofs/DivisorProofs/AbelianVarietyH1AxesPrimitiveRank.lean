import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lid_baseChange_self {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (x : K ⊗[K] M) :
    TensorProduct.lid K N (f.baseChange K x) = f (TensorProduct.lid K M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem nonempty_equiv_homology_of_baseChange_self {K : Type} [Field K]
    (S : ShortComplex (ModuleCat.{0} K)) {H : Type} [AddCommGroup H] [Module K H]
    (θ : LinearMap.ker (S.g.hom.baseChange K) →ₗ[K] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (S.f.hom.baseChange K)) :
    Nonempty (H ≃ₗ[K] S.homology) := by
  have hmem : ∀ x : LinearMap.ker S.g.hom,
      (TensorProduct.lid K S.X₂).symm x.1 ∈ LinearMap.ker (S.g.hom.baseChange K) := by
    intro x
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid K S.X₃).injective
    rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, map_zero]
    exact x.2
  let q : LinearMap.ker S.g.hom →ₗ[K] H :=
    θ ∘ₗ ((((TensorProduct.lid K S.X₂).symm : S.X₂ →ₗ[K] K ⊗[K] S.X₂) ∘ₗ
      (LinearMap.ker S.g.hom).subtype).codRestrict _ hmem)
  have hq : ∀ x, q x = θ ⟨(TensorProduct.lid K S.X₂).symm x.1, hmem x⟩ := fun x => rfl
  have hsurj : Function.Surjective q := by
    intro h
    obtain ⟨z, rfl⟩ := hs h
    have hz : TensorProduct.lid K S.X₂ z.1 ∈ LinearMap.ker S.g.hom := by
      rw [LinearMap.mem_ker, ← lid_baseChange_self, z.2, map_zero]
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [hq]
    congr 1
    exact Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  have hker : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    rw [LinearMap.mem_ker, hq, hk]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(TensorProduct.lid K S.X₁).symm y, ?_⟩
      apply (TensorProduct.lid K S.X₂).injective
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨TensorProduct.lid K S.X₁ y, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid K S.X₂) hy
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply] at this
      exact this
  exact ⟨((q.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
    S.moduleCatHomologyIso.toLinearEquiv.symm)⟩

theorem hO_equiv_cech : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ]
    [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧
      Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  intro K _ X s κ _ _ D hsep haff hcov
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology K X s κ D hsep haff hcov
  have hsp : spMap (algebraMap K K) = 𝟙 (Sp K) := by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  have hP : IsPullback (𝟙 X) s s (spMap (algebraMap K K)) := by
    rw [hsp]; exact IsPullback.id_horiz s
  obtain ⟨h1s, h1k, h2s, h2k⟩ := M.exact hP
  obtain ⟨e1⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 0 1 2) (M.θ1 hP) h1s h1k
  obtain ⟨e2⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 1 2 3) (M.θ2 hP) h2s h2k
  exact ⟨⟨e1 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.symm⟩,
    ⟨e2 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 1 2 3 (by simp) (by simp)).toLinearEquiv.symm⟩⟩

end GlobalTheory.AbCoh
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_structure_sheaf_iso : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧ Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  atlas_forward_decl GlobalTheory.AbCoh.hO_equiv_cech
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_trivial_bundle_abelian : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  first | exact @GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two | exact GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two | (intros; apply GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.Axes

theorem exists_cover {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨t, ht, hU⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨(isCompact_univ : IsCompact (Set.univ : Set X)), isOpen_univ⟩
  haveI := ht.fintype
  refine ⟨Fintype.card t, fun i ↦ ((Fintype.equivFin t).symm i).1.1, fun i ↦ ((Fintype.equivFin t).symm i).1.2, ?_⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨Fintype.equivFin t ⟨i, hi⟩, ?_⟩
  simpa using hxi

theorem ho1_fin {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  haveI := hA.proper
  obtain ⟨n, D, hD, hcov⟩ := exists_cover A.hom
  obtain ⟨⟨e⟩, -⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hf, h1, -⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hA hg (Fin n) D hD hcov
  haveI := hf 1
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h1⟩

theorem smooth_sq {K : Type} [Field K] {A : Over (Sp K)} {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom A.hom).flip hg
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g g _ _

theorem pO1_comp {K : Type} [Field K] {X Y Z : Over (Sp K)} (f : X ⟶ Y) (h : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ h) a = pO1 f (pO1 h a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 K K Z.left Y.left Z.hom Y.hom (RingHom.id K) h.left (ovw h) K X.left X.hom
    (RingHom.id K) f.left (ovw f) (RingHom.id K) (f ≫ h).left (ovw (f ≫ h)) (by simp)
    (fun _ ↦ rfl)).1 a).symm

theorem pO1_id {K : Type} [Field K] (X : Over (Sp K)) (a : HO1 X.hom) : pO1 (𝟙 X) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 K X).1 a

theorem pO1_unit {K : Type} [Field K] {X Y : Over (Sp K)} (f : X ⟶ 𝟙_ (Over (Sp K))) (h : 𝟙_ (Over (Sp K)) ⟶ Y)
    (a : HO1 Y.hom) : pO1 (f ≫ h) a = 0 := by
  have : IsAffine (𝟙_ (Over (Sp K))).left := by
    show IsAffine (Spec _); infer_instance
  haveI := (GlobalTheory.AbCoh.Vanish.main.1 K _ (𝟙_ (Over (Sp K))).hom this).1
  rw [pO1_comp, Subsingleton.elim (pO1 h a) 0, map_zero]

def axesRes {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] : HO1 (A ⊗ A).hom →ₗ[K] HO1 A.hom × HO1 A.hom :=
  (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))).prod (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))

def projSum {K : Type} [Field K] (A : Over (Sp K)) : HO1 A.hom × HO1 A.hom →ₗ[K] HO1 (A ⊗ A).hom :=
  (pO1 (fst A A)).coprod (pO1 (snd A A))

theorem axesRes_projSum {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (x : HO1 A.hom × HO1 A.hom) :
    axesRes A (projSum A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_ <;>
  simp only [axesRes, projSum, LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply, map_add,
    ← pO1_comp, lift_fst, lift_snd, pO1_id, pO1_unit, Prod.fst_add, Prod.snd_add, add_zero, zero_add]

theorem axesRes_injective {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : Function.Injective (axesRes A) := by
  obtain ⟨h1, h2⟩ := ho1_fin A g hA hg
  obtain ⟨h3, h4⟩ := ho1_fin (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_sq hg)
  have hinj : Function.Injective (projSum A) := Function.LeftInverse.injective (axesRes_projSum A)
  have hsurj : Function.Surjective (projSum A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_prod, h2, h4])).1 hinj
  intro y y' h
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨x', rfl⟩ := hsurj y'
  rw [axesRes_projSum, axesRes_projSum] at h
  rw [h]

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A ∧ GlobalTheory.AbCoh.StructureSheafH1Primitive A ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K _ _ A _ g hA hg
  have hN := axesRes_injective A g hA hg
  refine ⟨fun y h₁ h₂ ↦ ?_, fun x ↦ ?_, (ho1_fin A g hA hg).2⟩
  · refine hN ?_
    refine Prod.ext ?_ ?_ <;> simp only [axesRes, LinearMap.prod_apply, Function.prod, h₁, h₂, map_zero, Prod.fst_zero, Prod.snd_zero]
  · have := axesRes_projSum A (x, x)
    refine hN ?_
    rw [show pO1 (fst A A) x + pO1 (snd A A) x = projSum A (x, x) from rfl, this]
    refine Prod.ext ?_ ?_ <;> simp only [axesRes, LinearMap.prod_apply, Function.prod, ← pO1_comp, pO1_id, MonObj.lift_comp_one_left, MonObj.lift_comp_one_right]

end GlobalTheory.AbCoh.Axes
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_variety_h1_axes_primitive_rank : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A ∧ GlobalTheory.AbCoh.StructureSheafH1Primitive A ∧ Module.finrank K (HO1 A.hom) = g := by
  atlas_forward_decl GlobalTheory.AbCoh.Axes.main
end
