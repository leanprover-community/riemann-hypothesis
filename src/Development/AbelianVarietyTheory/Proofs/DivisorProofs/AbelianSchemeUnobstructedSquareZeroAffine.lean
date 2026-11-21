import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndPrimitiveOneForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BasisO

theorem restrict_bijective_one : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type)
    [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X),
    (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) →
    (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) →
    Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  intro R _ X s C' _ _ G h1 h2
  have H := hasLoc_OAff s
  have hcov := BasisExt.hcov_of_basis s G h1
  have hdir := BasisExt.hdir_of_basis s G h2
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

end GlobalTheory.Obs.BasisO
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X), (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) → (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) → Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  atlas_forward_decl GlobalTheory.Obs.BasisO.restrict_bijective_one
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroBC

theorem preimage_surj : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  intro R₀ R₁ _ _ _ q hq X₀ X₁ s₀ s₁ pr hp U
  have hqs : Function.Surjective (q : R₁ →+* R₀) := fun x ↦ ⟨algebraMap R₀ R₁ x, q.commutes x⟩
  have hid : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun x ↦ q.commutes x
    rw [this]
    exact Spec.map_id _
  let σ : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀)) (by rw [Category.id_comp, Category.assoc, hid, Category.comp_id])
  have hσ : σ ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hσ2 : σ ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (σ ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hσ, hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hleft : IsPullback σ s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hσ2 hp
  have hk2 : RingHom.ker (q : R₁ →+* R₀) ^ 2 = 0 := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    exact hq a b (RingHom.mem_ker.1 ha) (RingHom.mem_ker.1 hb)
  have hsurj : Surjective σ := surjective_of_isPullback_sqZero hk2 hqs rfl hleft
  refine ⟨σ ⁻¹ᵁ U, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hsurj.surj x
  have e : pr (σ y) = y := by
    have := congrArg (fun f : X₀ ⟶ X₀ ↦ f y) hσ
    simpa only [Scheme.Hom.comp_apply] using this.trans (by simp)
  change σ (pr (σ y)) ∈ U ↔ σ y ∈ U
  rw [e]

end GlobalTheory.SqZeroBC
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  atlas_forward_decl GlobalTheory.SqZeroBC.preimage_surj
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem isPushout_sec (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (U : X₀.affineOpens) :
    IsPushout (secMap s₀ U.1) (CommRingCat.ofHom (algebraMap R₀ R₁)) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl)
      (secMap s₁ (pr ⁻¹ᵁ U.1)) := by
  have po := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) U.2)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl

theorem tensHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)), Function.Bijective (GlobalTheory.Obs.BC.tensHom hp.w U hU) := by
  intro R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U hU
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) := (prSec hp.w U hU).toAlgebra
  haveI : IsScalarTower R₀ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun r ↦
    ((semiHom_secPull hp.w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r).symm
  have hpo : Algebra.IsPushout R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_sec R₀ R₁ X₀ X₁ s₀ s₁ pr hp U).flip
  have e : ∀ x, tensHom hp.w U hU x = Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r b => rw [tensHom_tmul, Algebra.IsPushout.equiv_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have : ⇑(tensHom hp.w U hU) = ⇑(Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1))) := funext e
  rw [this]
  exact (Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1))).bijective

end GlobalTheory.Obs.BC
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTensorSectionsHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)), Function.Bijective (GlobalTheory.Obs.BC.tensHom hp.w U hU) := by
  atlas_forward_decl GlobalTheory.Obs.BC.tensHom_bijective
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.BC

theorem natCoef_pull1_bijective (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R)
    (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) :
    (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  intro hb
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom
  have hαβ : ∀ T (b : F'.obj T), α T (β T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b
  have hβα : ∀ T (b : F.obj T), β T (α T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := by
    intro T T' a b
    apply (hb T').1
    rw [hαβ, nat, hαβ]
  have smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := by
    intro T r b
    apply (hb T).1
    rw [hαβ, smul, hαβ]
  let m := GlobalTheory.Obs.BC.natCoef α nat smul
  let n := GlobalTheory.Obs.BC.natCoef β natβ smulβ
  have left : ∀ c, n.pull1 (m.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hβα T' _
  have right : ∀ c, m.pull1 (n.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F' c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hαβ T' _
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end GlobalTheory.Obs.BC
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_bijective_coefficients_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R) (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b)) (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b), (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  atlas_forward_decl GlobalTheory.Obs.BC.natCoef_pull1_bijective
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem preAff_basis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ pr _ hsurj
  refine ⟨?_, ?_⟩
  · intro x U hx
    obtain ⟨V, rfl⟩ := hsurj U
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (show pr.base x ∈ V from hx) V.isOpen
    exact ⟨Opposite.op ⟨W, hW⟩, hxW, pr.preimage_mono hWV⟩
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨V, rfl⟩ := hsurj U
    have hmem : pr.base x ∈ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := ⟨⟨h₁, h₂⟩, hx⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open hmem (t₁.unop.1 ⊓ t₂.unop.1 ⊓ V).isOpen
    have hWV' : W ≤ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := hWV
    exact ⟨Opposite.op ⟨W, hW⟩, ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₁.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_left) : W ≤ t₁.unop.1))).op⟩,
      ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₂.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_right) : W ≤ t₂.unop.1))).op⟩, hxW,
      pr.preimage_mono (le_trans hWV' inf_le_right)⟩

end GlobalTheory.Obs.BC
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpensPreimage_baseChange_isBasis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  atlas_forward_decl GlobalTheory.Obs.BC.preAff_basis
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem exists_affineOpen_nhds_le {X : Scheme.{0}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W : Set X) from hx) W.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

theorem pairBC_fst_basis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ Y₀ Y₁ pr pr' _ _ f₀ f₁ e hsurj
  constructor
  · intro x U hx
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    obtain ⟨V, hfV, -⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) ⊤ trivial
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x) (W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨hy, hfV⟩
    refine ⟨Opposite.op (⟨(U', V), hU'le.trans inf_le_right⟩ : Pair f₀), ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans inf_le_left)
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    have hy₁ : pr' x ∈ t₁.unop.1.1.1 := h₁
    have hy₂ : pr' x ∈ t₂.unop.1.1.1 := h₂
    have hf₁ : f₀ (pr' x) ∈ t₁.unop.1.2.1 := t₁.unop.2 hy₁
    have hf₂ : f₀ (pr' x) ∈ t₂.unop.1.2.1 := t₂.unop.2 hy₂
    obtain ⟨V, hfV, hVle⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) (t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hf₁, hf₂⟩
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x)
      (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1 ⊓ W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨⟨⟨hy₁, hy₂⟩, hy⟩, hfV⟩
    let p : Pair f₀ := ⟨(U', V), hU'le.trans inf_le_right⟩
    have hp₁ : p ≤ t₁.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)), hVle.trans inf_le_left⟩)
    have hp₂ : p ≤ t₂.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)), hVle.trans inf_le_right⟩)
    refine ⟨Opposite.op p, ⟨(homOfLE hp₁).op⟩, ⟨(homOfLE hp₂).op⟩, ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans (inf_le_left.trans inf_le_right))

end GlobalTheory.Obs.BC
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePairPreimage_baseChange_fst_isBasis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  atlas_forward_decl GlobalTheory.Obs.BC.pairBC_fst_basis
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open Opposite
namespace GlobalTheory.Obs.BC

theorem tensPair_extMap_pairPull : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  intro R₀ R₁ _ _ _ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' _ _ w w' f₀ f₁ h₀ h₁ e p b
  have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (U : X₀.Opens) (V : Y₁.Opens) (k : V ≤ g ⁻¹ᵁ U) (k' : V ≤ g' ⁻¹ᵁ U),
      g.appLE U V k = g'.appLE U V k' := by
    rintro g _ rfl U V k k'; rfl
  change tensHom w' (unop ((pairFst f₀).obj p)) _ (extHom R₁ (coefHom (pairPull h₀) p) b) =
    GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop) (tensHom w (unop ((pairSnd f₀).obj p)) _ b)
  induction b using TensorProduct.induction_on with
  | zero => repeat erw [map_zero]
            all_goals exact rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]; exact rfl
  | tmul r x =>
    refine (congrArg (tensHom w' _ _) (Algebra.TensorProduct.map_tmul _ _ r x)).trans ?_
    refine (tensHom_tmul w' _ _ r _).trans ?_
    have h2 := congrArg (GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop))
      (tensHom_tmul w (unop ((pairSnd f₀).obj p)) ((isAffine_aff _).preimage pr) r x)
    refine Eq.trans ?_ h2.symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    · exact ((semiHom_secPull h₁ (pairBCObj pr pr' e p.unop)).map_algebraMap r).symm
    · change (pr'.appLE _ _ _).hom ((f₀.appLE _ _ _).hom x) = (f₁.appLE _ _ _).hom ((pr.appLE _ _ _).hom x)
      have c1 := Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1 (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl
      have c2 := Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1 (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl
        (pairBCObj pr pr' e p.unop).2
      rw [key (pr' ≫ f₀) (f₁ ≫ pr) e.symm _ _ _ (by rw [e]; exact pr'.preimage_mono p.unop.2)] at c1
      exact (congrArg (fun t ↦ t.hom x) c1).trans (congrArg (fun t ↦ t.hom x) c2).symm

end GlobalTheory.Obs.BC
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  atlas_forward_decl GlobalTheory.Obs.BC.tensPair_extMap_pairPull
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffineHom_of_isPullback {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback hp.flip inferInstance

theorem res_bijective (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] : Function.Bijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 :=
  have H := GlobalTheory.T.affineOpensPreimage_baseChange_isBasis X₀ X₁ pr (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp)
  GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ X₁ s₁ _ (preAff pr) H.1 H.2

theorem tens_bijective {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) [IsAffineHom pr] :
    Function.Bijective (tensCoef hp.w).pull1 := by
  exact GlobalTheory.T.natural_bijective_coefficients_pull1_bijective R₁ _ _ _ _ (tensCoef hp.w).naturality (tensCoef hp.w).smul fun U ↦ GlobalTheory.T.baseChangeTensorSectionsHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop _

def trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CatCoh.H1 (OAff s₁) ≃+ CatCoh.H1 (ext R₁ (OAff s₀)) :=
  haveI := isAffineHom_of_isPullback hp
  (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 (res_bijective q hq hp)).trans
    (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).symm

theorem tens_trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] (c : CatCoh.H1 (OAff s₁)) :
    (tensCoef hp.w).pull1 (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) = (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c :=
  (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).apply_symm_apply _

section Compat

variable {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr] [IsAffineHom pr']
  {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁} (e : f₁ ≫ pr = pr' ≫ f₀)

def pullBC (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preAff pr ⋙ OAff s₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((pairBC pr pr' e).obj p)
  naturality a b := (pairPull h₁).naturality ((pairBC pr pr' e).map a) b
  smul p r b := (pairPull h₁).smul ((pairBC pr pr' e).obj p) r b

def resBC : CoefMap (RingHom.id R₁) (preAff pr' ⋙ OAff t₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end Compat

end GlobalTheory.Obs.BC

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem extendedCoefficients_pullback_compat (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0)
    {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀}
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀)
    (c : CatCoh.H1 (OAff s₁)) (c' : CatCoh.H1 (OAff t₁))
    (H : IsExtendedPullbackDegOne R₁ h₀ (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) :
    IsPullO h₁ c c' := by
  haveI := isAffineHom_of_isPullback hp
  haveI := isAffineHom_of_isPullback hp'
  have kd := tens_trEquiv q hq hp c
  have kd' := tens_trEquiv q hq hp' c'
  let Φ := CoefMap.restrict (OPair f₁ t₁) (pairBC pr pr' e)
  have inj : Function.Injective Φ.pull1 := by
    intro x x' hx
    obtain ⟨y, rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x
    obtain ⟨y', rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x'
    have HH := GlobalTheory.T.affinePairPreimage_baseChange_fst_isBasis X₀ X₁ Y₀ Y₁ pr pr' f₀ f₁ e (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp')
    have B := GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ Y₁ t₁ _ (pairBC pr pr' e ⋙ pairFst f₁) HH.1 HH.2
    have k : ∀ z, Φ.pull1 ((pairRes f₁ t₁).pull1 z) =
        (CoefMap.restrict (OAff t₁) (pairBC pr pr' e ⋙ pairFst f₁)).pull1 z := by
      intro z; obtain ⟨z, rfl⟩ := H1.mk_surjective _ z; rfl
    rw [k, k] at hx
    rw [B.1 hx]
  have k1 : Φ.pull1 ((pairPull h₁).pull1 c) = (tensPair hp'.w e).pull1 ((extMap R₁ (pairPull h₀)).pull1
      (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c)) := by
    have a1 : Φ.pull1 ((pairPull h₁).pull1 c) =
        (pullBC e h₁).pull1 ((CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c) := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [a1, ← kd, ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp.w).comp (pullBC e h₁))
      ((extMap R₁ (pairPull h₀)).comp (tensPair hp'.w e)) (𝟙 (pairSnd f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff s₀)) _ b)).trans ?_
    exact GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback R₀ R₁ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' hp.w hp'.w f₀ f₁ h₀ h₁ e p b
  have k2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') = (tensPair hp'.w e).pull1 ((extMap R₁ (pairRes f₀ t₀)).pull1
      (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) := by
    have a2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') =
        (resBC e).pull1 ((CoefMap.restrict (OAff t₁) (preAff pr')).pull1 c') := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c'; rfl
    rw [a2, ← kd', ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp'.w).comp (resBC e))
      ((extMap R₁ (pairRes f₀ t₀)).comp (tensPair hp'.w e)) (𝟙 (pairFst f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff t₀)) _ b)).trans ?_
    have hc : coefHom (pairRes f₀ t₀) p = AlgHom.id R₀ _ := AlgHom.ext fun _ ↦ rfl
    change (tensPair hp'.w e).α p (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = _
    rw [hc]
    exact congrArg ((tensPair hp'.w e).α p) (DFunLike.congr_fun Algebra.TensorProduct.map_id b)
  apply inj
  unfold IsExtendedPullbackDegOne at H
  rw [k1, k2, H]

end GlobalTheory.Obs.BC

theorem GlobalTheory.Obs.BC.extO1 : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' :=
  fun _ _ _ _ _ q hq ↦ ⟨GlobalTheory.Obs.BC.trEquiv q hq, fun _ _ _ _ _ hp _ _ _ _ _ hp' _ _ h₀ h₁ e c c' H ↦
    GlobalTheory.Obs.BC.extendedCoefficients_pullback_compat q hq hp hp' h₀ h₁ e c c' H⟩
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' := by
  atlas_forward_decl GlobalTheory.Obs.BC.extO1
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem axesE1_of_axesO1 : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  intro hO R₀ R₁ _ _ _ q hq A _ g hab hsm c h₁ h₂
  obtain ⟨B, hB, pr, pr', habB, hsmB, hp, hp', -, -, -, hl, hr⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hab hsm
  letI : GrpObj B := hB
  obtain ⟨e, he⟩ := GlobalTheory.T.h1_structure_base_change_extension R₀ R₁ q hq
  set c₁ := (e _ _ _ _ _ hp').symm c with hc₁
  have hc : e _ _ _ _ _ hp' c₁ = c := by simp [hc₁]
  have hl' : IsPullO (overW (lift (𝟙 B) 1)) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift (𝟙 A) 1)) (overW (lift (𝟙 B) 1)) hl c₁ 0 ?_
    rw [hc, map_zero]; exact h₁
  have hr' : IsPullO (overW (lift 1 (𝟙 B))) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift 1 (𝟙 A))) (overW (lift 1 (𝟙 B))) hr c₁ 0 ?_
    rw [hc, map_zero]; exact h₂
  have h0 : c₁ = 0 := hO R₁ B g habB hsmB c₁ hl' hr'
  rw [← hc, h0, map_zero]

end GlobalTheory.Obs
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axes_vanishing_degree_one_extension : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  atlas_forward_decl GlobalTheory.Obs.axesE1_of_axesO1
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem globalFunctionsConstant_of_constant_after_baseChange (s : X ⟶ Sp R) (hU : UConst s) : CohomZeroIsConstants (OAff s) := by
  refine hU R X s (𝟙 X) ?_
  rw [Algebra.algebraMap_self, Cris.spMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {s : X ⟶ Sp R} {n : ℕ} (fr : Frame (OAff s) n) (hc : CohomZeroIsConstants (OAff s))

theorem coboundaryZero_frame_vectorField_globalForm_eq_zero (i : Fin n) (ω : GlobForm s) : d0 (OAff s) (fun T ↦ fr.δ i T (ω.1 T)) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply, ω.2 φ, fr.nat]
  exact sub_self _

def coef (i : Fin n) (ω : GlobForm s) : R := (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose

theorem coef_spec (i : Fin n) (ω : GlobForm s) (T : AffOp X) :
    fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) (coef fr hc i ω) :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose_spec T

theorem coef_eq (i : Fin n) (ω : GlobForm s) (r : R)
    (h : ∀ T, fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) r) : coef fr hc i ω = r :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).unique (coef_spec fr hc i ω) h

def coefL : GlobForm s →ₗ[R] (Fin n → R) where
  toFun ω i := coef fr hc i ω
  map_add' ω ω' := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    rw [coef_spec fr hc i ω T, coef_spec fr hc i ω' T]
  map_smul' r ω := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply,
      smul_eq_mul, map_mul, Algebra.smul_def]
    rw [coef_spec fr hc i ω T]

def sumL : (Fin n → R) →ₗ[R] GlobForm s where
  toFun c := ∑ i, c i • fr.w i
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, mul_smul]

theorem sumL_coefL (ω : GlobForm s) : sumL fr (coefL fr hc ω) = ω := by
  apply Subtype.ext
  funext T
  conv_rhs => rw [fr.sum T (ω.1 T)]
  simp only [sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coef_spec, algebraMap_smul]

include fr hc in

theorem projective : Module.Projective R (GlobForm s) :=
  Module.Projective.of_split (coefL fr hc) (sumL fr) (LinearMap.ext (sumL_coefL fr hc))

def back (U : AffOp X) (x : Ω[Sec s U.unop.1⁄R]) : Sec s U.unop.1 ⊗[R] GlobForm s :=
  ∑ i, (fr.δ i U x : Sec s U.unop.1) ⊗ₜ[R] fr.w i

theorem back_add (U : AffOp X) (x y : Ω[Sec s U.unop.1⁄R]) : back fr U (x + y) = back fr U x + back fr U y := by
  simp only [back, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]

include fr hc in

theorem par (U : AffOp X) : IsBaseChange (Sec s U.unop.1) (evForm s U) := by
  change Function.Bijective (TensorProduct.lift _)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨back fr U, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp [back]
    | tmul a ω =>
      simp only [TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
      conv_rhs => rw [← sumL_coefL fr hc ω]
      simp only [back, sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      change fr.δ i U (a • ω.1 U) = coef fr hc i ω • a
      rw [(fr.δ i U).map_smul a (ω.1 U), coef_spec fr hc i ω U, Algebra.smul_def, mul_comm]
      rfl
    | add t t' ht ht' => rw [map_add, back_add, ht, ht']
  · conv_rhs => rw [fr.sum U x]
    simp only [back, map_sum, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
    rfl

end GlobalTheory.FormsOnAb

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

theorem formSt_of (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
      GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) : FormSt := by
  intro R₀ _ A _ g hA hs
  obtain ⟨⟨n, ⟨fr⟩⟩, hU, hP⟩ := H R₀ A g hA hs
  have hc := globalFunctionsConstant_of_constant_after_baseChange A.hom hU
  refine ⟨fun U ↦ par fr hc U, projective fr hc, fun w wm w₁ w₂ hm h1 h2 ↦ ?_⟩
  rw [hm.eq_pullForm, h1.eq_pullForm, h2.eq_pullForm]
  exact hP w

end GlobalTheory.FormsOnAb
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → FormSt := by
  atlas_forward_decl GlobalTheory.FormsOnAb.formSt_of
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianUnobstructed_of_struct (hO : GlobalTheory.AbCoh.OStr)
    (hF : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧
        GlobalTheory.AbCoh.PrimF A) : GlobalTheory.Published.AbelianUnobstructed := by
  have hS : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b := by
    intro R _ A _ g hA hg
    obtain ⟨h1, h2, -, -⟩ := hO R A g hA hg
    exact ⟨h1, h2⟩
  exact GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension (GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure (GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames hF) (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish hS))
    (GlobalTheory.T.axes_vanishing_degree_one_extension (GlobalTheory.T.axesO1_of_projective_rank_cup hS)))

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure : GlobalTheory.AbCoh.OStr → (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → GlobalTheory.Published.AbelianUnobstructed := by
  atlas_forward_decl GlobalTheory.abelianUnobstructed_of_struct
end

section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnobTop.abelianUnobstructed : GlobalTheory.Published.AbelianUnobstructed :=
  GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure GlobalTheory.T.abelian_structure_cohomology_statement fun R _ A _ g hA hg =>
    ⟨(GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms R A g hA hg).1, GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA, (GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms R A g hA hg).2⟩
end
