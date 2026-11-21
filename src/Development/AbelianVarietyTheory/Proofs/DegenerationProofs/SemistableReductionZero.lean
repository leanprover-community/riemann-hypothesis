import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyPotentialSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_potential_semiAbelian_model : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_isSemiAbelian | exact GlobalTheory.SS.potModel_isSemiAbelian | (intros; apply GlobalTheory.SS.potModel_isSemiAbelian <;> assumption)
end

section
universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtTorus

theorem isTorus_splitTorus (k : Type u) [Field k] (X : Type u) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] : IsTorus (splitTorus (Spec (CommRingCat.of k)) X) where
  comm := GlobalTheory.Diag.isCommMonObj _ X
  finiteType := inferInstance
  quasiCompact := inferInstance
  splits := ⟨k, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    GlobalTheory.Diag.baseChangeIso _ X, GlobalTheory.Diag.baseChangeIso_isMonHom _ X⟩

def torusExtOfSplit {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    (E : TorusExtension G) : TorusExt G :=
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  { B := E.B
    isAbelian := E.isAbelian
    q := E.q
    q_hom := E.q_hom
    q_flat := E.q_flat
    q_surjective := E.q_surjective
    q_quasiCompact := E.q_quasiCompact
    T₀ := splitTorus (Spec (CommRingCat.of k)) E.X
    isTorus := isTorus_splitTorus k E.X
    i := E.i
    i_hom := E.i_hom
    isKernel := E.isKernel }

theorem nonempty_torusExt_of_split : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExtension G) → Nonempty (TorusExt G) :=
  fun _ _ _ _ h => h.map torusExtOfSplit

end GlobalTheory.SplitExtTorus
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_dvr_torusExtension_specialFibre' : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [IsAdicComplete (IsLocalRing.maximalIdeal V') V'] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], IsSemiAbelian G → ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''), Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧ IsLocalHom (algebraMap V' V'') ∧ IsSemiAbelian (baseChange V' V'' G) ∧ Nonempty (TorusExtension (specialFibre V'' (baseChange V' V'' G))) := by
  first | exact @GlobalTheory.exists_finite_dvr_torusExtension_specialFibre | exact GlobalTheory.exists_finite_dvr_torusExtension_specialFibre | (intros; apply GlobalTheory.exists_finite_dvr_torusExtension_specialFibre <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SS

theorem baseChange_iso_tower (K K' V' V'' L : Type) [CommRing K] [CommRing K'] [CommRing V'] [CommRing V''] [CommRing L]
    [Algebra K K'] [Algebra V' K'] [Algebra V' V''] [Algebra V'' L] [Algebra K L] (j : K' →+* L)
    (t : j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V''))
    (e₂ : algebraMap K L = j.comp (algebraMap K K'))
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G]
    (e : baseChange V' K' G ≅ baseChange K K' A) (he : IsMonHom e.hom) :
    ∃ e : baseChange V'' L (baseChange V' V'' G) ≅ baseChange K L A, IsMonHom e.hom := by
  have s₁ : specMap V'' L ≫ specMap V' V'' = spMap j ≫ specMap V' K' := by
    show spMap (algebraMap V'' L) ≫ spMap (algebraMap V' V'') = spMap j ≫ spMap (algebraMap V' K')
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, t]
  have s₂ : spMap j ≫ 𝟙 _ ≫ specMap K K' = specMap K L := by
    show spMap j ≫ 𝟙 _ ≫ spMap (algebraMap K K') = spMap (algebraMap K L)
    rw [Category.id_comp, e₂, ← Spec.map_comp]; rfl
  have p₁ := ((isGrpPullback_pullback (baseChange V' V'' G) (specMap V'' L)).comp
    (isGrpPullback_pullback G (specMap V' V''))).congr s₁ rfl
  have p₂ := (isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    (isGrpPullback_pullback G (specMap V' K'))
  have p₃ := ((isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (specMap K K')))).congr s₂ rfl
  obtain ⟨i₁, hi₁, -⟩ := grpPullback_iso p₁ p₂
  obtain ⟨i₂, hi₂, -⟩ := grpPullback_iso p₃ (isGrpPullback_pullback A (specMap K L))
  refine ⟨i₁ ≪≫ i₂, ?_⟩
  rw [Iso.trans_hom]; infer_instance

theorem exists_finite_frac (V' K' V'' L : Type) [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    [CommRing V''] [IsDomain V''] [Algebra V' V''] [Field L] [Algebra V'' L] [IsFractionRing V'' L]
    (hf : Module.Finite V' V'') (hi : Function.Injective (algebraMap V' V'')) :
    ∃ j : K' →+* L, j.Finite ∧ j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') := by
  have : FaithfulSMul V' V'' := (faithfulSMul_iff_algebraMap_injective V' V'').2 hi
  have hinj : Function.Injective ((algebraMap V'' L).comp (algebraMap V' V'')) :=
    (IsFractionRing.injective V'' L).comp hi
  obtain ⟨j, t⟩ : ∃ j : K' →+* L, j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') :=
    ⟨IsFractionRing.lift (K := K') hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩
  let a₁ : Algebra V' L := ((algebraMap V'' L).comp (algebraMap V' V'')).toAlgebra
  let a₂ : Algebra K' L := j.toAlgebra
  have : IsScalarTower V' V'' L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V' K' L := IsScalarTower.of_algebraMap_eq' t.symm
  have : IsLocalization (Algebra.algebraMapSubmonoid V'' (nonZeroDivisors V')) L := inferInstance
  have h : Module.Finite K' L := Module.Finite.of_isLocalization V' V'' (nonZeroDivisors V')
  exact ⟨j, h, t⟩

theorem model_finite_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  intro V _ _ _ K _ _ _ A _ K' _ _ hK V' _ _ _ _ _ hc G _ ⟨e, he⟩ V'' _ _ _ hf hi
  obtain ⟨j, hj, t⟩ := exists_finite_frac V' K' V'' (FractionRing V'') hf hi
  let aK : Algebra K (FractionRing V'') := (j.comp (algebraMap K K')).toAlgebra
  have e₂ : algebraMap K (FractionRing V'') = j.comp (algebraMap K K') := rfl
  refine ⟨aK, hj.comp (RingHom.finite_algebraMap.2 hK), ?_, baseChange_iso_tower K K' V' V'' _ j t e₂ A G e he⟩
  rw [e₂, ← RingHom.comp_assoc, ← t, RingHom.comp_assoc, hc, RingHom.comp_assoc]

end GlobalTheory.SS
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupScheme_model_finite_ring_extension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  first | exact @GlobalTheory.SS.model_finite_ext | exact GlobalTheory.SS.model_finite_ext | (intros; apply GlobalTheory.SS.model_finite_ext <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_torusExtension_of_potModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  intro V _ _ _ _ K _ _ _ _ A _ hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, hW, G, _, hmod, hG⟩ := hP
  have hinj : Function.Injective (algebraMap V W) := by
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  haveI hKL : FiniteDimensional K L := by
    letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
    haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
    haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
    exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)
  obtain ⟨W', _, _, _, hW', _, hfin', hinj', -, hG', hT⟩ := GlobalTheory.T.exists_finite_dvr_torusExtension_specialFibre' W G hG
  obtain ⟨_, hK', e', hmod'⟩ := GlobalTheory.T.groupScheme_model_finite_ring_extension V K A L W e G hmod W' hfin' hinj'
  letI : Algebra V W' := ((algebraMap W W').comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W W' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨FractionRing W', inferInstance, inferInstance, hK', W', inferInstance, inferInstance, inferInstance, hW',
    inferInstance, inferInstance, inferInstance, Module.Finite.trans W W', hinj'.comp hinj, e',
    baseChange W W' G, inferInstance, hG', hmod', hT⟩

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  atlas_forward_decl GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistable_of_potModel_semiAbelian : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  intro h
  refine ⟨?_, ?_⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i8, i9, i10, h1, h2, h3, G, i11,
      hG.comm, hG.smooth, hG.separated, hG.quasiCompact, he, GlobalTheory.SplitExtTorus.nonempty_torusExt_of_split _ _ hT⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, inferInstance, h3, G, i11, hG, he, hT⟩

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_of_potential_semiAbelian_model : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  atlas_forward_decl GlobalTheory.SS.semistable_of_potModel_semiAbelian
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistableReduction_zero : SemistableReductionZero := (GlobalTheory.T.semistable_of_potential_semiAbelian_model GlobalTheory.T.abelianVariety_potential_semiAbelian_model).1

end GlobalTheory.SS
end
