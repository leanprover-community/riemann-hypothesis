import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeronStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselian
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.GenProj

theorem ext_of_dense {W X T Z : Scheme.{0}} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] {m m' : X ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : j ≫ m = j ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' := by
  let a : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m
  let b : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m' h₂.symm
  have : IsSeparated (Over.mk g).hom := ‹_›
  let c : Over.mk (j ≫ m ≫ g) ⟶ Over.mk (m ≫ g) := Over.homMk j
  have hc : c ≫ a = c ≫ b := by ext1; exact h₁
  have hk : (equalizer.ι a b).left.ker = ⊥ := by
    have e : (equalizer.lift c hc).left ≫ (equalizer.ι a b).left = j := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    have := (equalizer.lift c hc).left.le_ker_comp (equalizer.ι a b).left
    rw [e] at this
    exact le_bot_iff.mp (this.trans j.ker_eq_bot.le)
  have : IsIso (equalizer.ι a b).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b).left]
  exact congr($(equalizer.condition a b).left)

theorem eq_of_generic {S E U X X' A : Scheme.{0}} (i : E ⟶ S) [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (s : X ⟶ S) (s' : X' ⟶ S) [Flat s] [IsSeparated s'] (p : U ⟶ X) (q : U ⟶ X') [Flat p]
    (hs : p ≫ s = q ≫ s') (j : A ⟶ X) [Mono j] (j' : A ⟶ X')
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U) (t : Z ⟶ E), a ≫ p ≫ s = t ≫ i → ∃ c : Z ⟶ A, c ≫ j = a ≫ p ∧ c ≫ j' = a ≫ q)
    {Z : Scheme.{0}} (a b : Z ⟶ U) (hab : a ≫ p = b ≫ p) : a ≫ q = b ≫ q := by
  have key : pullback.fst p p ≫ q = pullback.snd p p ≫ q := by
    let w := pullback.fst p p ≫ p ≫ s
    have : Flat w := by dsimp only [w]; infer_instance
    refine ext_of_dense (pullback.fst w i) s' ?_ ?_
    · obtain ⟨c₁, h₁, h₁'⟩ := H _ (pullback.fst w i ≫ pullback.fst p p) (pullback.snd w i)
        (by rw [← pullback.condition]; simp [w])
      obtain ⟨c₂, h₂, h₂'⟩ := H _ (pullback.fst w i ≫ pullback.snd p p) (pullback.snd w i)
        (by rw [← pullback.condition, Category.assoc, ← pullback.condition_assoc])
      have e : c₁ = c₂ := by
        rw [← cancel_mono j, h₁, h₂, Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, ← h₁', ← h₂', e]
    · rw [Category.assoc, Category.assoc, ← hs, pullback.condition_assoc]
  have := congrArg (fun x => pullback.lift a b hab ≫ x) key
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

theorem exists_image {U X : Scheme.{0}} (p : U ⟶ X) [Flat p] [LocallyOfFinitePresentation p] :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme), p' ≫ V.ι = p ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' := by
  let V : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hr : Set.range p ⊆ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact subset_rfl
  have e : IsOpenImmersion.lift V.ι p hr ≫ V.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (IsOpenImmersion.lift V.ι p hr) (𝟙 U) V.ι p :=
    IsPullback.of_vert_isIso_mono ⟨by rw [e, Category.id_comp]⟩
  refine ⟨V, IsOpenImmersion.lift V.ι p hr, e, ?_, ?_, ⟨?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hP.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP.flip ‹_›
  · rintro ⟨_, u, rfl⟩
    refine ⟨u, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, e]; rfl

theorem exists_openImmersion {U X X' : Scheme.{0}} (p : U ⟶ X) (q : U ⟶ X') [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q]
    (H : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme) (h : V.toScheme ⟶ X'), p' ≫ V.ι = p ∧ Flat p' ∧ Surjective p' ∧
      p' ≫ h = q ∧ IsOpenImmersion h := by
  obtain ⟨V, p', hp, _, _, _⟩ := exists_image p
  obtain ⟨V', q', hq, _, _, _⟩ := exists_image q
  have H' : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p' = b ≫ p' ↔ a ≫ q' = b ≫ q' := by
    intro Z a b
    rw [← cancel_mono V.ι, ← cancel_mono V'.ι]
    simpa [hp, hq] using H Z a b
  let u := EffectiveEpi.desc p' q' (fun a b h => (H' _ a b).1 h)
  let v := EffectiveEpi.desc q' p' (fun a b h => (H' _ a b).2 h)
  have hu : p' ≫ u = q' := EffectiveEpi.fac _ _ _
  have hv : q' ≫ v = p' := EffectiveEpi.fac _ _ _
  have : IsIso u := ⟨v, by rw [← cancel_epi p', ← Category.assoc, hu, hv, Category.comp_id],
    by rw [← cancel_epi q', ← Category.assoc, hv, hu, Category.comp_id]⟩
  exact ⟨V, p', u ≫ V'.ι, hp, ‹_›, ‹_›, by rw [← Category.assoc, hu, hq], inferInstance⟩

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => (M.prod N).e.inv.left ≫ q) h4).symm.trans h2)

theorem exists_lift_j (M : Model R A) {Z : Scheme.{0}} (a : Z ⟶ M.Y.left) (t : Z ⟶ Sp K)
    (h : a ≫ M.Y.hom = t ≫ spMap (algebraMap R K)) : ∃ d : Z ⟶ A.left, d ≫ M.j = a := by
  refine ⟨pullback.lift a t h ≫ M.e.hom.left, ?_⟩
  have e : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  unfold Model.j
  rw [Category.assoc, ← Category.assoc M.e.hom.left, e]
  exact (congrArg _ (Category.id_comp _)).trans (pullback.lift_fst _ _ _)

theorem mono_j [IsFractionRing R K] (M : Model R A) : Mono M.j := by
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : Mono (pullback.fst M.Y.hom (spMap (algebraMap R K))) := inferInstance
  exact mono_comp' inferInstance this

theorem genIso_of_prod : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  intro R K _ _ _ _ _ hSH A A' B B' _ _ M M' N N' f Θ _ _ _ _ hΘ ⟨z, hz, U, g, hzU, ⟨hg₁, hg₂⟩, hgo⟩
  have := hSH.2.2.2
  have := M.smooth; have := M'.smooth; have := N.smooth; have := N'.smooth
  have := M.sep; have := M'.sep
  have := mono_j M; have := mono_j M'
  have : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  let π : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let π' : (M'.prod N').Y.left ⟶ M'.Y.left := (fst M'.Y N'.Y).left
  have : Smooth π := inferInstanceAs (Smooth (pullback.fst M.Y.hom N.Y.hom))
  have : Smooth π' := inferInstanceAs (Smooth (pullback.fst M'.Y.hom N'.Y.hom))
  have hπ : π ≫ M.Y.hom = (M.prod N).Y.hom := Over.w (fst M.Y N.Y)
  have hπ' : π' ≫ M'.Y.hom = (M'.prod N').Y.hom := Over.w (fst M'.Y N'.Y)
  have hj : (M.prod N).j ≫ π = (fst A B).left ≫ M.j := prod_j_fst M N
  have hj' : (M'.prod N').j ≫ π' = (fst A' B').left ≫ M'.j := prod_j_fst M' N'
  have hs : (U.ι ≫ π) ≫ M.Y.hom = (g ≫ π') ≫ M'.Y.hom := by
    rw [Category.assoc, Category.assoc, hπ, hπ', hg₁]
  have H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U.toScheme) (t : Z ⟶ Sp K),
      a ≫ (U.ι ≫ π) ≫ M.Y.hom = t ≫ spMap (algebraMap R K) →
      ∃ c : Z ⟶ A.left, c ≫ M.j = a ≫ U.ι ≫ π ∧ c ≫ f.hom.left ≫ M'.j = a ≫ g ≫ π' := by
    intro Z a t h
    obtain ⟨d, hd⟩ := exists_lift_j (M.prod N) (a ≫ U.ι) t (by rw [← h, ← hπ]; simp only [Category.assoc])
    obtain ⟨d', h₁, h₂⟩ := (isPullback_morphismRestrict (M.prod N).j U).exists_lift a d hd.symm
    refine ⟨d ≫ (fst A B).left, ?_, ?_⟩
    · rw [Category.assoc, ← hj, ← Category.assoc, hd, Category.assoc]
    · have e : Θ.left ≫ (fst A' B').left = (fst A B).left ≫ f.hom.left := by
        rw [← Over.comp_left, hΘ, Over.comp_left]
      rw [← h₁, ← h₂]
      simp only [Category.assoc]
      rw [reassoc_of% hg₂, hj', reassoc_of% e]
  obtain ⟨V, p', h, hp, _, _, hq, hh⟩ := exists_openImmersion (U.ι ≫ π) (g ≫ π') (fun Z a b =>
    ⟨eq_of_generic (spMap (algebraMap R K)) M.Y.hom M'.Y.hom _ _ hs M.j (f.hom.left ≫ M'.j) H a b,
     eq_of_generic (spMap (algebraMap R K)) M'.Y.hom M.Y.hom _ _ hs.symm (f.hom.left ≫ M'.j) M.j
      (fun Z a t h => (H Z a t (by rw [hs, h])).imp fun _ h => h.symm) a b⟩)
  have : Epi p' := Flat.epi_of_flat_of_surjective _
  refine ⟨π z, ?_, V, h, ?_, ⟨?_, ?_⟩, hh⟩
  · show M.Y.hom (π z) = _
    rw [← Scheme.Hom.comp_apply, hπ]; exact hz
  · have : V.ι (p' ⟨z, hzU⟩) = π z := congrArg (fun q : U.toScheme ⟶ M.Y.left => q ⟨z, hzU⟩) hp
    rw [← this]; exact (p' ⟨z, hzU⟩).2
  · rw [← cancel_epi p', reassoc_of% hq, reassoc_of% hp]
    simpa only [Category.assoc] using hs.symm
  · have : Epi (pullback.snd p' (M.j ∣_ V)) := Flat.epi_of_flat_of_surjective _
    have e : pullback.fst p' (M.j ∣_ V) ≫ U.ι ≫ π = (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι) ≫ M.j := by
      rw [← hp, pullback.condition_assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨c, hc₁, hc₂⟩ := H _ (pullback.fst p' (M.j ∣_ V)) (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι ≫ A.hom)
      (by rw [← Category.assoc, e, Category.assoc, M.j_hom]; simp only [Category.assoc])
    rw [e, cancel_mono] at hc₁
    rw [← cancel_epi (pullback.snd p' (M.j ∣_ V)), ← pullback.condition_assoc, hq, ← hc₂, hc₁, Category.assoc]

end GlobalTheory.SS.GenProj
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_isomorphism_product_models : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  first | exact @GlobalTheory.SS.GenProj.genIso_of_prod | exact GlobalTheory.SS.GenProj.genIso_of_prod | (intros; apply GlobalTheory.SS.GenProj.genIso_of_prod <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.SS.InvFrame

theorem exists_det_ne_zero {F S : Type} [Field F] {n : ℕ} (D : Fin n → S → F) (h : LinearIndependent F D) :
    ∃ t : Fin n → S, (Matrix.of fun i j => D i (t j)).det ≠ 0 := by
  have hs := span_flip_eq_top_iff_linearIndependent.2 h
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flip D))
  have e : Module.finrank F (Submodule.span F (Set.range (flip D))) = n := by
    rw [hs, finrank_top, Module.finrank_fin_fun]
  choose t ht using hf
  refine ⟨fun j => t (j.cast e.symm), ?_⟩
  have h2 := hli.comp (Fin.cast e.symm) (Fin.cast_injective _)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)).ne_zero
  have e2 : (Matrix.of fun i j : Fin n => D i (t (j.cast e.symm))).col = f ∘ Fin.cast e.symm :=
    funext fun j => ht _
  rw [e2]
  exact h2

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis constFn)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.KS GlobalTheory.KS.InvField

theorem value_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{0}}
    (φ : Γ(X, U) ⟶ T) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso T).hom.hom (pbT (Spec.map φ ≫ hU.fromSpec) f ⊤) = φ.hom f := by
  have ht : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  rw [pbT_of_le _ ht']
  have h1 : hU.fromSpec.appLE U ⊤ ht = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso T).hom = φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, h1, Category.assoc, Iso.inv_comp_eq,
      ← Scheme.ΓSpecIso_naturality]
    congr 1
  exact congrArg (fun q => q.hom f) h2

theorem value_constFn_id {T : Type} [CommRing T] (a : T) :
    (Scheme.ΓSpecIso (.of T)).hom.hom (constFn (𝟙 (Sp T)) ⊤ a) = a := by
  have h : (𝟙 (Sp T) : Sp T ⟶ Sp T).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 (Sp T)) (U := ⊤)).trans rfl
  rw [constFn, h]
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (.of T)).inv_hom_id

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))} [GrpObj G] [IsCommMonObj G]

theorem exists_independent [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {S F : Type} [CommRing S] [Algebra K S] [Field F] [Algebra K F] (j : sp (R₀ := K) S ⟶ G)
    [IsOpenImmersion j.left] (u : S →ₐ[K] F) :
    ∃ D : Fin n → S → F, LinearIndependent F D ∧ ∀ k, ∃ φ : S →ₐ[K] DualNumber F,
      spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v k) *
        (spMap ((inlS K F).comp u) ≫ j) ∧ ∀ a, (φ a).snd = D k a := by
  obtain ⟨χ, hχ, hfst⟩ := exists_chart_pt_of_nil j (TrivSqZeroExt.fstHom K F (Fin n → F))
    (fun a => ⟨inl a, rfl⟩) (fun a ha => ⟨2, by
      rw [pow_two]; exact mul_eq_zero_of_sq (ker_fst_sq (R := K) (S := F) (Fin n → F)) ha ha⟩)
    (lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) *
      (spMap ((TrivSqZeroExt.inlAlgHom K F (Fin n → F)).comp u) ≫ j)) u (by
      rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), one_mul, ← Category.assoc,
        spMap_comp]
      rfl)
  have hfst : ∀ a, (χ a).fst = u a := AlgHom.congr_fun hfst
  let φ : (Fin n → F) → (S →ₐ[K] DualNumber F) := fun c => (vecTo (inlS K F) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = tanExp v c * (spMap ((inlS K F).comp u) ≫ j) := fun c => by
    rw [← spMap_comp, Category.assoc, ← hχ, MonObj.comp_mul, comp_lieExp, ← Category.assoc, spMap_comp]
    congr 1
    · exact lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _
    · congr 2
      exact AlgHom.ext fun a => by simp [vecTo_apply]
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, c k * (χ a).snd k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  refine ⟨fun k a => (χ a).snd k, Fintype.linearIndependent_iff.2 fun c hc k => ?_,
    fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using congrFun hc a)
    have h3 := mul_right_cancel ((hφ c).symm.trans (this ▸ hφ 0))
    have h4 := (expBij (DualNumber F) hv _ (ker_fst_sq (R := K) (S := F) F)).1 _ _ (fun _ => rfl) (fun _ => rfl) _ _ h3
    exact TrivSqZeroExt.inr_injective (congrFun h4 k)
  · rw [hφ]
    congr 1
    refine (Finset.prod_eq_single k (fun i _ hi => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
      (by simp [Pi.single_eq_of_ne hi]) _) (by simp)).trans ?_
    congr 3
    simp
  · rw [hφ2]
    simp [Pi.single_apply]

omit [IsCommMonObj G] in

theorem value_invDer {v : epsR K ⟶ G} {dd : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(G.left, W)} (hd : IsInvDer v dd)
    {U : G.left.Opens} (hU : IsAffineOpen U) [Algebra K Γ(G.left, U)] (j : sp (R₀ := K) Γ(G.left, U) ⟶ G)
    (hj : j.left = hU.fromSpec) {F : Type} [Field F] [Algebra K F] (u : Γ(G.left, U) →ₐ[K] F)
    (φ : Γ(G.left, U) →ₐ[K] DualNumber F)
    (hφ : spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v) *
        (spMap ((inlS K F).comp u) ≫ j)) (f : Γ(G.left, U)) : (φ f).snd = u (dd U f) := by
  let w : sp (R₀ := K) (DualNumber F) ⟶ epsR K ⊗ G :=
    lift (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))) (spMap ((inlS K F).comp u) ≫ j)
  have e1 : w.left ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, ← hφ, Over.comp_left, hj]
    rfl
  have e2 : w.left ≫ (snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom ((inlS K F).comp u).toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, hj]
    rfl
  have e3 : w.left ≫ (fst (epsR K) G).left = 𝟙 _ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
      (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)).toRingHom := by
    rw [← Over.comp_left, lift_fst, Category.id_comp]
    rfl
  have hw : ⊤ ≤ w.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, e2]
    exact fun q _ => hU.fromSpec_preimage_self.ge (x := Spec.map _ q) trivial
  have key : ∀ f : Γ(G.left, U), ((Scheme.ΓSpecIso (.of (DualNumber F))).hom.hom (pbT w.left
      (pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ U)) ⊤) : DualNumber F) =
      inl (u f) + inr 1 * inl (u (dd U f)) := fun f => by
    rw [hd U f, pbT_add, pbT_mul, pbT_pbT _ _ le_rfl hw, pbT_pbT _ _ le_rfl hw, pbT_constFn _ _ hw, e2, e3,
      constFn_spMap, map_add, map_mul]
    refine congrArg₂ _ (value_fromSpec hU _ _) (congrArg₂ _ ?_ (value_fromSpec hU _ _))
    refine Eq.trans ?_ (epsTo_eps (R := K) (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))
    exact value_constFn_id _
  by_cases h : (snd (epsR K) G).left ⁻¹ᵁ U ≤ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ U
  · have := key f
    rw [pbT_pbT _ _ h hw, e1] at this
    have h5 := congrArg TrivSqZeroExt.snd ((value_fromSpec hU _ f).symm.trans this)
    simpa using h5
  · have := key 1
    rw [show pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left (1 : Γ(G.left, U))
      ((snd (epsR K) G).left ⁻¹ᵁ U) = 0 from dif_neg h, pbT_zero, map_zero] at this
    simpa using congrArg TrivSqZeroExt.fst this

theorem exists_mem_basicOpen [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (D : Fin n → VF G) (hd : ∀ i, IsInvDer (v i) fun W f => (D i).D W f) (x : G.left) :
    ∃ (U : G.left.Opens) (t : Fin n → Γ(G.left, U)), x ∈ G.left.basicOpen (jac D U t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  letI : Algebra K Γ(G.left, U) := (Spec.preimage (hU.fromSpec ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) Γ(G.left, U) ⟶ G := Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
  have := PrimeSpectrum.isPrime p
  let u : Γ(G.left, U) →ₐ[K] (PrimeSpectrum.asIdeal p).ResidueField := IsScalarTower.toAlgHom _ _ _
  obtain ⟨δ, hδ, hφ⟩ := exists_independent hv j u
  obtain ⟨t, ht⟩ := exists_det_ne_zero δ hδ
  refine ⟨U, t, ?_⟩
  have h1 : u (jac D U t) ≠ 0 := by
    rw [jac, AlgHom.map_det]
    refine (congrArg Matrix.det (Matrix.ext fun i k => ?_)).trans_ne ht
    obtain ⟨φ, h2, h3⟩ := hφ i
    exact (value_invDer (hd i) hU j rfl u φ h2 (t k)).symm.trans (h3 _)
  have h2 : p ∈ hU.fromSpec ⁻¹ᵁ G.left.basicOpen (jac D U t) := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact fun h => h1 (Ideal.algebraMap_residueField_eq_zero.2 h)
  exact h2

end GlobalTheory.SS.InvFrame

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.SS.exists_isFrame : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  intro K _ A _ _ g hg
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  choose dd hdd using fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).1
  have hp := fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).2 _ (hdd i)
  let D : Fin g → VF A := fun i =>
    { D := fun U => AddMonoidHom.mk' (dd i U) ((hp i).1 U)
      leibniz := (hp i).2.1
      const := (hp i).2.2.2.1
      res := fun U V h a => by
        have := (hp i).2.2.1 U V a h
        rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h] at this
        exact this }
  refine ⟨D, by rwa [Fintype.card_fin], fun x => ?_⟩
  obtain ⟨U, t, hx⟩ := InvFrame.exists_mem_basicOpen hv D hdd x
  have hle := A.left.basicOpen_le (jac D U t)
  refine ⟨_, fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i), hx, ?_⟩
  have e : jac D _ (fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i)) =
      (A.left.presheaf.map (homOfLE hle).op).hom (jac D U t) := by
    exact (congrArg Matrix.det (Matrix.ext fun i k => (D i).res U _ hle (t k))).trans
      (RingHom.map_det (A.left.presheaf.map (homOfLE hle).op).hom (Matrix.of fun i k => (D i).D U (t k))).symm
  rw [e]
  exact A.left.toRingedSpace.isUnit_res_basicOpen (jac D U t)

end

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  atlas_forward_decl GlobalTheory.SS.exists_isFrame
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_modelHasJacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ M : Model R A, M.Irr → ∃! n : ℤ, HasOrd M D π n := by
  first | exact @GlobalTheory.SS.Ord.existsUnique_hasOrd | exact GlobalTheory.SS.Ord.existsUnique_hasOrd | (intros; apply GlobalTheory.SS.Ord.existsUnique_hasOrd <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.Ord

theorem model_smoothOfRelativeDimension {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {A : Over (Sp K)} {d : ℕ} (hA : SmoothOfRelativeDimension d A.hom) (M : Model R A) :
    SmoothOfRelativeDimension d M.Y.hom := by
  have := M.smooth
  choose n W hW hd using H1.exists_dim M.Y.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  have hne : ∃ y : A.left, M.j y ∈ W x := by
    by_contra hc
    have e : M.j ⁻¹ᵁ W x = ⊥ := le_bot_iff.1 fun y hy => (hc ⟨y, hy⟩).elim
    have h1 : Subsingleton Γ(A.left, M.j ⁻¹ᵁ W x) := by rw [e]; infer_instance
    have h2 : Subsingleton Γ(M.Y.left, W x) := (j_app_injective M (W x)).subsingleton
    have : Nonempty (W x) := ⟨⟨x, hW x⟩⟩
    exact not_subsingleton _ h2
  obtain ⟨y, hy⟩ := hne
  rw [← H1.dim_base (isPullback_j M) (hd x) hA y hy]
  exact hd x

theorem exists_etale_coord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (I : Type) [Fintype I], SmoothOfRelativeDimension (Fintype.card I) A.hom → ∀ (M : Model R A) (x : M.Y.left) (O : M.Y.left.Opens), x ∈ O → ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), IsAffineOpen U ∧ x ∈ U ∧ U ≤ O ∧ (MvPolynomial.eval₂Hom (cst M U) t).Etale := by
  intro R K _ _ _ _ _ _ A I _ hA M x O hx
  have hM := model_smoothOfRelativeDimension hA M
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (Fintype.card I)) M.Y.hom hM
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(M.Y.left, M.Y.left.basicOpen g)
  have h2 : (cst M (M.Y.left.basicOpen g)).IsStandardSmoothOfRelativeDimension (Fintype.card I) := by
    have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
    have e : cst M (M.Y.left.basicOpen g) = (rs _ (M.Y.left.basicOpen_le g)).comp (cst M W) :=
      RingHom.ext fun r => (rs_cst M (M.Y.left.basicOpen_le g) r).symm
    rw [e]
    exact h3
  obtain ⟨φ, hC, hφ⟩ := h2.exists_etale_mvPolynomial
  let e := Fintype.equivFin I
  refine ⟨M.Y.left.basicOpen g, fun i => φ (MvPolynomial.X (e i)), hW.basicOpen g, hxg,
    (M.Y.left.basicOpen_le g).trans hWO, ?_⟩
  have h4 := RingHom.Etale.respectsIso.2 φ (MvPolynomial.renameEquiv R e).toRingEquiv hφ
  convert h4 using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [← hC]
  · simp

end GlobalTheory.SS.Ord
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord

namespace GlobalTheory.SS.Ord

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma model_isPullback_genericFibre_spMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] in

theorem _root_.GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M N : _root_.GlobalTheory.SS.Model R A)
      (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left),
      _root_.GlobalTheory.SS.Extends M N (𝟙 A) U g → Etale g → IsOpenImmersion g := by
  intro R K _ _ _ _ _ _ A M N U g hE _
  haveI := M.smooth
  haveI := M.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI : IsSeparated (g ≫ N.Y.hom) := by rw [hE.1]; infer_instance
  haveI : IsSeparated g := IsSeparated.of_comp g N.Y.hom
  haveI := FormallyUnramified.isOpenImmersion_diagonal g
  let ψ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)
  let q := pullback.fst g g ≫ U.ι ≫ M.Y.hom
  let φ := pullback.fst q ψ
  haveI : IsSchemeTheoreticallyDominant φ :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback q ψ).flip
  have hU := ((isPullback_morphismRestrict M.j U).paste_vert
    (model_isPullback_genericFibre_spMap M))
  have hN := model_isPullback_genericFibre_spMap N
  have hs : (φ ≫ pullback.fst g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [Category.assoc]
    exact pullback.condition
  have hs' : (φ ≫ pullback.snd g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [← hs, ← hE.1]
    simp only [Category.assoc, pullback.condition_assoc]
  have key : ∀ (c : pullback q ψ ⟶ U) (hc : c ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ),
      (hU.lift c _ hc ≫ (M.j ⁻¹ᵁ U).ι) ≫ N.j = c ≫ g := by
    intro c hc
    have h2 := hE.2
    conv_rhs => rw [← hU.lift_fst c _ hc]
    rw [Category.assoc (hU.lift c _ hc) (M.j ∣_ U) g, h2]
    simp
  have hl : hU.lift _ _ hs ≫ (M.j ⁻¹ᵁ U).ι =
      hU.lift _ _ hs' ≫ (M.j ⁻¹ᵁ U).ι := by
    apply hN.hom_ext
    · rw [key _ hs, key _ hs']
      simp only [Category.assoc, pullback.condition]
    · have e1 := hU.lift_snd _ _ hs
      have e2 := hU.lift_snd _ _ hs'
      simp only [Category.assoc] at e1 e2 ⊢
      rw [e1, e2]
  have hab : φ ≫ pullback.fst g g = φ ≫ pullback.snd g g := by
    rw [← hU.lift_fst _ _ hs, ← hU.lift_fst _ _ hs', (cancel_mono _).1 hl]
  have hφ : φ = (φ ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [hab]
  have hrange : Set.range φ ⊆ Set.range (pullback.diagonal g) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(φ ≫ pullback.fst g g) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) :=
    (pullback.diagonal g).isClosedEmbedding.isClosed_range
  have huniv : Set.range (pullback.diagonal g) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (IsDominant.denseRange (f := φ)).closure_eq]
    exact closure_minimal hrange hclosed
  haveI : IsIso (pullback.diagonal g) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using huniv))
  haveI : Mono g := (pullback.isIso_diagonal_iff g).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono g

end GlobalTheory.SS.Ord
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.OrdMono

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
  {I : Type} [Fintype I] [DecidableEq I]

abbrev IsCoord (M : Model R A) {I : Type} (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cst M U) t).Etale

abbrev jm (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : Γ(A.left, M.j ⁻¹ᵁ U) :=
  jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i))

theorem etale_comp {B C I : Type} [CommRing B] [CommRing C] (c : R →+* B) (t : I → B) (φ : B →+* C)
    (h : (MvPolynomial.eval₂Hom c t).Etale) (hφ : φ.Etale) :
    (MvPolynomial.eval₂Hom (φ.comp c) (fun i => φ (t i))).Etale := by
  rw [← MvPolynomial.comp_eval₂Hom]
  exact RingHom.Etale.stableUnderComposition _ _ h hφ

theorem chain_model (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t t' : I → Γ(M.Y.left, U))
    (h : IsCoord M U t) : ∃ a, jm M D U t' = (M.j.app U).hom a * jm M D U t ∧ (IsUnit a → IsCoord M U t') := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion R _ (cst M U) I t t' h
  refine ⟨a, h1 _ (M.j.app U).hom (fun i => ((D i).D _).comp (M.j.app U).hom.toAddMonoidHom)
    (fun i x y => ?_) (fun i r => ?_), h2⟩
  · show (D i).D _ ((M.j.app U).hom (x * y)) = _
    rw [map_mul, (D i).leibniz]; rfl
  · show (D i).D _ ((M.j.app U).hom (cst M U r)) = _
    rw [j_cst, (D i).const]

theorem etale_rs (X : Scheme.{0}) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (rs X h).Etale := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  simpa [Scheme.Hom.appLE] using this

theorem coord_rs (M : Model R A) {I : Type} {U V : M.Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) : IsCoord M V fun i => rs _ h (t i) := by
  have := etale_comp _ t _ ht (etale_rs _ hU hV h)
  have e : (rs _ h).comp (cst M U) = cst M V := RingHom.ext (rs_cst M h)
  rwa [e] at this

theorem rs_jm (M : Model R A) (D : I → VF A) {U V : M.Y.left.Opens} (h : V ≤ U) (t : I → Γ(M.Y.left, U)) :
    rs _ (M.j.preimage_mono h) (jm M D U t) = jm M D V fun i => rs _ h (t i) := by
  rw [jm, rs_jac]; exact congrArg (jac D _) (funext fun i => rs_j M h (t i))

theorem isUnit_of_local (X : Scheme.{0}) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ IsUnit (rs X hV f)) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨V, hV, hxV, hu⟩ := h x hx
  have := hu.map (X.presheaf.germ V x hxV).hom
  exact (X.presheaf.germ_res_apply (homOfLE hV) x hxV f).subst this

theorem isUnit_of_dvd_pow {B : Type} [CommRing B] {p s : B} (hp : Prime p) (h0 : p ∈ nonZeroDivisors B)
    (hs : ¬ p ∣ s) (k : ℕ) (h : s ∣ p ^ k) : IsUnit s := by
  induction k with
  | zero => exact isUnit_of_dvd_one (by simpa using h)
  | succ k ih =>
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', rfl⟩ : p ∣ b := (hp.dvd_or_dvd (hb ▸ dvd_pow_self p k.succ_ne_zero)).resolve_left hs
    refine ih ⟨b', ?_⟩
    have : p * (p ^ k - s * b') = 0 := by linear_combination hb
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_left.1 h0) _ this)
end

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]

theorem isUnit_jm (M : Model R A) {D : I → VF A} (hD : IsFrame D) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) : IsUnit (jm M D U t) := by
  have := isOpenImmersion_j M
  refine isUnit_of_local _ _ _ fun z hz => ?_
  obtain ⟨U', t', hz', hu⟩ := hD.2 z
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := A.left) (U := U' ⊓ M.j ⁻¹ᵁ U) ⟨hz', hz⟩
  have h1 : V ≤ U' := fun _ h => (hle h).1
  have h2 : V ≤ M.j ⁻¹ᵁ U := fun _ h => (hle h).2
  refine ⟨V, h2, hzV, ?_⟩
  have he := etale_comp _ t _ ht (M.j.etale_appLE hU hV h2)
  obtain ⟨a, ha, -⟩ := GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion R _ _ I _ (fun i => rs _ h1 (t' i)) he
  have hb := ha _ (RingHom.id _) (fun i => (D i).D V) (fun i => (D i).leibniz V) (fun i r => by
    have : ((M.j.appLE U V h2).hom.comp (cst M U)) r = cstK A V (algebraMap R K r) := by
      rw [← rs_cstK h2, ← j_cst]; rfl
    rw [this, (D i).const])
  have hc : IsUnit (jac D V fun i => rs _ h1 (t' i)) := by rw [← rs_jac]; exact hu.map _
  rw [jm, rs_jac]
  exact isUnit_of_mul_isUnit_right (show IsUnit (_ * _) from hb.subst hc)

theorem isUnit_cstK (hπ : Irreducible π) (U : A.left.Opens) (n : ℤ) : IsUnit (cstK A U (algebraMap R K π ^ n)) :=
  (IsUnit.mk0 _ (zpow_ne_zero n (by simpa using hπ.ne_zero))).map _

theorem chart (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {D : I → VF A} (hD : IsFrame D) {n : ℤ}
    (hn : HasOrd M D π n) {U : M.Y.left.Opens} (hU : IsAffineOpen U) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) :
    ∃ s : Γ(M.Y.left, U), IsUnit s ∧ jm M D U t = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by
  obtain ⟨s, hs⟩ := hn.1 U t
  refine ⟨s, ?_, hs⟩
  obtain ⟨U₀, t₀, s₀, h₀, hu₀, hs₀⟩ := hn.2
  have hjs : IsUnit ((M.j.app U).hom s) := isUnit_of_mul_isUnit_right (show IsUnit (_ * _) from hs.subst (isUnit_jm M hD hU ht))
  obtain ⟨z, hz, hzU, hzU₀⟩ := hM.2 U U₀ U.isOpen U₀.isOpen (Set.inter_comm _ _ ▸ h) (Set.inter_comm _ _ ▸ h₀)
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := M.Y.left) (U := U ⊓ U₀) ⟨hzU, hzU₀⟩
  have h1 : V ≤ U := fun _ h => (hle h).1
  have h2 : V ≤ U₀ := fun _ h => (hle h).2
  obtain ⟨a, ha, -⟩ := chain_model M D V _ (fun i => rs _ h2 (t₀ i)) (coord_rs M hU hV h1 ht)
  rw [← rs_jm M D h1, ← rs_jm M D h2, jm, jm, hs, hs₀, map_mul, map_mul, rs_cstK, rs_cstK, rs_j M h1, rs_j M h2, mul_left_comm,
    ← map_mul] at ha
  have hb := j_app_injective M V ((isUnit_cstK hπ _ n).mul_left_cancel ha)
  have hc : IsUnit (rs _ h1 s) := isUnit_of_mul_isUnit_right (hb ▸ hu₀.map (rs _ h2))
  obtain ⟨f, hf⟩ := hjs.exists_right_inv
  obtain ⟨k, b, hk⟩ := exists_pow_mul_eq hπ M hU f
  refine isUnit_of_dvd_pow (prime_cst hπ M hM hU h) (cst_mem_nonZeroDivisors hπ M U) ?_ k ⟨b, ?_⟩
  · intro hd
    have := map_dvd (rs _ h1) hd
    rw [rs_cst] at this
    exact not_isUnit_cst M V ⟨z, hzV, hz⟩ hπ.not_isUnit (isUnit_of_dvd_unit this hc)
  · apply j_app_injective M U
    rw [map_mul, hk, mul_left_comm, hf, _root_.mul_one, map_pow]

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

def th {X : Scheme.{0}} (W : X.Opens) : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) := W.ι.appLE W ⊤ (by simp)

instance {X : Scheme.{0}} (W : X.Opens) : IsIso (th W) := by
  have : th W = W.topIso.inv := by simp [th, Scheme.Opens.topIso, Scheme.Opens.ι_appLE]; rfl
  rw [this]; infer_instance

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst e; rfl

theorem extends_res {M N : Model R A} {U W : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N (𝟙 A) U g) (hW : W ≤ U) : Extends M N (𝟙 A) W (M.Y.left.homOfLE hW ≫ g) := by
  refine ⟨by rw [Category.assoc, h.1, Scheme.homOfLE_ι_assoc], ?_⟩
  have : M.j ∣_ W ≫ M.Y.left.homOfLE hW = A.left.homOfLE (M.j.preimage_mono hW) ≫ M.j ∣_ U := by
    rw [← cancel_mono U.ι]; simp
  rw [← Category.assoc, this, Category.assoc, h.2, Scheme.homOfLE_ι_assoc]

theorem exists_pull {M N : Model R A} {W : M.Y.left.Opens} {g : W.toScheme ⟶ N.Y.left}
    (h : Extends M N (𝟙 A) W g) (V : N.Y.left.Opens) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ∃ (ψ : Γ(N.Y.left, V) →+* Γ(M.Y.left, W)) (hle : M.j ⁻¹ᵁ W ≤ N.j ⁻¹ᵁ V), ψ.comp (cst N V) = cst M W ∧
      (∀ u, (M.j.app W).hom (ψ u) = rs _ hle ((N.j.app V).hom u)) ∧
      (IsAffineOpen W → IsAffineOpen V → ψ.Etale → Etale g) := by
  have h2 : M.j ∣_ W ≫ g = (M.j ⁻¹ᵁ W).ι ≫ N.j := by simpa using h.2
  have hle : M.j ⁻¹ᵁ W ≤ N.j ⁻¹ᵁ V := fun x hx => by
    have : ((M.j ⁻¹ᵁ W).ι ≫ N.j) ⟨x, hx⟩ ∈ V := by
      rw [← h2]; exact hV (x := (M.j ∣_ W) ⟨x, hx⟩) trivial
    exact this
  refine ⟨(g.appLE V ⊤ hV ≫ inv (th W)).hom, hle, ?_, ?_, ?_⟩
  · have : N.Y.hom.appLE ⊤ V le_top ≫ g.appLE V ⊤ hV ≫ inv (th W) = M.Y.hom.appLE ⊤ W le_top := by
      rw [← Category.assoc, IsIso.comp_inv_eq, th, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr h.1 _ _ _ _
    ext r
    exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) this
  · have a : M.j.app W ≫ th (M.j ⁻¹ᵁ W) = th W ≫ (M.j ∣_ W).appLE ⊤ ⊤ le_top := by
      rw [th, th, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr (morphismRestrict_ι _ _).symm _ _ _ _
    have : (g.appLE V ⊤ hV ≫ inv (th W)) ≫ M.j.app W = N.j.appLE V _ hle := by
      rw [← cancel_mono (th (M.j ⁻¹ᵁ W)), Category.assoc, a, Category.assoc, IsIso.inv_hom_id_assoc, th,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr h2 _ _ _ _
    intro u
    exact congrArg (fun q => q.hom u) this
  · intro hW hV' he
    have : IsAffine W.toScheme := hW
    have he' : (g.appLE V ⊤ hV).hom.Etale := (RingHom.Etale.respectsIso.cancel_right_isIso _ _).1 he
    have h3 : Etale (g.resLE V ⊤ hV) := by
      have : IsAffine V.toScheme := hV'
      have : IsAffine (⊤ : W.toScheme.Opens).toScheme := isAffineOpen_top _
      rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
      exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso g V ⊤ hV)).2 he'
    have h4 : Etale ((⊤ : W.toScheme.Opens).ι ≫ g) := by
      rw [← Scheme.Hom.resLE_comp_ι g hV]; infer_instance
    have h5 : g = W.toScheme.topIso.inv ≫ (⊤ : W.toScheme.Opens).ι ≫ g := by simp
    rw [h5]; infer_instance
end

theorem ord_mono : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [IsIntegral A.left] (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ (M N : Model R A) (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D π n → (∃ y ∈ M.sp, DefAt M N (𝟙 A) y) → m ≤ n ∧ (m = n → GenIso M N (𝟙 A)) := by
  intro R K _ _ _ _ _ _ π hπ A _ I _ _ D hD M N m n hM hN hm hn ⟨y, hy, U, g, hyU, hg⟩
  have hx : g ⟨y, hyU⟩ ∈ N.sp := by
    have : (g ≫ N.Y.hom) ⟨y, hyU⟩ = (U.ι ≫ M.Y.hom) ⟨y, hyU⟩ := by rw [hg.1]
    exact this.trans hy
  obtain ⟨V, t, hV, hxV, -, ht⟩ := GlobalTheory.SS.Ord.exists_etale_coord R K A I hD.1 N (g ⟨y, hyU⟩) ⊤ trivial
  obtain ⟨s, hs, e⟩ := chart hπ N hN hD hn hV ⟨_, hxV, hx⟩ ht
  obtain ⟨W, r, hW, hyW, hle, hr⟩ := GlobalTheory.SS.Ord.exists_etale_coord R K A I hD.1 M y (U.ι ''ᵁ g ⁻¹ᵁ V) ⟨⟨y, hyU⟩, hxV, rfl⟩
  have hWU : W ≤ U := hle.trans (U.ι_image_le _)
  have hg' := extends_res hg hWU
  have htop : ⊤ ≤ (M.Y.left.homOfLE hWU ≫ g) ⁻¹ᵁ V := by
    intro z _
    obtain ⟨w, hw, e⟩ := hle z.2
    have : M.Y.left.homOfLE hWU z = w := Subtype.ext (by rw [Scheme.homOfLE_apply]; exact e.symm)
    show g (M.Y.left.homOfLE hWU z) ∈ V
    rw [this]; exact hw
  obtain ⟨ψ, hj, hc, hψ, het⟩ := exists_pull hg' V htop
  have key : jm M D W (fun i => ψ (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app W).hom (ψ s) := by
    have := congrArg (rs _ hj) e
    rw [jm, rs_jac, map_mul, rs_cstK, ← hψ] at this
    simpa only [jm, hψ] using this
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  refine ⟨not_lt.1 fun hlt => ?_, ?_⟩
  · obtain ⟨s', e'⟩ := hm.1 W fun i => ψ (t i)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = n + (k + 1 : ℕ) := ⟨(m - n - 1).toNat, by omega⟩
    replace e' := key.symm.trans e'
    rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cst, ← map_mul] at e'
    have h1 := j_app_injective M W ((isUnit_cstK hπ _ n).mul_left_cancel e')
    have h2 := hs.map ψ
    rw [h1, pow_succ, map_mul] at h2
    exact not_isUnit_cst M W ⟨y, hyW, hy⟩ hπ.not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h2))
  · rintro rfl
    obtain ⟨s', e'⟩ := hm.1 W r
    obtain ⟨a, ha, hb⟩ := chain_model M D W r (fun i => ψ (t i)) hr
    rw [key, jm, e', mul_left_comm, ← map_mul] at ha
    have h1 := j_app_injective M W ((isUnit_cstK hπ _ m).mul_left_cancel ha)
    have h2 := hb (isUnit_of_mul_isUnit_left (show IsUnit (_ * _) from h1.subst (hs.map ψ)))
    have h3 : (ψ.comp (MvPolynomial.eval₂Hom (cst N V) t)).Etale := by
      rw [MvPolynomial.comp_eval₂Hom, hc]; exact h2
    have h4 : ψ.Etale := by
      algebraize [MvPolynomial.eval₂Hom (cst N V) t, ψ, ψ.comp (MvPolynomial.eval₂Hom (cst N V) t)]
      exact Algebra.Etale.of_restrictScalars (R := MvPolynomial I R) _ _
    exact ⟨y, hy, W, _, hyW, hg', GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale R K A M N W _ hg' (het hW hV h4)⟩

end GlobalTheory.SS.OrdMono
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_order_monotone_semistableModel : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [IsIntegral A.left] (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ (M N : Model R A) (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D π n → (∃ y ∈ M.sp, DefAt M N (𝟙 A) y) → m ≤ n ∧ (m = n → GenIso M N (𝟙 A)) := by
  atlas_forward_decl GlobalTheory.SS.OrdMono.ord_mono
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.OrdTwist

theorem det_cross {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Type} [Fintype I] [DecidableEq I]
    (b : Module.Basis I B Ω[B⁄K]) (D D' : I → Derivation K B B) (t u : I → B) :
    (Matrix.of fun i j => D' i (t j)).det * (Matrix.of fun i j => D i (u j)).det =
      (Matrix.of fun i j => D' i (u j)).det * (Matrix.of fun i j => D i (t j)).det := by
  have key : ∀ (E : I → Derivation K B B) (v : I → B), (Matrix.of fun i j => E i (v j)).det =
      (Matrix.of fun i k => (E i).liftKaehlerDifferential (b k)).det *
        (Matrix.of fun k j => b.repr (KaehlerDifferential.D K B (v j)) k).det := by
    intro E v
    rw [← Matrix.det_mul]
    congr 1
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← Derivation.liftKaehlerDifferential_comp_D (E i) (v j)]
    conv_lhs => rw [← b.sum_repr (KaehlerDifferential.D K B (v j))]
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.of_apply, mul_comm]
  rw [key D' t, key D u, key D' u, key D t]
  ring

variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]

abbrev rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    rs h' (rs h a) = rs (h'.trans h) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem rs_jac (D : I → VF A) {U V : A.left.Opens} (h : V ≤ U) (t : I → Γ(A.left, U)) :
    rs h (jac D U t) = jac D V (fun i => rs h (t i)) := by
  unfold jac
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact ((D i).res U V h (t j)).symm

theorem rs_cstK {U V : A.left.Opens} (h : V ≤ U) (c : K) : rs h (cstK A U c) = cstK A V c := by
  exact congr($(Scheme.Hom.appLE_map A.hom (U := ⊤) (V := U) le_top (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))

theorem eq_of_locally {X : Scheme.{0}} {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (e : V ≤ U), x ∈ V ∧ rs e a = rs e b) : a = b := by
  choose V e hx hV using h
  refine X.sheaf.eq_of_locally_eq' (fun x : U => V x.1 x.2) U (fun x => homOfLE (e x.1 x.2)) ?_ a b
    (fun x => hV x.1 x.2)
  intro x hxU
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩

theorem exists_std {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) (U : A.left.Opens) (x : A.left) (hx : x ∈ U) :
    ∃ V : A.left.Opens, V ≤ U ∧ x ∈ V ∧ (cstK A V).IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨W, -, V, hV, hxV, e, hf⟩ := hA.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : W = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = A.hom x := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact e hxV
  obtain ⟨g, hgU, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨A.left.basicOpen g, hgU, hxg, ?_⟩
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(A.left, V) Γ(A.left, A.left.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h2 : (cstK A V).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv hf
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (rs_cstK _ c).symm

def toDer (D : VF A) (V : A.left.Opens) :
    letI := (cstK A V).toAlgebra
    Derivation K Γ(A.left, V) Γ(A.left, V) :=
  letI := (cstK A V).toAlgebra
  Derivation.mk'
    { toFun := D.D V
      map_add' := map_add _
      map_smul' := fun c a => by
        show D.D V (cstK A V c * a) = cstK A V c * D.D V a
        rw [D.leibniz, D.const, mul_zero, add_zero] }
    (fun a b => D.leibniz V a b)

theorem jac_cross (hA : SmoothOfRelativeDimension (Fintype.card I) A.hom) (D D' : I → VF A)
    (U : A.left.Opens) (t u : I → Γ(A.left, U)) :
    jac D' U t * jac D U u = jac D' U u * jac D U t := by
  refine eq_of_locally _ _ fun x hx => ?_
  obtain ⟨V, e, hxV, hs⟩ := exists_std hA U x hx
  refine ⟨V, e, hxV, ?_⟩
  simp only [map_mul, rs_jac]
  letI := (cstK A V).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I) K Γ(A.left, V) := hs
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (Fintype.card I) (R := K) (S := Γ(A.left, V))
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Module.finrank Γ(A.left, V) Ω[Γ(A.left, V)⁄K] = Fintype.card I := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (Fintype.card I)]
    simp
  exact det_cross ((Module.finBasisOfFinrankEq _ _ this).reindex (Fintype.equivFin I).symm) (fun i => toDer (D i) V) (fun i => toDer (D' i) V) _ _

theorem exists_ratio (D D' : I → VF A) (hD : IsFrame D) :
    ∃ h : Γ(A.left, ⊤), ∀ (U : A.left.Opens) (t : I → Γ(A.left, U)), jac D' U t = rs le_top h * jac D U t := by
  obtain ⟨hA, hD⟩ := hD
  choose V u hx hu using hD
  have hu' : ∀ x, ∃ w, jac D (V x) (u x) * w = 1 := fun x => (hu x).exists_right_inv
  choose w hw using hu'
  have key : ∀ x (U : A.left.Opens) (e : U ≤ V x) (t : I → Γ(A.left, U)),
      jac D' U t = rs e (jac D' (V x) (u x) * w x) * jac D U t := by
    intro x U e t
    have h1 := congrArg (rs e) (hw x)
    have h2 := jac_cross hA D D' U t (fun i => rs e (u x i))
    simp only [map_mul, map_one, rs_jac] at h1 ⊢
    linear_combination (rs e (w x)) * h2 - jac D' U t * h1
  obtain ⟨h, hh, -⟩ := A.left.sheaf.existsUnique_gluing' V ⊤ (fun x => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) (fun x => jac D' (V x) (u x) * w x) (by
      intro x y
      show rs (inf_le_left : V x ⊓ V y ≤ V x) _ = rs (inf_le_right : V x ⊓ V y ≤ V y) _
      have h1 := key x (V x ⊓ V y) inf_le_left (fun i => rs inf_le_right (u y i))
      have h2 := congrArg (rs (inf_le_right : V x ⊓ V y ≤ V y)) (hw y)
      generalize rs (inf_le_left : V x ⊓ V y ≤ V x) (jac D' (V x) (u x) * w x) = z at h1 ⊢
      simp only [map_mul, map_one, rs_jac] at h2 ⊢
      rw [h1, _root_.mul_assoc, h2, _root_.mul_one])
  revert hh
  change Γ(A.left, ⊤) at h
  intro hh
  refine ⟨h, fun U t => eq_of_locally _ _ fun x hxU => ⟨U ⊓ V x, inf_le_left, ⟨hxU, hx x⟩, ?_⟩⟩
  have h3 : rs (le_top : V x ≤ ⊤) h = jac D' (V x) (u x) * w x := hh x
  rw [map_mul, rs_jac, rs_jac, key x _ inf_le_right, ← h3, rs_rs, rs_rs]

section Pull
variable {A' : Over (Sp K)} (g : A ⟶ A')

theorem app_rs {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    (g.app V).hom (rs h a) = rs (g.preimage_mono h) ((g.app U).hom a) :=
  congr($(g.naturality (homOfLE h).op) a)

theorem app_cstK (V : A'.left.Opens) (c : K) : (g.left.app V).hom (cstK A' V c) = cstK A _ c := by
  have h : A'.hom.appLE ⊤ V le_top ≫ g.left.app V = A.hom.appLE ⊤ (g.left ⁻¹ᵁ V) le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE g.left A'.hom ⊤ V _ le_top le_rfl).trans ?_
    simp only [Over.w g]
  exact congr($h ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))

variable [IsIso g.left]

def appE (V : A'.left.Opens) : Γ(A'.left, V) ≃+* Γ(A.left, g.left ⁻¹ᵁ V) :=
  (asIso (g.left.app V)).commRingCatIsoToRingEquiv


theorem app_symm (V : A'.left.Opens) (a : Γ(A.left, g.left ⁻¹ᵁ V)) :
    (g.left.app V).hom ((appE g V).symm a) = a := (appE g V).apply_symm_apply a

def transport (D : VF A) : VF A' where
  D V := (appE g V).symm.toAddMonoidHom.comp ((D.D _).comp (appE g V).toAddMonoidHom)
  leibniz V a b := by
    apply (appE g V).injective
    simp [D.leibniz]
  const V c := by
    show (appE g V).symm (D.D _ ((g.left.app V).hom (cstK A' V c))) = 0
    rw [app_cstK, D.const, map_zero]
  res U V h a := by
    apply (appE g V).injective
    show (g.left.app V).hom ((appE g V).symm (D.D _ ((g.left.app V).hom (rs h a)))) =
      (g.left.app V).hom (rs h ((appE g U).symm (D.D _ ((g.left.app U).hom a))))
    rw [app_symm, app_rs, app_rs, app_symm]
    exact D.res _ _ _ _

theorem app_jac (D : I → VF A) (V : A'.left.Opens) (t : I → Γ(A'.left, V)) :
    (g.left.app V).hom (jac (fun i => transport g (D i)) V t) =
      jac D _ (fun i => (g.left.app V).hom (t i)) := by
  unfold jac
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact app_symm g V _

end Pull

theorem exists_const [GrpObj A] (hA : IsAbelianScheme A) (D : I → VF A) (hD : IsFrame D) (f : A ≅ A) :
    ∃ c : K, c ≠ 0 ∧ ∀ (V : A.left.Opens) (t : I → Γ(A.left, V)),
      jac D _ (fun i => (f.inv.left.app V).hom (t i)) = cstK A _ c * (f.inv.left.app V).hom (jac D V t) := by
  have : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  obtain ⟨h, hh⟩ := exists_ratio D (fun i => transport f.inv (D i)) hD
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsIso A.hom.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_field A.hom
  obtain ⟨c', rfl⟩ := (ConcreteCategory.bijective_of_isIso A.hom.appTop).2 h
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 c'
  have key : ∀ (V : A.left.Opens) (t : I → Γ(A.left, V)),
      jac D _ (fun i => (f.inv.left.app V).hom (t i)) = cstK A _ c * (f.inv.left.app V).hom (jac D V t) := by
    intro V t
    rw [← app_jac, hh, map_mul, ← app_cstK f.inv V c]
    rfl
  refine ⟨c, ?_, key⟩
  rintro rfl
  obtain ⟨x⟩ : Nonempty A.left := inferInstance
  obtain ⟨U, t, hx, hu⟩ := hD.2 x
  have e : f.inv.left ⁻¹ᵁ (f.hom.left ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, f.inv_hom_id]; rfl
  have h1 := key (f.hom.left ⁻¹ᵁ U) (fun i => (appE f.inv _).symm (rs e.le (t i)))
  simp only [app_symm, map_zero, zero_mul] at h1
  have h2 := hu.map (rs e.le)
  rw [rs_jac, h1] at h2
  have : Nonempty (f.inv.left ⁻¹ᵁ (f.hom.left ⁻¹ᵁ U) : A.left.Opens) := ⟨⟨x, e.ge hx⟩⟩
  exact not_isUnit_zero h2

def cstR {R : Type} [CommRing R] [Algebra R K] (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem app_cstR {R : Type} [CommRing R] [Algebra R K] (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by
  have h : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U =
      (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE M.j M.Y.hom ⊤ U _ le_top le_rfl).trans ?_
    simp only [M.j_hom]
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  refine Eq.trans congr($h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ?_
  exact congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm

theorem main : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  intro R K _ _ _ _ _ _ π hπ A _ hA I _ _ D hD f
  obtain ⟨c₀, hc₀, key⟩ := exists_const hA D hD f
  obtain ⟨c, u, hc⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hc₀
  have hπ0 : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  refine ⟨c, fun M n hM => ?_⟩
  have step : ∀ (j : A.left ⟶ M.Y.left), j = f.inv.left ≫ M.j → ∀ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U))
      (s : Γ(M.Y.left, U)),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s →
      jac D (j ⁻¹ᵁ U) (fun i => (j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ (n + c)) * (j.app U).hom (cstR M U u * s) := by
    rintro j rfl U t s h
    have h1 := key (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i))
    rw [h, map_mul, app_cstK] at h1
    refine Eq.trans h1 ?_
    show _ = cstK A (f.inv.left ⁻¹ᵁ M.j ⁻¹ᵁ U) _ * (f.inv.left.app (M.j ⁻¹ᵁ U)).hom ((M.j.app U).hom (cstR M U u * s))
    rw [map_mul, map_mul, app_cstR, app_cstK, hc, zpow_add₀ hπ0, Units.smul_def, Algebra.smul_def]
    simp only [map_mul]
    ring
  have hj : (M.twist f).j = f.inv.left ≫ M.j := by simp [Model.j, Model.twist]
  refine ⟨fun U t => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hM.1 U t
    exact ⟨_, step _ hj U t s hs⟩
  · obtain ⟨U, t, s, hU, hs, h⟩ := hM.2
    exact ⟨U, t, _, hU, (u.isUnit.map _).mul hs, step _ hj U t s h⟩

end GlobalTheory.SS.OrdTwist
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  atlas_forward_decl GlobalTheory.SS.OrdTwist.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SS.WeakNeronDef

theorem fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

theorem isDominant_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (N : Model R A) : IsPullback N.j A.hom N.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w N.e.inv
  have : IsIso N.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K)))
    (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem exists_dvr_point (N : Model R A) [IsIntegral N.Y.left] (hN : N.Irr) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ y ∈ N.sp, IsDiscreteValuationRing (N.Y.left.presheaf.stalk y) ∧
      Irreducible (((Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫
        N.Y.left.presheaf.germ ⊤ y trivial).hom ϖ) := by
  have := N.smooth
  have hs := IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  have hr : Set.range i = N.sp := Set.ext fun x => DvrModel.mem_range_special hs x
  have : IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    have h1 : IrreducibleSpace (Set.range i) := by
      rw [hr]; exact Subtype.irreducibleSpace hN
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨_, hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩

end GlobalTheory.SS.WeakNeronDef

namespace GlobalTheory.SS

open WeakNeronDef

theorem exists_defAt_of_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away K hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelMapDefined_weakNeronFamily : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  atlas_forward_decl GlobalTheory.SS.exists_defAt_of_weakNeron
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem Model.twist_twist_symm {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
    (M : Model R A) (f : A ≅ A') : (M.twist f).twist f.symm = M := by
  obtain ⟨Y, e, h₁, h₂, h₃⟩ := M
  simp [Model.twist]

theorem isIntegral_of_abelian {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem exists_genIso_of_max_ord (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) (π : R) (hπ : Irreducible π) (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A) (hD : IsFrame D)
    (J : Type) (M : J → Model R A) (hI : ∀ j, (M j).Irr) (hW : WeakNeron M) (o : J → ℤ)
    (ho : ∀ j, HasOrd (M j) D π (o j)) (ρ : ℤ) (hρ : ∀ j, o j ≤ ρ) (f : A ≅ A) (i : J) (hi : o i = ρ) :
    ∃ i', o i' = ρ ∧ GenIso (M i) (M i') f.hom := by
  have hint := isIntegral_of_abelian A hA
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have bound : ∀ (N : Model R A) (m : ℤ), N.Irr → HasOrd N D π m →
      m ≤ ρ ∧ (m = ρ → ∃ i', o i' = ρ ∧ GenIso N (M i') (𝟙 A)) := by
    intro N m hN hm
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_modelMapDefined_weakNeronFamily R K A J M hW N hN
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.jacobian_order_monotone_semistableModel R K π hπ A I D hD N (M j) m (o j) hN (hI j) hm (ho j) hj
    have := hρ j
    exact ⟨h₁.trans this, fun e => ⟨j, by omega, h₂ (by omega)⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f
  obtain ⟨c', hc'⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f.symm
  have t₁ := hc _ _ (ho i)
  have t₂ := hc' _ _ (ho i)
  have t₃ := hc' _ _ t₁
  rw [Model.twist_twist_symm] at t₃
  have e₃ := (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A I D hD (M i) (hI i)).unique t₃ (ho i)
  have i₁ : ((M i).twist f).Irr := hI i
  have i₂ : ((M i).twist f.symm).Irr := hI i
  obtain ⟨b₁, b₁'⟩ := bound _ _ i₁ t₁
  obtain ⟨b₂, -⟩ := bound _ _ i₂ t₂
  obtain ⟨i', hi', hg⟩ := b₁' (by omega)
  exact ⟨i', hi', (h3 A A (M i) (M i') f).2.1.2 hg⟩

theorem WeakNeron.nonempty {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) {A : Over (Sp K)} [GrpObj A] {J : Type} {M : J → Model R A} (hW : WeakNeron M) :
    Nonempty J := by
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  obtain ⟨i, -⟩ := hW R K (by simp) (η[A]).left (by
    rw [← Category.assoc, Over.w]
    simp)
  exact ⟨i⟩

theorem exists_permuted_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  have hne := hW.nonempty hSH
  have hdvr := hSH.1
  have hfr := hSH.2.2.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme K A g hg
  choose o ho using fun i => (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A (Fin g) D hD (M i) (hI i)).exists
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max o
  refine ⟨Finset.univ.filter fun i => o i = o i₀, ⟨i₀, by simp⟩, ?_, ?_⟩
  · intro f i hi
    obtain ⟨i', hi', h⟩ := exists_genIso_of_max_ord R K hSH π hπ A hA _ D hD _ M hI hW o ho (o i₀) hi₀ f i
      (by simpa using hi)
    exact ⟨i', by simpa using hi', h⟩
  · intro Θ i hi j hj
    have hi : o i = o i₀ := by simpa using hi
    have hj : o j = o i₀ := by simpa using hj
    obtain ⟨D₂, hD₂, hp⟩ := GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian R K hSH π hπ A A _ _ D D hD hD
    obtain ⟨p₁, p₂⟩ := GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A
    obtain ⟨⟨i', j'⟩, h', h⟩ := exists_genIso_of_max_ord R K hSH π hπ (A ⊗ A)
      (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ D₂ hD₂ (Fin n × Fin n)
      (fun p => (M p.1).prod (M p.2)) (fun p => p₁ _ _ (hI _) (hI _)) (p₂ _ _ M M hW hW)
      (fun p => o p.1 + o p.2) (fun p => hp _ _ _ _ (hI _) (hI _) (ho _) (ho _)) (o i₀ + o i₀)
      (fun p => add_le_add (hi₀ _) (hi₀ _)) Θ (i, j) (by simp [hi, hj])
    have a₁ := hi₀ i'
    have a₂ := hi₀ j'
    have h' : o i' + o j' = o i₀ + o i₀ := h'
    exact ⟨i', by simp; omega, j', by simp; omega, h⟩

end GlobalTheory.SS
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphism_permutation_maxOrder_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  first | exact @GlobalTheory.SS.exists_permuted_members | exact GlobalTheory.SS.exists_permuted_members | (intros; apply GlobalTheory.SS.exists_permuted_members <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS.NeutralModel

theorem exists_idem_of_rel {S : Type} [Finite S] [Nonempty S] (r : Setoid S) (T : S → S → S → Prop)
    (tot : ∀ i j, ∃ k, T i j k) (resp : ∀ i j k k', T i j k → r k k' → T i j k')
    (assoc : ∀ i j l k m p q, T i j k → T k l m → T j l p → T i p q → r m q) : ∃ e, T e e e := by
  choose f hf using tot
  let mul : Quotient r → Quotient r → Quotient r := fun a b => Quotient.mk r (f a.out b.out)
  have hm : ∀ a b, T a.out b.out (mul a b).out := fun a b =>
    resp _ _ _ _ (hf _ _) (r.symm (Quotient.mk_out _))
  letI : Semigroup (Quotient r) :=
    { mul := mul
      mul_assoc := fun a b c => by
        have := assoc _ _ _ _ _ _ _ (hm a b) (hm (mul a b) c) (hm b c) (hm a (mul b c))
        have h2 := Quotient.sound this
        rwa [Quotient.out_eq, Quotient.out_eq] at h2 }
  letI : TopologicalSpace (Quotient r) := ⊥
  haveI : DiscreteTopology (Quotient r) := ⟨rfl⟩
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary S)⟩
  obtain ⟨e, he⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left (M := Quotient r)
    (fun _ => continuous_of_discreteTopology)
  refine ⟨e.out, ?_⟩
  have := hm e e
  rwa [show mul e e = e from he] at this

theorem rel_factorial {S : Type} [Fintype S] (T : ℕ → S → S → Prop) (tot : ∀ i, ∃ j, T 1 i j)
    (zero : ∀ i, T 0 i i) (add : ∀ p q i j k, T p i j → T q j k → T (p + q) i k)
    (sub : ∀ p d i j, T p i j → T (p + d) i j → T d i i) (i : S) : T (Fintype.card S).factorial i i := by
  choose σ hσ using tot
  have hit : ∀ p, T p i (σ^[p] i) := by
    intro p
    induction p with
    | zero => exact zero i
    | succ p ih => rw [Function.iterate_succ_apply']; exact add _ _ _ _ _ ih (hσ _)
  have hmul : ∀ d, T d i i → ∀ m, T (d * m) i i := by
    intro d hd m
    induction m with
    | zero => exact zero i
    | succ m ih => rw [Nat.mul_succ]; exact add _ _ _ _ _ ih hd
  have key : ∀ p q : Fin (Fintype.card S + 1), p < q → σ^[p] i = σ^[q] i → T (Fintype.card S).factorial i i := by
    intro p q hpq h
    have hq : (q : ℕ) = p + (q - p) := by have : (p : ℕ) < q := hpq; omega
    have h1 : T (q - p) i i := sub p _ i _ (hit p) (by rw [← hq, h]; exact hit q)
    obtain ⟨m, hm⟩ : (q - p : ℕ) ∣ (Fintype.card S).factorial :=
      Nat.dvd_factorial (by have : (p : ℕ) < q := hpq; omega) (by have := q.2; omega)
    rw [hm]; exact hmul _ h1 m
  obtain ⟨p, q, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : Fin (Fintype.card S + 1) => σ^[p] i) (by simp)
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact key p q h' h
  · exact key q p h' h.symm

section
variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A]

noncomputable def shearIso : A ⊗ A ≅ A ⊗ A where
  hom := shear A true
  inv := shear A false
  hom_inv_id := by
    ext <;> simp [shear, MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    ext <;> simp [shear, MonObj.comp_mul, GrpObj.comp_inv]

instance : IsIso (shear A true) := (shearIso A).isIso_hom

theorem triple_fst :
    ((shear A true ⊗ₘ 𝟙 A) ≫ (α_ A A A).hom ≫ (𝟙 A ⊗ₘ (shear A true ≫ (β_ A A).hom)) ≫ (β_ A (A ⊗ A)).hom ≫
      (α_ A A A).hom) ≫ fst A (A ⊗ A) =
    ((α_ A A A).hom ≫ (𝟙 A ⊗ₘ (shear A true ≫ (β_ A A).hom)) ≫ (α_ A A A).inv ≫
      ((shear A true ≫ (β_ A A).hom) ⊗ₘ 𝟙 A) ≫ (α_ A A A).hom) ≫ fst A (A ⊗ A) := by
  simp [shear, MonObj.comp_mul, _root_.mul_assoc]

theorem inv_fst :
    ((β_ A A).hom ≫ shear A true ≫ (β_ A A).hom ≫ shear A false ≫ (β_ A A).hom) ≫ fst A A = fst A A ≫ ι[A] := by
  simp [shear, MonObj.comp_mul, GrpObj.comp_inv]
  rfl

noncomputable def invIso : A ≅ A := asIso ι[A]

variable {A} [IsCommMonObj A]

theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  simp [transl]

theorem transl_mul (a b : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom ≫ (transl b).hom = (transl (a * b)).hom := by
  simp [transl, MonObj.comp_mul, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc, mul_left_comm, _root_.mul_assoc]
end

theorem integral_powers {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left ∧ IsIntegral (A ⊗ A).left ∧ IsIntegral (A ⊗ (A ⊗ A)).left := by
  have := hA.smooth
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have h1 : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have h2 : IsIntegral (A ⊗ A).left := inferInstanceAs (IsIntegral (pullback A.hom A.hom))
  have : LocallyOfFiniteType (A ⊗ A).hom := by
    show LocallyOfFiniteType (pullback.fst _ _ ≫ A.hom); infer_instance
  have : IsLocallyNoetherian (A ⊗ A).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ A).hom
  exact ⟨h1, h2, inferInstanceAs (IsIntegral (pullback A.hom (A ⊗ A).hom))⟩

theorem exists_birLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  obtain ⟨h1, h2, h3⟩ := integral_powers A hA
  obtain ⟨hle, hcomp, hiso, hprod, hstr⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  have hP : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr → (X.prod Y).Irr :=
    fun {B B' X Y} => (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH B B').1 X Y
  have hproj := GlobalTheory.T.generic_isomorphism_product_models R K hSH
  obtain ⟨S, hne, hS1, hS2⟩ := GlobalTheory.T.exists_automorphism_permutation_maxOrder_members R K hSH A hA n M hI hW
  have refl : ∀ {B : Over (Sp K)} {X : Model R B}, X.Irr → GenIso X X (𝟙 B) :=
    fun {B X} h => hle B X X h X.le_refl
  have comp : ∀ {B B' B'' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R B''} {f : B ⟶ B'}
      {g : B' ⟶ B''}, Y.Irr → GenIso X Y f → GenIso Y Z g → GenIso X Z (f ≫ g) :=
    fun {B B' B'' X Y Z f g} => hcomp B B' B'' X Y Z f g
  have symm : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'} (f : B ≅ B'),
      GenIso X Y f.hom → GenIso Y X f.inv := fun {B B' X Y} f => (hiso B B' X Y f).1
  have prod : ∀ {B B' C C' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R C} {V : Model R C'}
      {f : B ⟶ C} {g : B' ⟶ C'}, GenIso X Z f → GenIso Y V g → GenIso (X.prod Y) (Z.prod V) (f ⊗ₘ g) :=
    fun {B B' C C' X Y Z V f g} => hprod B B' C C' X Y Z V f g
  have asc : ∀ i j k, GenIso (((M i).prod (M j)).prod (M k)) ((M i).prod ((M j).prod (M k))) (α_ A A A).hom :=
    fun i j k => (hstr A A A _ _ _ (hI i) (hI j) (hI k)).1
  have swp : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr →
      GenIso (X.prod Y) (Y.prod X) (β_ B B').hom :=
    fun {B B' X Y} hX hY => (hstr B B' B X Y X hX hY hX).2
  have cmp : ∀ {C B : Over (Sp K)} [IsIntegral (A ⊗ B).left] {P : Model R C} {X X' : Model R A} {Y Y' : Model R B}
      (f g : C ⟶ A ⊗ B) [IsIso f], P.Irr → X.Irr → X'.Irr → Y.Irr → Y'.Irr → f ≫ fst A B = g ≫ fst A B →
      GenIso P (X.prod Y) f → GenIso P (X'.prod Y') g → GenIso X X' (𝟙 A) := by
    intro C B _ P X X' Y Y' f g _ hP hX hX' hY hY' e hf hg
    refine hproj A A B B X X' Y Y' (Iso.refl A) ((asIso f).inv ≫ g) hX hX' hY hY' ?_
      (comp hP (symm (asIso f) hf) hg)
    simp [← e]
  let r : Setoid S :=
    { r := fun i j => GenIso (M i) (M j) (𝟙 A)
      iseqv := ⟨fun i => refl (hI i), fun h => symm (Iso.refl A) h,
        fun h h' => by simpa using comp (hI _) h h'⟩ }
  let T : S → S → S → Prop := fun i j k => GenIso ((M i).prod (M j)) ((M i).prod (M k)) (shear A true)
  have hT : ∀ {i j k : S}, T i j k →
      GenIso ((M i).prod (M j)) ((M k).prod (M i)) (shear A true ≫ (β_ A A).hom) :=
    fun h => comp (hP (hI _) (hI _)) h (swp (hI _) (hI _))
  haveI : Nonempty S := hne.to_subtype
  obtain ⟨e, he⟩ := exists_idem_of_rel r T
    (by
      intro i j
      obtain ⟨i', hi', k, hk, h⟩ := hS2 (shearIso A) i i.2 j j.2
      have h0 : GenIso (M i) (M i') (𝟙 A) :=
        hproj A A A A _ _ _ _ (Iso.refl A) _ (hI _) (hI _) (hI _) (hI _) (by simp [shearIso, shear]) h
      have := comp (hP (hI _) (hI _)) h (prod (symm (Iso.refl A) h0) (refl (hI k)))
      refine ⟨⟨k, hk⟩, ?_⟩
      simpa [shearIso] using this)
    (by
      intro i j k k' h h'
      have := comp (hP (hI _) (hI _)) h (prod (refl (hI i)) h')
      simpa using this)
    (by
      intro i j l k m p q a b c d
      refine cmp _ _ (hP (hP (hI i) (hI j)) (hI l)) (hI m) (hI q) (hP (hI k) (hI i)) (hP (hI i) (hI j))
        (triple_fst A) ?_ ?_
      · exact comp (hP (hP (hI _) (hI _)) (hI _)) (prod a (refl (hI l))) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT b)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (swp (hI _) (hP (hI _) (hI _))) (asc _ _ _)
      · exact comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT c)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (symm (α_ A A A) (asc _ _ _)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (prod (hT d) (refl (hI j))) (asc _ _ _))
  have he' : GenIso ((M e).prod (M e)) ((M e).prod (M e)) (shear A false) := symm (shearIso A) he
  have hee := hP (hI e) (hI e)
  have hs := swp (hI e) (hI e)
  refine ⟨M e, ⟨hI e, fun b => by cases b <;> assumption, ?_⟩, (Fintype.card S).factorial,
    Nat.factorial_pos _, fun a => ?_⟩
  · exact hproj A A A A _ _ _ _ (invIso A) _ (hI e) (hI e) (hI e) (hI e) (inv_fst A)
      (comp hee hs <| comp hee he <| comp hee hs <| comp hee he' hs)
  · refine rel_factorial (fun p (i j : S) => GenIso (M i) (M j) (transl (a ^ p)).hom) ?_ ?_ ?_ ?_ e
    · intro i
      obtain ⟨j, hj, h⟩ := hS1 (transl (a ^ 1)) i i.2
      exact ⟨⟨j, hj⟩, h⟩
    · intro i
      simp only [pow_zero, transl_one]
      exact refl (hI i)
    · intro p q i j k h h'
      have := comp (hI _) h h'
      rwa [transl_mul, ← pow_add] at this
    · intro p d i j h h'
      have := comp (hI _) h' (symm _ h)
      rwa [add_comm, pow_add, ← transl_mul, Category.assoc, Iso.hom_inv_id, Category.comp_id] at this

end GlobalTheory.SS.NeutralModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weakNeronModel_birational_groupLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  atlas_forward_decl GlobalTheory.SS.NeutralModel.exists_birLaw
end
