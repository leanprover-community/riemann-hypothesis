import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HCXBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingCofaceMapComplexPreadditiveYonedaDApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfProd
import BuildAid.ForwardExisting

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.AugExact

theorem augmented_exact_iff (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C)
    (f : K ⟶ (SimplicialObject.const C).obj B) :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔
      (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
        (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
          (ShortComplex.mk _ _ w).Exact) ∧
        ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv
  let g : (AlgebraicTopology.alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj B) ⟶
      (ChainComplex.single₀ C).obj B := e.hom
  haveI : QuasiIso g := e.quasiIso_hom
  have hg : g.f 0 = 𝟙 B := AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero _
  rw [← quasiIso_iff_comp_right _ g, quasiIso_iff]
  set φ := (AlgebraicTopology.alternatingFaceMapComplex C).map f ≫ g with hφ
  have h0 : φ.f 0 = f.app (op (SimplexCategory.mk 0)) := by
    rw [hφ, HomologicalComplex.comp_f, hg]
    exact Category.comp_id _
  have hd : ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).d 1 0 =
      K.δ (n := 0) 0 - K.δ (n := 0) 1 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj K).d (0 + 1) 0 = _
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  have w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0 := by
    simp [Preadditive.sub_comp, SimplicialObject.δ_naturality, SimplicialObject.δ]
  have he : Epi (φ.f 0) ↔ Epi (f.app (op (SimplexCategory.mk (0)))) := h0 ▸ Iff.rfl
  have hz : QuasiIsoAt φ 0 ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
      (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
        (ShortComplex.mk _ _ w).Exact)) := by
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨he.1 h2, w, (ShortComplex.exact_iff_of_iso ?_).1 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.symm.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.symm.trans (Category.comp_id _).symm))
    · rintro ⟨h1, _, h2⟩
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 h2, he.2 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.trans (Category.comp_id _).symm))
  have hs : ∀ n : ℕ, QuasiIsoAt φ (n + 1) ↔
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1) :=
    fun n => quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)
  constructor
  · intro h
    exact ⟨(hz.1 (h 0)).1, (hz.1 (h 0)).2, fun n => (hs n).1 (h (n + 1))⟩
  · rintro ⟨h1, h2, h3⟩ i
    cases i with
    | zero => exact hz.2 ⟨h1, h2⟩
    | succ n => exact (hs n).2 (h3 n)

end GlobalTheory.EtC.AugExact
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact : ∀ (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C) (f : K ⟶ (SimplicialObject.const C).obj B), QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧ (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0, (ShortComplex.mk _ _ w).Exact) ∧ ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  first | (exact @GlobalTheory.EtC.AugExact.augmented_exact_iff) | (exact GlobalTheory.EtC.AugExact.augmented_exact_iff) | (intros; apply GlobalTheory.EtC.AugExact.augmented_exact_iff  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_preadditiveYoneda_of_injective (R : Type) [CommRing R] (T : Type 1) [Category.{0} T]
    (Ψ : T ⥤ PShᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (J : Shv R) (hJ : Injective J) (hq : QuasiIso ((chains R).map (lev Ψ a))) :
    WExact (Ψ ⋙ (free R).op ⋙ preadditiveYoneda.obj J) a := by
  let K : SimplicialObject (Shv R) := ((SimplicialObject.whiskering _ _).obj (free R)).obj ((X ⋙ Ψ).leftOp)
  let B : Shv R := (free R).obj (Ψ.obj U).unop
  let f : K ⟶ (SimplicialObject.const (Shv R)).obj B :=
    ((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a) ≫ (Functor.constComp _ _ _).hom
  haveI h1 : QuasiIso ((chainsN R).map (lev Ψ a)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).1 hq
  have hq' : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f) := by
    have e : (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map f =
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a)) ≫
        (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp _ _ _).hom :=
      Functor.map_comp _ _ _
    rw [e]
    haveI : IsIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      Functor.map_isIso _ _
    haveI h2 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (((SimplicialObject.whiskering _ _).obj (free R)).map (lev Ψ a))) := h1
    haveI h3 : QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (Functor.constComp SimplexCategoryᵒᵖ (Ψ.obj U).unop (free R)).hom) :=
      quasiIso_of_isIso _
    exact quasiIso_comp (hφ := h2) (hφ' := h3) _ _
  obtain ⟨hepi, ⟨w, hex⟩, hn⟩ := (GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact _ K B f).1 hq'
  have hepi' : Epi ((free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop) := by
    have e : f.app (op (SimplexCategory.mk 0)) = (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop :=
      Category.comp_id _
    rw [← e]; exact hepi
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    change (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ x =
      (free R).map (Ψ.map (a.app (SimplexCategory.mk 0))).unop ≫ y at hxy
    exact (cancel_epi _).1 hxy
  · intro y hy
    change (free R).map (Ψ.map (X.δ (n := 0) 0)).unop ≫ y = (free R).map (Ψ.map (X.δ (n := 0) 1)).unop ≫ y at hy
    let y' : K.obj (op (SimplexCategory.mk 0)) ⟶ J := y
    have hy' : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ y' = 0 := by
      refine (Preadditive.sub_comp _ _ _).trans (sub_eq_zero.2 ?_)
      exact hy
    refine ⟨hex.descToInjective (J := J) y' hy', ?_⟩
    exact hex.comp_descToInjective (J := J) y' hy'
  · intro n
    exact GlobalTheory.alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ K J n (hn n)

end GlobalTheory.EtC
end

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_term_HC (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T]
    (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (h : Hyp R Φ a) (n : ℤ) : WExact (term (Φ ⋙ HC R F) n) a := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  exact GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a ℕ
    (fun k => Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)))
    (term (Φ ⋙ HC R F) n) (fun k => Functor.whiskerLeft Φ (π k)) (fun V => hπ (Φ.obj V))
    (fun k => wExact_preadditiveYoneda_of_injective R T (Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op)
      U X a ((res R F).X (n - k)) ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).1 (n - k)) (h (op (SimplexCategory.mk k))))

end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X), Hyp R Φ a → ∀ n, WExact (term (Φ ⋙ HC R F) n) a := by
  atlas_forward_decl GlobalTheory.EtC.wExact_term_HC
end
