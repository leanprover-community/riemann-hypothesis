import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChange
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictTensor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafHOver
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionCech
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MvPolynomial
open GroundTheory.Arith.Etale (pullbackUnitApp)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

variable (A) in

abbrev cmap :
    C(ProjectiveSpectrum.top (grading B n), ProjectiveSpectrum.top (grading A n)) :=
  ProjectiveSpectrum.comap (gradedMap A B n) (irrelevant_le_map A B n)

variable (A) in

abbrev pt (y : ProjectiveSpectrum (grading B n)) : ProjectiveSpectrum (grading A n) :=
  ProjectiveSpectrum.comapFun (gradedMap A B n) (irrelevant_le_map A B n) y

def locMap (y : ProjectiveSpectrum (grading B n)) :
    ProjTwist.Loc (grading A n) (pt A y) →+* ProjTwist.Loc (grading B n) y :=
  Localization.localRingHom _ _
    (gradedMap A B n : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin (n + 1)) B) rfl

lemma locMap_mk (y : ProjectiveSpectrum (grading B n)) (r : MvPolynomial (Fin (n + 1)) A)
    (s : (pt A y).asHomogeneousIdeal.toIdeal.primeCompl) :
    locMap y (Localization.mk r s) =
      Localization.mk (gradedMap A B n r)
        (⟨gradedMap A B n s, s.2⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) :=
  Localization.localRingHom_mk _ _ _ _ _ _

variable (k : ℤ)

def twistPushSec {V : (projectiveSpace A n).Opens} (s : Γ(twistingSheaf (grading A n) k, V)) :
    Γ(twistingSheaf (grading B n) k, baseChangeMap A B n ⁻¹ᵁ V) :=
  ProjTwist.mkSection (fun y => locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩))
    (by
      intro y
      obtain ⟨W, hyW, iW, i, j, hij, r, t, hr, ht, htn, w⟩ :=
        ProjTwist.isLocallyFraction_val s ⟨pt A y.1, y.2⟩
      refine ⟨W.comap (cmap (B := B) A), hyW, homOfLE (fun z hz => (leOfHom iW) hz), i, j, hij,
        gradedMap A B n r, gradedMap A B n t, (gradedMap A B n).2 hr, (gradedMap A B n).2 ht,
        fun z => htn ⟨pt A z.1, z.2⟩, fun z => ?_⟩
      have e := w ⟨pt A z.1, z.2⟩
      change locMap z.1 (ProjTwist.val s ⟨pt A z.1, _⟩) = _
      change ProjTwist.val s ⟨pt A z.1, _⟩ = _ at e
      rw [e]
      exact locMap_mk _ _ _)

lemma val_app_apply {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (y : baseChangeMap A B n ⁻¹ᵁ V) :
    ((((baseChangeMap A B n).app V t) : Γ(Proj (grading B n), _)).1 y).val =
      locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val) := by
  have : y.1.asHomogeneousIdeal.toIdeal.IsPrime :=
    ProjectiveSpectrum.isPrime (y.1 : ProjectiveSpectrum (grading B n))
  show HomogeneousLocalization.val (HomogeneousLocalization.localRingHom (gradedMap A B n)
    (pt A y.1).asHomogeneousIdeal.toIdeal y.1.asHomogeneousIdeal.toIdeal rfl (t.1 ⟨pt A y.1, y.2⟩)) = _
  exact HomogeneousLocalization.val_localRingHom _

lemma twistPushSec_smul {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (t • s) = (baseChangeMap A B n).app V t • twistPushSec (B := B) k s := by
  apply ProjTwist.ext
  funext y
  show locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val * ProjTwist.val s ⟨pt A y.1, y.2⟩) =
    (((baseChangeMap A B n).app V t).1 y).val * locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩)
  exact (map_mul (locMap y.1) _ _).trans (congrArg (· * _) (val_app_apply t y).symm)

lemma twistPushSec_add {V : (projectiveSpace A n).Opens}
    (s s' : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (s + s') = twistPushSec k s + twistPushSec k s' := by
  apply ProjTwist.ext
  funext y
  show locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩ + ProjTwist.val s' ⟨pt A y.1, y.2⟩) =
    locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩) + locMap y.1 (ProjTwist.val s' ⟨pt A y.1, y.2⟩)
  exact map_add _ _ _

def twistToPushforward :
    twistingSheaf (grading A n) k ⟶
      (Scheme.Modules.pushforward (baseChangeMap A B n)).obj (twistingSheaf (grading B n) k) :=
  ⟨{ app V := ModuleCat.ofHom (X := (twistingSheaf (grading A n) k).val.obj V)
      (Y := ((Scheme.Modules.pushforward (baseChangeMap A B n)).obj
        (twistingSheaf (grading B n) k)).val.obj V)
      { toFun := fun s => twistPushSec k (V := V.unop) s
        map_add' := fun s s' => twistPushSec_add k s s'
        map_smul' := fun t s => twistPushSec_smul k t s }
     naturality := fun {V V'} i => by
      ext s
      exact ProjTwist.ext (funext fun y => rfl) }⟩

def pullbackTwistingSheafMap :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ⟶
      twistingSheaf (grading B n) k :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv _ _).symm
    (twistToPushforward k)

lemma pullbackTwistingSheafMap_unit {V : (projectiveSpace A n).Opens}
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    (pullbackTwistingSheafMap (B := B) k).app _ (pullbackUnitApp (baseChangeMap A B n) _ V s) =
      twistPushSec k s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv_unit
    (twistingSheaf (grading A n) k) (twistingSheaf (grading B n) k)
    (pullbackTwistingSheafMap k))
  rw [pullbackTwistingSheafMap, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun g => (Scheme.Modules.Hom.app g V) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h2
  exact h2.symm

lemma twistPushSec_upow {u : MvPolynomial (Fin (n + 1)) A} (hu : u ∈ grading A n 1) :
    twistPushSec (B := B) k (ProjTwist.upow (grading A n) hu k) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 hu) k := by
  apply ProjTwist.ext
  funext y
  change locMap y.1 (ProjTwist.val (ProjTwist.upow (grading A n) hu k) ⟨pt A y.1, y.2⟩) = _
  erw [ProjTwist.val_upow, ProjTwist.val_upow]
  unfold ProjTwist.twistFrac
  refine (locMap_mk _ _ _).trans ?_
  congr 1
  · exact map_pow (gradedMap A B n) u _
  · exact Subtype.ext (map_pow (gradedMap A B n) u _)

instance isIso_pullbackTwistingSheafMap :
    IsIso (pullbackTwistingSheafMap (A := A) (B := B) (n := n) k) := by
  apply isIso_of_isBasisOn
  intro y
  obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj ((baseChangeMap A B n).base y)
  refine ⟨baseChangeMap A B n ⁻¹ᵁ stdOpen A n j, hj,
    pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
      (ProjTwist.upow (grading A n) (X_mem j) k),
    isBasisOn_pullbackUnitApp _ (ProjTwist.isBasisOn_upow _ (X_mem j) k), ?_⟩
  have key : ((preMod _).map (pullbackTwistingSheafMap (B := B) k)).app _
      (pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
        (ProjTwist.upow (grading A n) (X_mem j) k)) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 (X_mem j)) k :=
    (pullbackTwistingSheafMap_unit k _).trans (twistPushSec_upow k _)
  rw [key]
  exact ProjTwist.isBasisOn_upow _ _ k

variable (A B n) in

def pullbackTwistingSheafIso :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ≅
      twistingSheaf (grading B n) k :=
  asIso (pullbackTwistingSheafMap k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} {Y : Scheme.{u}}

variable (A B n) in

def baseChangeIso :
    projectiveSpace B n ≅
      pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  (isPullback_baseChange A B n).isoPullback

@[reassoc (attr := simp)]
lemma baseChangeIso_inv_baseChangeMap :
    (baseChangeIso A B n).inv ≫ baseChangeMap A B n = pullback.fst _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_fst

@[reassoc (attr := simp)]
lemma baseChangeIso_inv_toSpecBase :
    (baseChangeIso A B n).inv ≫ toSpecBase B n = pullback.snd _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_snd

def toBaseChange (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    Y ⟶ projectiveSpace B n :=
  ι ≫ (baseChangeIso A B n).inv

instance (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [IsClosedImmersion ι] : IsClosedImmersion (toBaseChange ι) := by
  rw [toBaseChange]
  infer_instance

@[reassoc (attr := simp)]
lemma toBaseChange_baseChangeMap
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ baseChangeMap A B n = ι ≫ pullback.fst _ _ := by
  simp [toBaseChange]

@[reassoc (attr := simp)]
lemma toBaseChange_toSpecBase
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ toSpecBase B n = ι ≫ pullback.snd _ _ := by
  simp [toBaseChange]

variable (A) in

def twistingSheafBaseChangeIso (g : Y ⟶ projectiveSpace B n) (k : ℤ) :
    ProjScheme.twistingSheaf (g ≫ baseChangeMap A B n) k ≅ ProjScheme.twistingSheaf g k :=
  ((Scheme.Modules.pullbackComp g (baseChangeMap A B n)).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (pullbackTwistingSheafIso A B n k)

variable (A) in

def twistBaseChangeIso (g : Y ⟶ projectiveSpace B n) (F : Y.Modules) (k : ℤ) :
    ProjScheme.twist (g ≫ baseChangeMap A B n) F k ≅ ProjScheme.twist g F k :=
  whiskerLeftIso F (twistingSheafBaseChangeIso A g k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}

variable (A) in

def baseHom {V : X.Opens} (hV : IsAffineOpen V) : CommRingCat.of A ⟶ Γ(X, V) :=
  Spec.preimage (hV.fromSpec ≫ (X ↘ Spec (.of A)))

variable (A) in

abbrev baseAlgebra {V : X.Opens} (hV : IsAffineOpen V) : Algebra A Γ(X, V) :=
  (baseHom A hV).hom.toAlgebra

variable (A) in
lemma specMap_baseAlgebra {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V))) = hV.fromSpec ≫ (X ↘ Spec (.of A)) := by
  change Spec.map (CommRingCat.ofHom (baseHom A hV).hom) = _
  rw [CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

variable (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

abbrev graph : X' ⟶ pullback (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)) :=
  pullback.lift i ψ h

instance isClosedImmersion_graph [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))] :
    IsClosedImmersion (graph i ψ h) := by
  have : IsClosedImmersion (graph i ψ h ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)

variable (A) in

abbrev overV {V : X.Opens} (hV : IsAffineOpen V) :
    pullback (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec ⟶
      pullback (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)) :=
  pullback.fst _ _

lemma preimage_opensRange_overV {V : X.Opens} (hV : IsAffineOpen V) :
    graph i ψ h ⁻¹ᵁ (overV (N := N) A hV).opensRange = ψ ⁻¹ᵁ V := by
  have e1 : (overV (N := N) A hV).opensRange = (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) ⁻¹ᵁ hV.fromSpec.opensRange :=
    Scheme.Hom.opensRange_pullbackFst _ _
  rw [e1, hV.opensRange_fromSpec, ← Scheme.Hom.comp_preimage, pullback.lift_snd]

def restrictT {V : X.Opens} (hV : IsAffineOpen V) :
    pullback (graph i ψ h) (overV (N := N) A hV) ⟶
      pullback (graph i ψ h) (overV (N := N) A hV).opensRange.ι :=
  pullback.map _ _ _ _ (𝟙 _)
    (IsOpenImmersion.isoOfRangeEq (overV (N := N) A hV) (overV (N := N) A hV).opensRange.ι
      Subtype.range_coe.symm).hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; exact (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm)

instance {V : X.Opens} (hV : IsAffineOpen V) : IsIso (restrictT (N := N) i ψ h hV) := by
  unfold restrictT
  infer_instance

lemma inv_restrictT_fst {V : X.Opens} (hV : IsAffineOpen V) :
    inv (restrictT (N := N) i ψ h hV) ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [IsIso.inv_comp_eq, restrictT, pullback.lift_fst, Category.comp_id]

def restrictIso {V : X.Opens} (hV : IsAffineOpen V) :
    (ψ ⁻¹ᵁ V).toScheme ≅ pullback (graph i ψ h) (overV (N := N) A hV) :=
  X'.isoOfEq (preimage_opensRange_overV i ψ h hV).symm ≪≫
    (pullbackRestrictIsoRestrict (graph i ψ h) (overV (N := N) A hV).opensRange).symm ≪≫
    (asIso (restrictT i ψ h hV)).symm

lemma restrictIso_hom_fst {V : X.Opens} (hV : IsAffineOpen V) :
    (restrictIso (N := N) i ψ h hV).hom ≫ pullback.fst _ _ = (ψ ⁻¹ᵁ V).ι := by
  simp only [restrictIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    inv_restrictT_fst, pullbackRestrictIsoRestrict_inv_fst, Scheme.isoOfEq_hom_ι]

variable (A) in

def pasteIso {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    pullback (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec ≅
      pullback (ProjSpace.toSpecBase A N) (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V)))) :=
  letI := baseAlgebra A hV
  pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (specMap_baseAlgebra A hV).symm

variable (A) in
lemma pasteIso_hom_fst {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (pasteIso (N := N) A hV).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [pasteIso, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.map]
  erw [pullback.lift_fst]
  rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

variable (A) in
lemma pasteIso_hom_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (pasteIso (N := N) A hV).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [pasteIso, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.map]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

def embed {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (ψ ⁻¹ᵁ V).toScheme ⟶
      pullback (ProjSpace.toSpecBase A N) (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V)))) :=
  (restrictIso i ψ h hV).hom ≫ pullback.snd _ _ ≫ (pasteIso A hV).hom

instance isClosedImmersion_embed [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) : IsClosedImmersion (embed i ψ h hV) := by
  unfold embed
  infer_instance

lemma embed_fst {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.fst _ _ = (ψ ⁻¹ᵁ V).ι ≫ i := by
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_fst (N := N) A hV
  simp only [embed, Category.assoc]
  rw [hp, ← Category.assoc (pullback.snd _ _) (pullback.fst _ _), show pullback.fst (pullback.snd
    (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec = overV A hV from rfl, hc,
    Category.assoc, pullback.lift_fst, ← Category.assoc, restrictIso_hom_fst]

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

theorem IsCoherent.of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (hM : IsCoherent M) :
    IsCoherent N := by
  obtain ⟨hq, hf⟩ := hM
  refine ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq, fun U hU => ?_⟩
  have := hf U hU
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := e.hom.app U
      map_add' := map_add _
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul e.hom r m }
  refine Module.Finite.of_surjective φ fun n => ⟨e.inv.app U n, ?_⟩
  change (e.inv ≫ e.hom).app U n = n
  rw [e.inv_hom_id]
  rfl

theorem IsCoherent.restrict {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] {G : X.Modules}
    (hG : IsCoherent G) : IsCoherent (G.restrict f) :=
  IsCoherent.of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app G).symm
    (isCoherent_pullback f hG)

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

abbrev overBase {V : X.Opens} (hV : IsAffineOpen V) : (ψ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  letI := baseAlgebra A hV
  ⟨embed i ψ h hV ≫ pullback.snd _ _⟩

def embedProj {V : X.Opens} (hV : IsAffineOpen V) : (ψ ⁻¹ᵁ V).toScheme ⟶ projectiveSpace Γ(X, V) N :=
  letI := baseAlgebra A hV
  ProjSpace.toBaseChange (embed i ψ h hV)

instance isClosedImmersion_embedProj [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) : IsClosedImmersion (embedProj i ψ h hV) := by
  letI := baseAlgebra A hV
  unfold embedProj
  infer_instance

lemma embedProj_isOver {V : X.Opens} (hV : IsAffineOpen V) :
    letI := overBase i ψ h hV
    (embedProj i ψ h hV).IsOver (Spec (.of Γ(X, V))) := by
  letI := baseAlgebra A hV
  letI := overBase i ψ h hV
  exact ⟨ProjSpace.toBaseChange_toSpecBase _⟩

lemma embedProj_baseChangeMap {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embedProj i ψ h hV ≫ ProjSpace.baseChangeMap A Γ(X, V) N = (ψ ⁻¹ᵁ V).ι ≫ i := by
  letI := baseAlgebra A hV
  rw [embedProj, ProjSpace.toBaseChange_baseChangeMap, embed_fst]

def twistRestrictIso {V : X.Opens} (hV : IsAffineOpen V) (G : X'.Modules) (k : ℤ) :
    ProjScheme.twist (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) k ≅
      (ProjScheme.twist i G k).restrict (ψ ⁻¹ᵁ V).ι :=
  letI := baseAlgebra A hV
  (ProjSpace.twistBaseChangeIso A (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) k).symm ≪≫
    eqToIso (congrArg (fun g => ProjScheme.twist g (G.restrict (ψ ⁻¹ᵁ V).ι) k)
      (embedProj_baseChangeMap i ψ h hV)) ≪≫
    restrictTwistIso (ψ ⁻¹ᵁ V).ι i G k

attribute [local instance] algebraOfOver

theorem exists_vanishing_finite [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (G : X'.Modules)
    (hG : IsCoherent G) :
    letI := overBase i ψ h hV
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton
        (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ V).ι)) (q + 1))) ∧
      Module.Finite Γ(X, V)
        (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ V).ι)) 0) := by
  letI := overBase i ψ h hV
  haveI := embedProj_isOver i ψ h hV
  have hGr : IsCoherent (G.restrict (ψ ⁻¹ᵁ V).ι) := hG.restrict _
  obtain ⟨q₀, hq₀⟩ := ProjScheme.exists_subsingleton_H_twist.{u} (embedProj i ψ h hV) _ hGr
  refine ⟨q₀, fun n hn => ⟨fun q => ?_, ?_⟩⟩
  · have h1 := hq₀ n hn (q + 1) (Nat.succ_pos q)
    exact (H.linearEquivOfIso.{u} Γ(X, V) (twistRestrictIso i ψ h hV G n) (q + 1)).toEquiv.subsingleton_congr.1
      h1
  · have hc : IsCoherent (ProjScheme.twist (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) n) :=
      isCoherent_tensor_of_invertible hGr (ProjScheme.isInvertibleSheaf_twistingSheaf _ _)
    have h2 := ProjScheme.finite_H.{u} (embedProj i ψ h hV) _ hc 0
    exact Module.Finite.equiv (H.linearEquivOfIso.{u} Γ(X, V) (twistRestrictIso i ψ h hV G n) 0)

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

lemma embed_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.snd _ _ = ψ ∣_ V ≫ hV.isoSpec.hom := by
  letI := baseAlgebra A hV
  rw [← cancel_mono hV.fromSpec, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι]
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_snd (N := N) A hV
  have hq : pullback.snd (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)))
      hV.fromSpec ≫ hV.fromSpec = overV A hV ≫ pullback.snd _ _ := pullback.condition.symm
  simp only [embed, Category.assoc]
  rw [reassoc_of% hp, hq, reassoc_of% hc, pullback.lift_snd, ← Category.assoc, restrictIso_hom_fst]

lemma app_eqToHom_apply {X X' : Scheme.{u}} (ψ : X' ⟶ X) {U U' : X.Opens} (hU : U' = U)
    {W W' : X'.Opens} (h1 : W = ψ ⁻¹ᵁ U') (h2 : W' = W) (b : Γ(X, U)) :
    X'.presheaf.map (eqToHom h2).op (X'.presheaf.map (eqToHom h1).op
      (ψ.app U' (X.presheaf.map (eqToHom hU).op b))) =
      X'.presheaf.map (eqToHom (h2.trans (h1.trans (by rw [hU])))).op (ψ.app U b) := by
  subst hU
  subst h1
  subst h2
  simp

attribute [local instance] algebraOfOver

lemma algebraMap_overBase {V : X.Opens} (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI := overBase i ψ h hV
    X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(X', (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      ψ.app V b := by
  letI := overBase i ψ h hV
  have s1 : algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b = (ψ ∣_ V).appTop (V.topIso.inv b) := by
    change (embed i ψ h hV ≫ pullback.snd _ _).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [embed_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (app_eqToHom_apply ψ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

omit [X.Over (Spec (.of A))] in

lemma smul_restrict_top (M : X'.Modules) (U : X'.Opens) (a : Γ(U.toScheme, ⊤))
    (y : Γ(M.restrict U.ι, ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
      ((modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y) =
      X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
        (a : Γ(X', U.ι ''ᵁ ⊤)) •
        M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
          (y : Γ(M, U.ι ''ᵁ ⊤)) := by
  have e1 : (modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y =
      restrictTop (X := U.toScheme) ⊤ a • y := rfl
  have e2 : restrictTop (X := U.toScheme) ⊤ a = a := by
    simp [restrictTop]; rfl
  have e3 : (a • y : Γ(M.restrict U.ι, ⊤)) =
      ((U.ι.appIso ⊤).inv a • (@id Γ(M, U.ι ''ᵁ ⊤) y) : Γ(M, U.ι ''ᵁ ⊤)) := rfl
  rw [e1, e2, e3, Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact Scheme.Modules.map_smul M (eqToHom (Scheme.Opens.ι_image_top U).symm) a y

def H0ToSections {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward ψ).obj M, V) :=
  letI := overBase i ψ h hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (smul_restrict_top M (ψ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overBase i ψ h hV b)).trans ?_
      exact (smul_pushforward ψ M b _).symm }

lemma H0ToSections_bijective {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    Function.Bijective (H0ToSections i ψ h hV M) := by
  letI := overBase i ψ h hV
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop).bijective

theorem finite_sections_pushforward {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Module.Finite Γ(X, V) (Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0) →
      Module.Finite Γ(X, V) Γ((Scheme.Modules.pushforward ψ).obj M, V) := by
  letI := overBase i ψ h hV
  intro hfin
  exact Module.Finite.of_surjective (H0ToSections i ψ h hV M) (H0ToSections_bijective i ψ h hV M).2

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian TopologicalSpace AlgebraicGeometry

universe w' v u

noncomputable section

section Congr

variable {C D : Type v} [SmallCategory C] [SmallCategory D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  {T : C} (hT : IsTerminal T)

abbrev sheafCongrAb : Sheaf J AddCommGrpCat.{v} ≌ Sheaf K AddCommGrpCat.{v} :=
  e.sheafCongr J K AddCommGrpCat.{v}

def sheafCongrSectionsIso :
    (sheafCongrAb J K e).inverse ⋙ (sheafSections J AddCommGrpCat.{v}).obj (op T) ≅
      (sheafSections K AddCommGrpCat.{v}).obj (op (e.functor.obj T)) :=
  Iso.refl _

def constantSheafCongrIso :
    constantSheaf J AddCommGrpCat.{v} ⋙ (sheafCongrAb J K e).functor ≅
      constantSheaf K AddCommGrpCat.{v} :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj J AddCommGrpCat.{v} hT).comp (sheafCongrAb J K e).toAdjunction).ofNatIsoRight
      (sheafCongrSectionsIso J K e))
    (constantSheafAdj K AddCommGrpCat.{v} (hT.isTerminalObj e.functor))

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]

instance sheafCongrAb_functor_additive : (sheafCongrAb J K e).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance sheafCongrAb_functor_preservesInjectiveObjects :
    (sheafCongrAb J K e).functor.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafCongrAb J K e).symm.toAdjunction

def sheafHCongr [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (G : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} ((sheafCongrAb J K e).functor.obj G) n :=
  (AddEquiv.ofBijective _ ((sheafCongrAb J K e).functor.mapExt_bijective_of_preservesInjectiveObjects
      _ G n)).trans
    (extAddEquivOfIsoLeft ((constantSheafCongrIso J K e hT).app _) _ n)

end Congr

section Scheme

variable {X : Scheme.{u}} (U : X.Opens)

instance isDenseSubsite_overEquivalence_inverse :
    U.overEquivalence.inverse.IsDenseSubsite (Opens.grothendieckTopology U.toScheme.toTopCat)
      ((Opens.grothendieckTopology X.toTopCat).over U) :=
  U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence


set_option maxHeartbeats 4000000 in

def restrictAbIso (F : X.Modules) :
    (sheafCongrAb ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology U.toScheme.toTopCat) U.overEquivalence).functor.obj
      ((modulesAb F).over U) ≅ modulesAb (F.restrict U.ι) :=
  (SheafOfModules.toSheaf _).mapIso ((Scheme.Modules.overFunctorEquiv U).app F)

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology U.toScheme.toTopCat) AddCommGrpCat.{u})]

def cohomologyPresheafAddEquivRestrict (F : X.Modules) (n : ℕ) :
    (modulesAb F).H' n U ≃+ Sheaf.H.{w'} (modulesAb (F.restrict U.ι)) n :=
  (cohomologyPresheafOverAddEquivOfSmall _ U (modulesAb F) n).trans
    ((sheafHCongr ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology U.toScheme.toTopCat) U.overEquivalence Over.mkIdTerminal
      ((modulesAb F).over U) n).trans
      ((Sheaf.functorH _ n).mapIso (restrictAbIso U F)).addCommGroupIsoToAddEquiv)

lemma subsingleton_H'_of_restrict (F : X.Modules) (n : ℕ)
    [h : Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict U.ι)) n)] :
    Subsingleton ((modulesAb F).H' n U) :=
  (cohomologyPresheafAddEquivRestrict.{w'} U F n).toEquiv.subsingleton

end Scheme

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry

universe w w' u

section Top

variable {X : TopCat.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → Opens X)

def HAcyclicOn (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ {n : ℕ} (i : Fin (n + 1) → ι) (q : ℕ), Subsingleton (G.H' (q + 1) (inter U i))

variable {U}

lemma surjective_app_of_subsingleton_H'
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (V : Opens X) [Subsingleton (S.X₁.H' 1 V)] : Function.Surjective (S.g.hom.app (op V)) := by
  intro y
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    ((H'.equiv₀ S.X₃ V).symm y) rfl (Subsingleton.elim (α := S.X₁.H' 1 V) _ _)
  have key : H'.equiv₀ S.X₃ V (x.comp (Ext.mk₀ S.g) (add_zero 0)) =
      S.g.hom.app (op V) (H'.equiv₀ S.X₂ V x) := H'.equiv₀_naturality S.g V x
  exact ⟨H'.equiv₀ S.X₂ V x, by rw [← key, hx, AddEquiv.apply_symm_apply]⟩

lemma subsingleton_H'_of_injective
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    [Injective S.X₂] (V : Opens X) (q : ℕ) [Subsingleton (S.X₁.H' (q + 2) V)] :
    Subsingleton (S.X₃.H' (q + 1) V) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    y rfl (Subsingleton.elim (α := S.X₁.H' (q + 2) V) _ _)
  have : Subsingleton (S.X₂.H' (q + 1) V) := H'.subsingleton_of_injective S.X₂ q V
  have hx0 : x = 0 := Subsingleton.elim (α := S.X₂.H' (q + 1) V) _ _
  rw [← hx, hx0, Ext.zero_comp]
  rfl

variable (U)

lemma injectiveSequence_isCechShortExact_of_acyclic
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    IsCechShortExact U (injectiveSequence G).f.hom (injectiveSequence G).g.hom :=
  isCechShortExact_of_surjective (injectiveSequence_shortExact G) U fun i =>
    have : Subsingleton ((injectiveSequence G).X₁.H' 1 (inter U i)) := hG i 0
    surjective_app_of_subsingleton_H'.{w'} (injectiveSequence_shortExact G) _

lemma injectiveSequence_hAcyclicOn
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    HAcyclicOn.{w, w'} U (injectiveSequence G).X₃ := fun i q =>
  have : Subsingleton ((injectiveSequence G).X₁.H' (q + 2) (inter U i)) := hG i (q + 1)
  have : Injective (injectiveSequence G).X₂ := inferInstanceAs (Injective (Injective.under G))
  subsingleton_H'_of_injective (injectiveSequence_shortExact G) _ q

variable (hU : iSup U = ⊤)

def cechHEquivOfAcyclic : ∀ (n : ℕ) (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
    HAcyclicOn.{w, w'} U G → (cechH G.obj U n ≃+ Sheaf.H.{w'} G n)
  | 0, G, _ => cechHZeroEquivH G U hU
  | 1, G, hG => cechHOneEquiv (S := injectiveSequence G) U hU (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U)
  | m + 2, G, hG => cechHEquivStep (S := injectiveSequence G) U (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U) m
      (cechHEquivOfAcyclic (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))

theorem cechHEquivOfAcyclic_naturality : ∀ (n : ℕ)
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hG : HAcyclicOn.{w, w'} U G) (hG' : HAcyclicOn.{w, w'} U G') (φ : G ⟶ G')
    (x : cechH G.obj U n),
    cechHEquivOfAcyclic U hU n G' hG' (cechHMap U φ.hom n x) =
      Sheaf.H.map.{w'} φ n (cechHEquivOfAcyclic U hU n G hG x)
  | 0, _, _, _, _, φ, x => cechHZeroEquivH_naturality U φ hU x
  | 1, G, G', hG, hG', φ, x =>
      cechHOneEquiv_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U hU
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) x
  | m + 2, G, G', hG, hG', φ, x =>
      cechHEquivStep_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) m
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G' hG'))
        (fun y => cechHEquivOfAcyclic_naturality (m + 1) (injectiveSequence_hAcyclicOn U G hG)
          (injectiveSequence_hAcyclicOn U G' hG') (injectiveSequenceMap φ).τ₃ y) x

end Top

section Scheme

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → X.Opens) (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def cechHLinearEquivHOfAcyclic (hU : iSup U = ⊤) (F : X.Modules)
    (hF : HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F)) (n : ℕ) :
    cechH (modulesAb F).obj U n ≃ₗ[A] Sheaf.H.{w'} (modulesAb F) n :=
  (cechHEquivOfAcyclic (X := X.toTopCat) U hU n (modulesAb F) hF).toLinearEquiv fun a x =>
    cechHEquivOfAcyclic_naturality (X := X.toTopCat) U hU n hF hF
      (modulesAbMap (smulHom F (algebraMap A Γ(X, ⊤) a))) x

variable [∀ V : X.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]

lemma hAcyclicOn_of_restrict (F : X.Modules)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict (⨅ a, U (i a)).ι)) (q + 1))) :
    HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F) := fun {n} i q => by
  have := h n i q
  rw [inter_eq_iInf]
  exact subsingleton_H'_of_restrict.{w'} (⨅ a, U (i a)) F (q + 1)

end Scheme

section Pushforward

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) (A : Type u) [CommRing A] [X.Over (Spec (.of A))]
  [X'.Over (Spec (.of A))] [ψ.IsOver (Spec (.of A))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u})]
  [∀ V : X'.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X'.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X'.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (V : ι → X.Opens) (hV : iSup V = ⊤)
  (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, V (i a)))

attribute [local instance] algebraOfOver

def HLinearEquivPushforwardOfAcyclic (G : X'.Modules)
    [((Scheme.Modules.pushforward ψ).obj G).IsQuasicoherent]
    (hG : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (G.restrict (ψ ⁻¹ᵁ ⨅ a, V (i a)).ι)) (q + 1)))
    (p : ℕ) :
    Sheaf.H.{w'} (modulesAb G) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward ψ).obj G)) p :=
  have hV' : iSup (fun j => ψ ⁻¹ᵁ V j) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]
    rfl
  have hG' : HAcyclicOn.{w, w'} (X := X'.toTopCat) (fun j => ψ ⁻¹ᵁ V j) (modulesAb G) :=
    hAcyclicOn_of_restrict _ G fun n i q => by
      have e := preimage_inter ψ V i
      rw [inter_eq_iInf, inter_eq_iInf] at e
      have h1 := hG n i q
      rw [e] at h1
      exact h1
  (cechHLinearEquivHOfAcyclic (fun j => ψ ⁻¹ᵁ V j) A hV' G hG' p).symm ≪≫ₗ
    (cechHPushforwardLinearEquiv ψ A G V p).symm ≪≫ₗ cechHLinearEquivH V hV hVaff A _ p

end Pushforward

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {Y : Scheme.{u}} (G : Y.Modules)

lemma eq_of_forall_resF {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens} (hle : ∀ k, W k ≤ U)
    (hcov : U ≤ iSup W) (m m' : Γ(G, U)) (h : ∀ k, resF G (hle k) m = resF G (hle k) m') :
    m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' (modulesAb G) W U (fun k => homOfLE (hle k)) hcov m m' h

lemma exists_resF_eq_of_compatible {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens}
    (hle : ∀ k, W k ≤ U) (hcov : U ≤ iSup W) (σ : ∀ k, Γ(G, W k))
    (hσ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) :
    ∃ m : Γ(G, U), ∀ k, resF G (hle k) m = σ k := by
  obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesAb G) W U
    (fun k => homOfLE (hle k)) hcov σ
    (fun k l => hσ k l)
  exact ⟨m, hm⟩

variable [G.IsQuasicoherent]

lemma basicOpen_resO_le {U W : Y.Opens} (hWU : W ≤ U) (h : Γ(Y, U)) :
    Y.basicOpen (resO hWU h) ≤ Y.basicOpen h := by
  rw [Scheme.basicOpen_res]
  exact inf_le_right

theorem qcoh_exists_pow_smul_eq_zero_of_isCompact {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (h : Γ(Y, U)) (m : Γ(G, U)) (hm : resF G (Y.basicOpen_le h) m = 0) :
    ∃ e : ℕ, h ^ e • m = 0 := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have hle : ∀ k : Us, (k : Y.Opens) ≤ U := fun k => hUeq ▸ le_sSup k.2
  have key : ∀ k : Us, ∃ e : ℕ, resO (hle k) h ^ e • resF G (hle k) m = 0 := fun k =>
    qcoh_exists_pow_smul_eq_zero G (hUs k.2) (resO (hle k) h) (resF G (hle k) m) (by
      rw [resF_resF, ← resF_resF G (Y.basicOpen_le h) (basicOpen_resO_le (hle k) h), hm, map_zero])
  choose e he using key
  have := Fintype.ofFinite Us
  refine ⟨Finset.univ.sup e, eq_of_forall_resF G (fun k : Us => (k : Y.Opens)) hle
    (by rw [hUeq, sSup_eq_iSup']) _ _ fun k => ?_⟩
  have hk : e k ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ k)
  rw [map_zero, resF_smul, map_pow, ← Nat.sub_add_cancel hk, pow_add, mul_smul, he k, smul_zero]

theorem qcoh_exists_res_eq_of_qcqs {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (hU' : IsQuasiSeparated (U : Set Y)) (h : Γ(Y, U)) (m : Γ(G, Y.basicOpen h)) :
    ∃ (e : ℕ) (m' : Γ(G, U)), resF G (Y.basicOpen_le h) m' = resO (Y.basicOpen_le h) h ^ e • m := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have := Fintype.ofFinite Us
  let W : Us → Y.Opens := fun k => k
  have hle : ∀ k, W k ≤ U := fun k => hUeq ▸ le_sSup k.2
  have hcov : U ≤ iSup W := by rw [hUeq, sSup_eq_iSup']

  have loc : ∀ k, ∃ (e : ℕ) (mk : Γ(G, W k)),
      resF G (Y.basicOpen_le (resO (hle k) h)) mk =
        resO (Y.basicOpen_le (resO (hle k) h)) (resO (hle k) h) ^ e •
          resF G (basicOpen_resO_le (hle k) h) m := fun k =>
    qcoh_exists_res_eq G (hUs k.2) (resO (hle k) h) (resF G (basicOpen_resO_le (hle k) h) m)
  choose e mk hmk using loc
  set N := Finset.univ.sup e
  obtain ⟨σ, hσ⟩ : ∃ σ : ∀ k, Γ(G, W k), ∀ k,
      resF G (Y.basicOpen_le (resO (hle k) h)) (σ k) =
        resO ((basicOpen_resO_le (hle k) h).trans (Y.basicOpen_le h)) h ^ N •
          resF G (basicOpen_resO_le (hle k) h) m := by
    refine ⟨fun k => resO (hle k) h ^ (N - e k) • mk k, fun k => ?_⟩
    have hk : e k ≤ N := Finset.le_sup (Finset.mem_univ k)
    rw [resF_smul, hmk, smul_smul]
    simp only [map_pow, resO_resO]
    rw [← pow_add, Nat.sub_add_cancel hk]

  have pair : ∀ k l, ∃ e' : ℕ, resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h ^ e' •
      (resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) -
        resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) = 0 := by
    intro k l
    have hkl : IsCompact ((W k ⊓ W l : Y.Opens) : Set Y) :=
      hU' _ _ (hle k) (W k).2 (hUs k.2).isCompact (hle l) (W l).2 (hUs l.2).isCompact
    refine qcoh_exists_pow_smul_eq_zero_of_isCompact G hkl _ _ ?_
    have hb : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle k) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_left
    have hb' : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle l) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_right
    rw [map_sub, resF_resF, resF_resF, sub_eq_zero,
      ← resF_resF G (Y.basicOpen_le (resO (hle k) h)) hb,
      ← resF_resF G (Y.basicOpen_le (resO (hle l) h)) hb', hσ k, hσ l, resF_smul, resF_smul,
      resF_resF, resF_resF, map_pow, map_pow, resO_resO, resO_resO]
  choose e' he' using pair
  set N' := Finset.univ.sup (fun kl : Us × Us => e' kl.1 kl.2)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ∀ k, Γ(G, W k), ∀ k, τ k = resO (hle k) h ^ N' • σ k :=
    ⟨fun k => resO (hle k) h ^ N' • σ k, fun _ => rfl⟩
  have hτ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (τ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (τ l) := by
    intro k l
    have hkl : e' k l ≤ N' := Finset.le_sup (f := fun kl : Us × Us => e' kl.1 kl.2)
      (Finset.mem_univ (k, l))
    rw [hτdef, hτdef, resF_smul, resF_smul, map_pow, map_pow, resO_resO, resO_resO, ← sub_eq_zero,
      ← smul_sub, ← Nat.sub_add_cancel hkl, pow_add, mul_smul, he' k l, smul_zero]
  obtain ⟨m', hm'⟩ := exists_resF_eq_of_compatible G W hle hcov τ hτ
  refine ⟨N' + N, m', ?_⟩

  refine eq_of_forall_resF G (fun k => Y.basicOpen (resO (hle k) h))
    (fun k => basicOpen_resO_le (hle k) h) ?_ _ _ fun k => ?_
  · intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hcov (Y.basicOpen_le h hx))
    refine Opens.mem_iSup.2 ⟨k, ?_⟩
    rw [Scheme.basicOpen_res]
    exact ⟨hk, hx⟩
  · rw [resF_resF, ← resF_resF G (hle k) (Y.basicOpen_le (resO (hle k) h)), hm', hτdef, resF_smul,
      hσ k, resF_smul, smul_smul]
    simp only [map_pow, resO_resO, ← pow_add]

theorem isQuasicoherent_pushforward_of_qcqs {X : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : Y.affineOpens => (V : Y.Opens))
    (fun V => V.2) (iSup_affineOpens_eq_top Y) ?_ ?_
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hqs : IsQuasiSeparated ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) :=
      f.isQuasiSeparated_preimage V.2.isQuasiSeparated
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ Y.basicOpen g), ∃ (e : ℕ) (m' : Γ(F, f ⁻¹ᵁ (V : Y.Opens))),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m' =
        f.app (Y.basicOpen g) (resO (Y.basicOpen_le g) g ^ e) • m
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq_of_qcqs F hc hqs (f.app V g) (resF F hb.ge m)
    refine ⟨e, m', ?_⟩
    have h2 := congrArg (resF F hb.le) hm'
    rw [resF_resF, resF_smul, resF_resF, resF_self, map_pow, resO_resO] at h2
    rw [h2, map_pow, app_resO]
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ (V : Y.Opens)),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m = 0 →
        ∃ e : ℕ, f.app V (g ^ e) • m = 0
    intro m hm
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero_of_isCompact F hc (f.app V g) m (by
      have h2 := congrArg (resF F hb.ge) hm
      rw [resF_resF, map_zero] at h2
      exact h2)
    exact ⟨e, by rw [map_pow]; exact he⟩

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

attribute [local instance] algebraOfOver

namespace ProjScheme

theorem exists_relativeSerre {A : Type u} [CommRing A] [IsNoetherianRing A] {X X' : Scheme.{u}}
    [X.Over (Spec (.of A))] [X'.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [CompactSpace X] [IsLocallyNoetherian X] {N : ℕ} (i : X' ⟶ projectiveSpace A N)
    [IsClosedImmersion i] [i.IsOver (Spec (.of A))] (ψ : X' ⟶ X) [ψ.IsOver (Spec (.of A))]
    (G : X'.Modules) (hG : IsCoherent G) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsCoherent ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)) ∧
      ∀ p : ℕ, Nonempty (Sheaf.H.{u} (modulesAb (ProjScheme.twist i G n)) p ≃ₗ[A]
        Sheaf.H.{u} (modulesAb ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n))) p) := by
  classical
  have h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) := by
    rw [CategoryTheory.comp_over ψ (Spec (.of A))]
    exact CategoryTheory.comp_over i (Spec (.of A))
  have : X.IsSeparated := ⟨by
    rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  have : QuasiCompact (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ (X ↘ Spec (.of A))
  have : QuasiSeparated (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiSeparated ψ := QuasiSeparated.of_comp ψ (X ↘ Spec (.of A))

  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun U : X.affineOpens => (U : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨U, hU⟩ := Opens.mem_iSup.1
        (show x ∈ ⨆ U : X.affineOpens, (U : X.Opens) by rw [iSup_affineOpens_eq_top X]; trivial)
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  let ι := { U // U ∈ t }
  let V : ι → X.Opens := fun a => a.1.1
  have hVaff1 : ∀ a, IsAffineOpen (V a) := fun a => a.1.2
  have hV : iSup V = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hUt, hxU⟩ := Set.mem_iUnion.1 hU
    exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

  let W : Finset ι → X.Opens := fun S => ⨅ a : S, V a
  have hWaff : ∀ S : Finset ι, S.Nonempty → IsAffineOpen (W S) := fun S hS => by
    have : Nonempty S := hS.to_subtype
    exact IsAffineOpen.iInf fun a => hVaff1 a
  have hWtuple : ∀ (m : ℕ) (s : Fin (m + 1) → ι),
      (⨅ a, V (s a)) = W (Finset.univ.image s) := fun m s => by
    apply le_antisymm
    · exact le_iInf fun b => by
        obtain ⟨a, -, ha⟩ := Finset.mem_image.1 b.2
        exact (iInf_le _ a).trans (le_of_eq (congrArg V ha))
    · exact le_iInf fun a => iInf_le (fun b : (Finset.univ.image s : Finset ι) => V b)
        ⟨s a, Finset.mem_image_of_mem s (Finset.mem_univ a)⟩
  have hWsingle : ∀ a : ι, W {a} = V a := fun a => by
    apply le_antisymm
    · exact iInf_le (fun b : ({a} : Finset ι) => V b) ⟨a, Finset.mem_singleton_self a⟩
    · exact le_iInf fun b => le_of_eq (congrArg V (Finset.mem_singleton.1 b.2).symm)

  have key : ∀ S : Finset ι, ∃ n₁ : ℕ, S.Nonempty → ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton (Sheaf.H.{u}
        (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ W S).ι)) (q + 1))) ∧
      Module.Finite Γ(X, W S) Γ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n), W S) := by
    intro S
    by_cases hS : S.Nonempty
    · have hA := hWaff S hS
      have : IsNoetherianRing Γ(X, W S) := IsLocallyNoetherian.component_noetherian ⟨_, hA⟩
      obtain ⟨n₁, hn₁⟩ := RelSerre.exists_vanishing_finite i ψ h hA G hG
      exact ⟨n₁, fun _ n hn => ⟨(hn₁ n hn).1,
        RelSerre.finite_sections_pushforward i ψ h hA _ (hn₁ n hn).2⟩⟩
    · exact ⟨0, fun h' => absurd h' hS⟩
  choose nS hnS using key
  refine ⟨Finset.univ.sup nS, fun n hn => ?_⟩
  have hle : ∀ S, nS S ≤ n := fun S => (Finset.le_sup (Finset.mem_univ S)).trans hn
  have : G.IsQuasicoherent := hG.1
  have : ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs ψ _
  refine ⟨?_, fun p => ?_⟩
  · refine isCoherent_of_affineCover _ V hVaff1 hV fun a => ?_
    have hfin := (hnS {a} (Finset.singleton_nonempty a) n (hle _)).2
    rw [hWsingle] at hfin
    exact hfin
  · have hVaff : ∀ (m : ℕ) (s : Fin (m + 1) → ι), IsAffineOpen (⨅ a, V (s a)) := fun m s =>
      IsAffineOpen.iInf fun a => hVaff1 (s a)
    refine ⟨HLinearEquivPushforwardOfAcyclic ψ A V hV hVaff (ProjScheme.twist i G n)
      (fun m s q => ?_) p⟩
    have h1 := (hnS (Finset.univ.image s) (Finset.univ_nonempty.image s) n (hle _)).1 q
    rw [← hWtuple] at h1
    exact h1

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
end
