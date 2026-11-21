import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndPullOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixPoint

theorem exists_affine_hom (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg)
    (x : Fin n → Γ(T, ⊤)) :
    ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  let φ : MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom) x
  have key : ∀ p, (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv p) = φ p := by
    intro p
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop]
    simp
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · apply ext_of_isAffine
    refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of Rg)) _ _).1 ?_
    ext r
    have n2 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n2, key]
    simp [φ]
  · intro i
    unfold coord
    rw [key]
    simp [φ]

end GlobalTheory.HomFixPoint
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineSpace_morphism_of_coordinates : ∀ (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg) (x : Fin n → Γ(T, ⊤)), ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  first | (exact @GlobalTheory.HomFixPoint.exists_affine_hom) | (exact GlobalTheory.HomFixPoint.exists_affine_hom) | (intros; apply GlobalTheory.HomFixPoint.exists_affine_hom  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem hom_to_topS_eq {Rg : Type} [CommRing Rg] {Z : Over (Sp Rg)} (f g : Z ⟶ topS Rg) : f = g := by
  haveI : IsIso (topS Rg).hom := by
    show IsIso ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id, ← Scheme.topIso_hom]
    infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w f, Over.w g]

def θOver {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A ⟶ topS Rg ⊗ A :=
  lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)

theorem θOver_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θOver A) := by
  refine ⟨⟨snd (topS Rg) A, ?_, ?_⟩⟩
  · rw [θOver, lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, θOver, lift_fst, Category.id_comp]
      exact hom_to_topS_eq _ _
    · rw [Category.assoc, θOver, lift_snd, Category.comp_id, Category.id_comp]

theorem θ_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θ A) := by
  haveI := θOver_isIso A
  have : θ A = (Over.forget _).map (θOver A) := rfl
  rw [this]
  exact (Over.forget _).map_isIso (θOver A)

theorem θ_fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ fA A = A.hom :=
  Over.w (θOver A)

theorem θ_pullback (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left)
    (p : X' ⟶ T) (t : T ⟶ Sp Rg) :
    (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
      GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  haveI := θ_isIso A
  refine ⟨fun h => ?_, θ_fA A, inferInstance⟩
  refine IsPullback.of_iso h (Iso.refl _) (asIso (θ A)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact (θ_fA A).symm
  · simp

example : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left) (p : X' ⟶ T)
    (t : T ⟶ Sp Rg), (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
    GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := θ_pullback

end GlobalTheory.HomFixUniv
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left) (p : X' ⟶ T) (t : T ⟶ Sp Rg), (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧ GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  first | (exact @GlobalTheory.HomFixUniv.θ_pullback) | (exact GlobalTheory.HomFixUniv.θ_pullback) | (intros; apply GlobalTheory.HomFixUniv.θ_pullback  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem topS_hom_ext {Rg : Type} [CommRing Rg] {Y : Over (Sp Rg)} (u v : Y ⟶ topS Rg) : u = v := by
  have hm : Mono (topS Rg).hom := by
    change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w u, Over.w v]

instance isIso_snd_left {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) :
    IsIso (snd (topS Rg) A).left := by
  have : IsIso (snd (topS Rg) A) := by
    refine ⟨⟨lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A), ?_, ?_⟩⟩
    · refine CartesianMonoidalCategory.hom_ext _ _ (topS_hom_ext _ _) ?_
      simp
    · simp
  exact (Over.forget _).map_isIso (snd (topS Rg) A)

theorem fA_flat_isProjBy_universallyClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  intro Rg _ A _ L hA hL hamp
  have hsq : IsPullback (snd (topS Rg) A).left (fA A) A.hom (𝟙 (Sp Rg)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w (snd (topS Rg) A)⟩
  obtain ⟨hproj, hsm, hpr, -⟩ :=
    GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp Rg) A L hA hL hamp Rg (𝟙 _) _ _ (fA A) hsq
  exact ⟨inferInstance, hproj, inferInstance⟩

end GlobalTheory.HomFixUniv
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  first | (exact @GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (exact GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (intros; apply GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem factors_quot_iff {P : Type} [CommRing P] (I : Ideal P) (T : Scheme.{0}) (g : T ⟶ Sp P) :
    (∃ w : T ⟶ Sp (P ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ x hx
    have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of (P ⧸ I))).inv (Ideal.Quotient.mk I x) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of P ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ g.appTop
    let ψ : CommRingCat.of (P ⧸ I) ⟶ Γ(T, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom (fun x hx => h x hx))
    refine ⟨T.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have e : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ = φ := by ext x; rfl
    rw [Category.assoc, ← Spec.map_comp, e]
    simp only [φ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

def normEq {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (j : Fin mB) : MvPolynomial (Fin (mA * mB)) Rg :=
  MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (β j)) -
    ∑ i, MvPolynomial.X (finProdFinEquiv (i, j)) *
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (α i))

theorem appTop_affπ {Rg : Type} [CommRing Rg] {N : ℕ} (a : Γ(Sp Rg, ⊤)) :
    (affπ Rg N).appTop a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv
      (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom a)) := by
  conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of Rg)).hom_inv_id_apply a]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl

theorem normal_iff {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔
      ∀ j, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (normEq α β j)) = 0 := by
  refine forall_congr' fun j => ?_
  rw [normEq, map_sub, map_sub, sub_eq_zero, map_sum, map_sum]
  simp only [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affπ, matOf, coord]

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem normal_closed : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ mA mB α β
  let I : Ideal (MvPolynomial (Fin (mA * mB)) Rg) := Ideal.span (Set.range (normEq α β))
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ I), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, fun T g => ?_⟩
  rw [factors_quot_iff, normal_iff]
  let φ : MvPolynomial (Fin (mA * mB)) Rg →+* Γ(T, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv.hom
  change (∀ j, φ (normEq α β j) = 0) ↔ ∀ x ∈ I, φ x = 0
  constructor
  · intro h x hx
    have hle : I ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    exact hle hx
  · intro h j
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.HomFixUniv
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearNormalisation_closed_subscheme : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.HomFixUniv.normal_closed) | (exact GlobalTheory.HomFixUniv.normal_closed) | (intros; apply GlobalTheory.HomFixUniv.normal_closed  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishingForms_iff_proportional_pullbacks : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔ ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  first | (exact @GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (exact GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (intros; apply GlobalTheory.HomFixUniv.formsOK_iff_exists_proport  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUnivVals

open TopologicalSpace Opposite

theorem comp_base_pt {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem glue_fn {X : Scheme.{0}} {J : Type} (W : J → X.Opens) (hc : (⊤ : X.Opens) ≤ iSup W) (a : ∀ i, Γ(X, W i))
    (h : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 X) x (W i) (a i) = gs (𝟙 X) x (W j) (a j)) :
    ∃ α : Γ(X, ⊤), ∀ i x, x ∈ W i → gs (𝟙 X) x ⊤ α = gs (𝟙 X) x (W i) (a i) := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hc a
    (fun i j => fn_ext (V := W i ⊓ W j) fun y hy =>
      (gs_res (𝟙 X) y inf_le_left hy _).trans ((h i j y hy.1 hy.2).trans (gs_res (𝟙 X) y inf_le_right hy _).symm))
  refine ⟨s, fun i x hx => ?_⟩
  exact (gs_res (𝟙 X) x (le_top : W i ≤ ⊤) hx s).symm.trans (congrArg (gs (𝟙 X) x (W i)) (hs i))

theorem vals (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))) (hL : L.IsLB) (hA : eA.IsGen) :
    ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  set S : Scheme.{0} := (𝟙_ (Over (Sp Rg))).left with hS
  set e : S ⟶ (topS Rg ⊗ A).left := eSec A ≫ θ A with he_def
  have he : e ≫ (snd (topS Rg) A).left = eSec A := by
    rw [he_def, Category.assoc, θ_snd, Category.comp_id]
  have memN : ∀ (z : S) (q : Fin 1 → L.ι), e z ∈ (LPow A L (k : ℤ) (topS Rg)).U q ↔ eSec A z ∈ L.U (q 0) := by
    intro z q
    constructor
    · intro h
      have h0 := Set.mem_iInter.1 h 0
      rw [Set.mem_preimage, ← comp_base_pt, he] at h0
      exact h0
    · intro h
      refine Set.mem_iInter.2 fun t => ?_
      rw [Subsingleton.elim t 0, Set.mem_preimage, ← comp_base_pt, he]
      exact h
  let W : L.ι → S.Opens := fun i => e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => i)
  have memW : ∀ (z : S) (i : L.ι), z ∈ W i ↔ eSec A z ∈ L.U i := by
    intro z i
    constructor
    · intro h; exact mem_pull.1 h.2
    · intro h; exact ⟨(memN z _).2 h, mem_pull.2 h⟩
  let a : ∀ i, Γ(S, W i) := fun i =>
    (S.presheaf.map (homOfLE (inf_le_left : W i ≤ e ⁻¹ᵁ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i))).op).hom ((e.app _).hom (s.f (fun _ => i))) *
      ((res (inf_le_right : W i ≤ (L.pull (eSec A)).U (fun _ => i)) (eA.s (fun _ => i)))⁻¹ ^ k).val
  have ga : ∀ i x, x ∈ W i → gs (𝟙 S) x (W i) (a i) =
      gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i)) (s.f (fun _ => i)) * ((gm (𝟙 S) x _ (eA.s (fun _ => i)))⁻¹ ^ k).val := by
    intro i x hx
    rw [gs_mul (𝟙 S) x _ hx, gs_res (𝟙 S) x _ hx, gs_pull (𝟙 S) e x _ hx.1, Category.id_comp, gs_unit (𝟙 S) x _ hx,
      map_pow, map_inv, gm_res (𝟙 S) x _ hx]

  have compat : ∀ i j x, x ∈ W i → x ∈ W j → gs (𝟙 S) x (W i) (a i) = gs (𝟙 S) x (W j) (a j) := by
    intro i j x hx hy
    have hxi := (memW x i).1 hx
    have hxj := (memW x j).1 hy
    have hx' : e x ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j) := ⟨hx.1, hy.1⟩
    have mem : (snd (topS Rg) A).left (e x) ∈ L.U i ⊓ L.U j := by
      rw [← comp_base_pt, he]; exact ⟨hxi, hxj⟩
    have hg : gm e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) ((LPow A L (k : ℤ) (topS Rg)).g (fun _ => i) (fun _ => j)) =
        (gm (eSec A) x _ (L.g i j)) ^ k := by
      show gm e x _ (∏ _t : Fin 1, (res _ (pullU (snd (topS Rg) A).left _ (L.g i j))) ^ (k : ℤ)) = _
      rw [Fintype.prod_unique, map_zpow]
      erw [gm_res e x _ hx']
      rw [gm_pull e _ x _ mem, he, zpow_natCast]
    have hs := congrArg (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => i) ⊓ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => j))) (s.compat (fun _ => i) (fun _ => j))
    rw [gs_res e x _ hx', gs_mul e x _ hx', gs_res e x _ hx', gs_unit e x _ hx', hg] at hs
    have hp : x ∈ (L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j) := ⟨hx.2, hy.2⟩
    have mem' : (eSec A) ((𝟙 S : S ⟶ S) x) ∈ L.U i ⊓ L.U j := ⟨hxi, hxj⟩
    have hg' : gm (𝟙 S) x _ ((L.pull (eSec A)).g (fun _ => i) (fun _ => j)) = gm (eSec A) x _ (L.g i j) := by
      show gm (𝟙 S) x _ (∏ _t : PUnit, (res _ (pullU (eSec A) _ (L.g i j))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      erw [gm_res (𝟙 S) x _ hp]
      rw [gm_pull (𝟙 S) (eSec A) x _ mem', Category.id_comp]
    have hA' := congrArg (gm (𝟙 S) x ((L.pull (eSec A)).U (fun _ => i) ⊓ (L.pull (eSec A)).U (fun _ => j)))
      (hA (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ x _ hp, gm_res _ x _ hp, hg'] at hA'
    rw [ga i x hx, ga j x hy, hs, hA']
    set u := gm (eSec A) x _ (L.g i j)
    set B := gm (𝟙 S) x _ (eA.s (fun _ => j))
    have hinv : (u * B)⁻¹ ^ k = (u ^ k)⁻¹ * B⁻¹ ^ k := by rw [mul_inv, mul_pow, inv_pow]
    have hU : (u ^ k).val * ((u ^ k)⁻¹).val = 1 := Units.mul_inv _
    rw [hinv, Units.val_mul]
    linear_combination (gs e x ((LPow A L (k : ℤ) (topS Rg)).U (fun _ => j)) (s.f (fun _ => j)) * (B⁻¹ ^ k).val) * hU
  obtain ⟨α, hα⟩ := glue_fn W (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (eSec A x)
      exact Opens.mem_iSup.2 ⟨i, (memW x i).2 hi⟩) a compat
  refine ⟨α, fun z q hz => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, q = fun _ => i := ⟨q 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
  have hzW : z ∈ W i := (memW z i).2 ((memN z _).1 hz)
  rw [hα i z hzW, ga i z hzW]
  show _ = _ * ((gm (𝟙 S) z _ (eA.s fun _ => i)) ^ k).val
  rw [_root_.mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.HomFixUnivVals
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeroSection_value_in_powerFrame : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))), L.IsLB → eA.IsGen → ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  first | (exact @GlobalTheory.HomFixUnivVals.vals) | (exact GlobalTheory.HomFixUnivVals.vals) | (intros; apply GlobalTheory.HomFixUnivVals.vals  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixTrivLocus

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem isoLocus_closed : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  intro Rg _ A B _ _ L M eA eB Z₁ _ t₁ A₁ B₁ _ _ φA₁ φB₁ Φ₁ hA hB hL hM hgA hgB hamp hpA hpB hΦ
  haveI : IsMonHom Φ₁ := hΦ
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj A₁ := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A₁ t₁ φA₁ hpA
  obtain ⟨hA₁, hL₁, hrA₁, haA₁⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ t₁ A A₁ φA₁ L
    hpA hA hL ⟨eA, hgA⟩ hamp
  have hrB₁ : Out.Rigidified B₁ (M.pull φB₁) := GlobalTheory.PolBaseChange.rigidified_pull hpB ⟨eB, hgB⟩
  have hM₁ : (M.pull (Φ₁.left ≫ φB₁)).IsLB := pull_isLB hM _
  have hN : (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)).IsLB := LB.isLB_div hM₁ hL₁
  have hrN : Out.Rigidified A₁ (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)) := by
    refine (GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) (eSec A₁)).1 ?_
    obtain ⟨s, hs⟩ := hrA₁
    obtain ⟨t, ht⟩ := hrB₁
    have e1 : LBIso ((L.pull φA₁).pull (eSec A₁)) ((M.pull φB₁).pull (eSec B₁)) :=
      GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    have hc : eSec A₁ ≫ Φ₁.left = eSec B₁ := congrArg (fun z => z.left) (IsMonHom.one_hom Φ₁)
    have e2 : LBIso ((M.pull φB₁).pull (eSec B₁)) ((M.pull (Φ₁.left ≫ φB₁)).pull (eSec A₁)) :=
      GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc])
    exact LBIso.trans (pull_isLB hL₁ _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM₁ _) e1 e2
  obtain ⟨Z, i, hi, H⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw Z₁ A₁ (L.pull φA₁) (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁))
    hA₁ hL₁ haA₁ hN hrN
  refine ⟨Z, i, hi, fun T u A' B' _ _ ψA ψB Φ' hpA' hpB' hc => ?_⟩
  refine Iff.trans ?_ ((GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) ψA).trans
    (H T u A' ψA hpA'))
  have a1 : LBIso (L.pull (ψA ≫ φA₁)) ((L.pull φA₁).pull ψA) := lbIso_pull_comp' hL φA₁ ψA
  have a2 : LBIso ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ((M.pull (Φ₁.left ≫ φB₁)).pull ψA) :=
    GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc, Category.assoc])
  have h1 := pull_isLB hL (ψA ≫ φA₁)
  have h2 := pull_isLB hL₁ ψA
  have h3 := pull_isLB (pull_isLB hM (ψB ≫ φB₁)) Φ'.left
  have h4 := pull_isLB hM₁ ψA
  exact ⟨fun h => GlobalTheory.HomFixTransport.lbIso_congr h1 h2 h3 h4 (LBIso.symm a1) h a2,
    fun h => GlobalTheory.HomFixTransport.lbIso_congr h2 h1 h4 h3 a1 h (LBIso.symm a2)⟩

end GlobalTheory.HomFixTrivLocus
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  first | (exact @GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (exact GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (intros; apply GlobalTheory.HomFixTrivLocus.isoLocus_closed  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixMat.exists_immersed_locus : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  intro Y _ Z₁ Z₂ ι₁ ι₂ U h₁ h₂
  let p : pullback ι₁ ι₂ ⟶ Y := pullback.fst ι₁ ι₂ ≫ ι₁
  let V : (pullback ι₁ ι₂).Opens := p ⁻¹ᵁ U
  let j : V.toScheme ⟶ Y := V.ι ≫ p
  have hj : IsImmersion j := IsImmersion.comp _ _
  have hW : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian j
  have hN : TopologicalSpace.NoetherianSpace V.toScheme :=
    (IsPreimmersion.isEmbedding j).isInducing.noetherianSpace
  refine ⟨V.toScheme, j, hj, quasiCompact_of_noetherianSpace_source j, hW, ?_⟩
  intro T g
  constructor
  · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, hU⟩
    let f : T ⟶ pullback ι₁ ι₂ := pullback.lift w₁ w₂ (hw₁.trans hw₂.symm)
    have hf : f ≫ p = g := by
      simp only [f, p]; rw [← Category.assoc, pullback.lift_fst]; exact hw₁
    have hr : Set.range f ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      show p (f τ) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact hU τ
    refine ⟨IsOpenImmersion.lift V.ι f hr, ?_⟩
    simp only [j, ← Category.assoc, IsOpenImmersion.lift_fac, hf]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨w ≫ V.ι ≫ pullback.fst ι₁ ι₂, by simp [j, p]⟩,
      ⟨w ≫ V.ι ≫ pullback.snd ι₁ ι₂, by simp [j, p, pullback.condition]⟩, ?_⟩
    intro τ
    have : V.ι (w τ) ∈ V := by
      have h := Scheme.Opens.range_ι V
      exact (Set.ext_iff.mp h (V.ι (w τ))).mp ⟨_, rfl⟩
    exact this
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_immersed_closed_open_intersection : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  first | (exact @GlobalTheory.HomFixMat.exists_immersed_locus) | (exact GlobalTheory.HomFixMat.exists_immersed_locus) | (intros; apply GlobalTheory.HomFixMat.exists_immersed_locus  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixUniv

variable {mA mB : ℕ}

theorem comb_comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) (z : X₂)
    (q : N.ι) (hq : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ : gs p₂ z ⊤ (h.appTop (c i j)) = gs (r ≫ p) z ⊤ (c i j) := by
    rw [← e]; exact gs_pull p₂ h z ⊤ trivial (c i j)
  rw [e₁, gs_comp r p z ⊤ trivial, gs_comp r φ z _ hq]

theorem Generates.comp {A₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hg : Generates a φ p c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂)
    (e : p₂ ≫ h = r ≫ p) : Generates a (r ≫ φ) p₂ (fun i j => h.appTop (c i j)) := by
  intro z q hq
  obtain ⟨j, hj⟩ := hg (r z) q hq
  exact ⟨j, by rw [comb_comp a φ p c r h p₂ e z q hq j]; exact hj.map _⟩

theorem Proport.comp {A₀ B₀ X X₂ T T₂ : Scheme.{0}} {N : LB A₀} {H : LB B₀} {a : Fin mA → LB.Sec N}
    {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hp : Proport a b φ p Ψ c) (r : X₂ ⟶ X) (h : T₂ ⟶ T) (p₂ : X₂ ⟶ T₂) (e : p₂ ≫ h = r ≫ p) :
    Proport a b (r ≫ φ) p₂ (r ≫ Ψ) (fun i j => h.appTop (c i j)) := by
  intro z q k hq hk j j'
  rw [comb_comp a φ p c r h p₂ e z q hq, comb_comp a φ p c r h p₂ e z q hq, gs_comp r Ψ z _ hk,
    gs_comp r Ψ z _ hk, ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem matOf_comp {Rg : Type} [CommRing Rg] {X X' : Scheme.{0}} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) : matOf (h ≫ g) = fun i j => h.appTop (matOf g i j) := by
  funext i j; exact coord_comp h g _

theorem relift {S T' T : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over T} [GrpObj G₁] {G' : Over T'} [GrpObj G']
    {t₁ : T ⟶ S} {u : T' ⟶ T} {φ₁ : G₁.left ⟶ G.left} {φ' : G'.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G t₁ φ₁)
    (h' : IsGrpPullback G' G (u ≫ t₁) φ') : ∃ ψ : G'.left ⟶ G₁.left, IsGrpPullback G' G₁ u ψ ∧ ψ ≫ φ₁ = φ' := by
  refine ⟨h₁.1.lift φ' (G'.hom ≫ u) (by rw [h'.1.w, Category.assoc]), ?_, h₁.1.lift_fst _ _ _⟩
  exact h₁.cancel (by rw [h₁.1.lift_fst]; exact h') (h₁.1.lift_snd _ _ _)

theorem exists_universal_matrix : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∃ (X : Scheme.{0}) (cE : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (H : Scheme.{0}) (i : H ⟶ X) (AH : Over H) (_ : GrpObj AH) (BH : Over H) (_ : GrpObj BH) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH), IsClosedImmersion cE ∧ IsOpenImmersion i ∧ IsTest A B L M (i ≫ cE ≫ affπ Rg (mA * mB)) AH BH φA φB Φ ∧ (∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ h : Sp R ⟶ H, h ≫ i ≫ cE ≫ affπ Rg (mA * mB) = t ∧ matOf (h ≫ i ≫ cE) = c) ∧ ∀ (R : Type) [CommRing R] (h : Sp R ⟶ H) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' → IsPullD φA φB Φ φA' φB' Φ' h → IsMat L M k bA bB eA eB (h ≫ i ≫ cE ≫ affπ Rg (mA * mB)) A' B' φA' φB' Φ' (matOf (h ≫ i ≫ cE)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH
  obtain ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ := hH
  obtain ⟨hfl, hpj, huc⟩ := GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed Rg A L hAb hL hamp
  haveI := huc
  have hEmb := GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hBb hM hk hva hbB
  have hcov : (⨆ j, nonzeroLocus (bB j)) = ⊤ := hEmb.1
  have hNA : (LPow A L (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hL _ _
  have hNB : (LPow B M (k : ℤ) (topS Rg)).IsLB := LB.isLB_linComb hM _ _
  choose αA hαA using fun i => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg A L k eA (bA i) hL heA
  choose βB hβB using fun j => GlobalTheory.T.exists_zeroSection_value_in_powerFrame Rg B M k eB (bB j) hM heB
  obtain ⟨U, hU⟩ := GlobalTheory.T.isOpen_generatingCombinationMatrixLocus Rg _ (fA A) _ mA mB bA hNA
  obtain ⟨ZF, ιF, hιF, hF⟩ := GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections Rg _ _ (fA A) (fA B) _ _ mA mB bA bB hfl hpj hNA
  obtain ⟨ZN, ιN, hιN, hNm⟩ := GlobalTheory.T.linearNormalisation_closed_subscheme Rg mA mB αA βB
  haveI : IsNoetherian (Sp (MvPolynomial (Fin (mA * mB)) Rg)) := isNoetherian_Spec.2 inferInstance
  obtain ⟨W, j₁, hj₁, hj₁q, hWn, hW⟩ := GlobalTheory.T.exists_immersed_closed_open_intersection _ ZF ZN ιF ιN U hιF hιN
  have cond : ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ (topS Rg ⊗ A).left)
      (p : X' ⟶ T), (∃ w, w ≫ j₁ = g) → IsPullback φ p (fA A) (g ≫ affπ Rg (mA * mB)) →
      Generates bA φ p (matOf g) ∧ FormsOK bA (fA B) bB φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ∧
        Normal (g ≫ affπ Rg (mA * mB)) (matOf g) αA βB := by
    intro T X' g φ p hg hP
    obtain ⟨h1, h2, h3⟩ := (hW T g).2 hg
    exact ⟨(hU T X' g φ p hP).2 h3, (hF T X' g φ p hP).2 h1, (hNm T g).2 h2⟩
  have datum : ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (∃ w, w ≫ j₁ = g) →
      ∃ (AT : Over T) (_ : GrpObj AT) (BT : Over T) (_ : GrpObj BT) (φA : AT.left ⟶ A.left) (φB : BT.left ⟶ B.left)
        (Φ : AT ⟶ BT), IsGrpPullback AT A (g ≫ affπ Rg (mA * mB)) φA ∧
        IsGrpPullback BT B (g ≫ affπ Rg (mA * mB)) φB ∧ IsMonHom Φ ∧ Generates bA (φA ≫ θ A) AT.hom (matOf g) ∧
        Proport bA bB (φA ≫ θ A) AT.hom (Φ.left ≫ φB ≫ θ B) (matOf g) := by
    intro T g hg
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (g ≫ affπ Rg (mA * mB))).obj B) := Functor.grpObjObj
    have pA := isGrpPullback_pullback A (g ≫ affπ Rg (mA * mB))
    have pB := isGrpPullback_pullback B (g ≫ affπ Rg (mA * mB))
    have hP := (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A T _ _ _ (g ≫ affπ Rg (mA * mB))).1 pA.1
    obtain ⟨c1, c2, c3⟩ := cond T _ g _ _ hg hP
    obtain ⟨Ψ, hΨ, hpr⟩ := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ T (fA A) (fA B) _ _ mA mB bA bB _ _ _ (matOf g) hEmb hNB hNA hP.w
      c1).1 c2
    obtain ⟨Φ, hΦ, hΦΨ⟩ := GlobalTheory.T.grpHom_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB T _ _ _ _ _ Ψ (matOf g)
      ⟨hAb, hBb, hL, hM, heA, heB, hamp, hk, hva, hbA, hbB⟩ hαA hβB pA pB hΨ c1 hpr c3
    exact ⟨_, inferInstance, _, inferInstance, _, _, Φ, pA, pB, hΦ, c1, by rw [hΦΨ]; exact hpr⟩
  have θf : ∀ C : Over (Sp Rg), θ C ≫ fA C = C.hom := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.1
  have θi : ∀ C : Over (Sp Rg), IsIso (θ C) := fun C => (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg C C.left C.left (𝟙 _) (𝟙 _) C.hom).2.2
  obtain ⟨A₁, iA₁, B₁, iB₁, φA₁, φB₁, Φ₁, pA₁, pB₁, hΦ₁, hg₁, hp₁⟩ := datum W j₁ ⟨𝟙 _, Category.id_comp _⟩
  haveI := hWn
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic Rg A B L M eA eB W (j₁ ≫ affπ Rg (mA * mB)) A₁ B₁ φA₁ φB₁ Φ₁ hAb hBb hL hM heA heB
    hamp pA₁ pB₁ hΦ₁
  have compare : ∀ (T : Scheme.{0}) (u : T ⟶ W) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φA' →
      IsGrpPullback B' B ((u ≫ j₁) ≫ affπ Rg (mA * mB)) φB' →
      Generates bA (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) →
      Proport bA bB (φA' ≫ θ A) A'.hom (Φ'.left ≫ φB' ≫ θ B) (matOf (u ≫ j₁)) →
      ∃ (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left), IsGrpPullback A' A₁ u ψA ∧ IsGrpPullback B' B₁ u ψB ∧
        ψA ≫ φA₁ = φA' ∧ ψB ≫ φB₁ = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ₁.left := by
    intro T u A' B' _ _ φA' φB' Φ' hA' hB' hgen hprop
    rw [Category.assoc] at hA' hB'
    obtain ⟨ψA, hψA, eA'⟩ := relift pA₁ hA'
    obtain ⟨ψB, hψB, eB'⟩ := relift pB₁ hB'
    refine ⟨ψA, ψB, hψA, hψB, eA', eB', ?_⟩
    apply pB₁.1.hom_ext
    · rw [Category.assoc, eB', Category.assoc, ← cancel_mono (θ B), Category.assoc, Category.assoc, Category.assoc]
      have hp := hp₁.comp ψA u A'.hom hψA.1.w.symm
      rw [← matOf_comp, ← Category.assoc ψA φA₁, eA'] at hp
      refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ _ T (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (matOf (u ≫ j₁)) _ _ hEmb hNB hNA hgen
        hprop hp ?_
      simp only [Category.assoc, θf]
      rw [hB'.1.w, pB₁.1.w, reassoc_of% (Over.w Φ'), reassoc_of% (Over.w Φ₁), reassoc_of% hψA.1.w]
    · rw [Category.assoc, hψB.1.w, reassoc_of% (Over.w Φ'), Category.assoc, Over.w Φ₁, hψA.1.w]
  obtain ⟨AH, iAH, BH, iBH, φAH, φBH, ΦH, pAH, pBH, hΦH, hgH, hpH⟩ := datum Z (i ≫ j₁) ⟨i, rfl⟩
  obtain ⟨ψA, ψB, hψA, hψB, eψA, eψB, eΦ⟩ := compare Z i AH BH φAH φBH ΦH pAH pBH hgH hpH
  have hlb : LBIso (L.pull φAH) ((M.pull φBH).pull ΦH.left) := by
    have := (hZ Z i AH BH ψA ψB ΦH hψA hψB eΦ).2 ⟨𝟙 _, Category.id_comp _⟩
    rwa [eψA, eψB] at this
  refine ⟨(i ≫ j₁).image, (i ≫ j₁).imageι, Z, (i ≫ j₁).toImage, AH, iAH, BH, iBH, φAH, φBH, ΦH, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.toImage_imageι_assoc]
    exact ⟨pAH, pBH, hΦH, hlb⟩
  · intro R _ t A' B' _ _ φA' φB' Φ' c hT hMat
    obtain ⟨g, hgt, hgc⟩ := GlobalTheory.T.exists_affineSpace_morphism_of_coordinates Rg (Sp R) (mA * mB) t
      (fun n => c (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2)
    have hgm : matOf g = c := by funext a b; simp [matOf, hgc]
    obtain ⟨hgen, hprop, hnorm⟩ := GlobalTheory.T.testHom_matrix_generates_normalised Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c hL hM
      hcov hαA hβB hT hMat
    rw [← hgm] at hgen hprop
    rw [← hgm, ← hgt] at hnorm
    have hP : IsPullback (φA' ≫ θ A) A'.hom (fA A) (g ≫ affπ Rg (mA * mB)) := by
      rw [hgt]; exact (GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso Rg A _ _ _ _ t).1 hT.1.1
    have hbase : (Φ'.left ≫ φB' ≫ θ B) ≫ fA B = A'.hom ≫ g ≫ affπ Rg (mA * mB) := by
      rw [hgt, Category.assoc, Category.assoc, θf, hT.2.1.1.w, reassoc_of% (Over.w Φ')]
    have hforms := (GlobalTheory.T.vanishingForms_iff_proportional_pullbacks Rg _ _ _ _ (fA A) (fA B) _ _ mA mB bA bB (φA' ≫ θ A) A'.hom (g ≫ affπ Rg _) (matOf g)
      hEmb hNB hNA hP.w hgen).2 ⟨_, hbase, hprop⟩
    obtain ⟨w₁, hw₁⟩ := (hW _ g).1 ⟨(hF _ _ g _ _ hP).1 hforms, (hNm _ g).1 hnorm, (hU _ _ g _ _ hP).1 hgen⟩
    have hA' : IsGrpPullback A' A ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φA' := by rw [hw₁, hgt]; exact hT.1
    have hB' : IsGrpPullback B' B ((w₁ ≫ j₁) ≫ affπ Rg (mA * mB)) φB' := by rw [hw₁, hgt]; exact hT.2.1
    obtain ⟨ψA', ψB', hψA', hψB', eψA', eψB', eΦ'⟩ := compare _ w₁ A' B' φA' φB' Φ' hA' hB'
      (by rw [hw₁]; exact hgen) (by rw [hw₁]; exact hprop)
    have hlb' := hT.2.2.2
    rw [← eψA', ← eψB'] at hlb'
    obtain ⟨w₂, hw₂⟩ := (hZ _ w₁ A' B' ψA' ψB' Φ' hψA' hψB' eΦ').1 hlb'
    refine ⟨w₂, ?_, ?_⟩
    · rw [Scheme.Hom.toImage_imageι_assoc, ← Category.assoc, ← Category.assoc, hw₂, hw₁, hgt]
    · rw [Scheme.Hom.toImage_imageι, ← Category.assoc, hw₂, hw₁, hgm]
  · intro R _ h A' B' _ _ φA' φB' Φ' hT hD
    obtain ⟨ψA', ψB', qA, qB, eA', eB', eΦ'⟩ := hD
    simp only [Scheme.Hom.toImage_imageι_assoc, Scheme.Hom.toImage_imageι] at hT ⊢
    have e₀ : A'.hom ≫ h = ψA' ≫ AH.hom := qA.1.w.symm
    have keyA : ψA' ≫ φAH ≫ θ A = φA' ≫ θ A := by rw [← eA', Category.assoc]
    have keyB : ψA' ≫ ΦH.left ≫ φBH ≫ θ B = Φ'.left ≫ φB' ≫ θ B := by
      rw [← eB']; simp only [Category.assoc]; rw [reassoc_of% eΦ']
    have hgen := hgH.comp ψA' h A'.hom e₀
    rw [keyA, ← matOf_comp] at hgen
    have hpr := hpH.comp ψA' h A'.hom e₀
    rw [keyA, keyB, ← matOf_comp] at hpr
    have hnorm : Normal ((h ≫ i ≫ j₁) ≫ affπ Rg (mA * mB)) (matOf (h ≫ i ≫ j₁)) αA βB :=
      (hNm _ _).2 ((hW _ _).2 ⟨h ≫ i, Category.assoc _ _ _⟩).2.1
    simp only [Category.assoc] at hT hnorm hgen hpr ⊢
    exact GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations Rg A B L M k mA mB bA bB eA eB αA βB R _ A' B' φA' φB' Φ' _ hL hM heA heB hcov hαA hβB hT
      hgen hpr hnorm

end GlobalTheory.HomFixUniv
end
end
