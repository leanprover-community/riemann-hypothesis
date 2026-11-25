module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem imageIdealSheaf_eq_comap_inv {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    _root_.FunctorialResolution.Blowup.schemeImageIdeal f J = J.comap (inv f) := by
  rw [imageIdealSheaf_eq_ker]
  symm
  rw [Scheme.IdealSheafData.comap,
    ← Scheme.Hom.ker_comp_of_isIso (inv (Limits.pullback.snd (inv f) J.subschemeι)),
    Limits.pullback_inv_snd_fst_of_left_isIso, IsIso.inv_inv]

theorem imageIdealSheaf_comap {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    _root_.FunctorialResolution.Blowup.schemeImageIdeal f (I.comap f) = I := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

theorem comap_imageIdealSheaf {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    (_root_.FunctorialResolution.Blowup.schemeImageIdeal f J).comap f = J := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

theorem ker_comp_eq_imageIdealSheaf_ker {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) :
    (g ≫ w).ker = _root_.FunctorialResolution.Blowup.schemeImageIdeal w g.ker := by
  rw [imageIdealSheaf_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_comp,
    AlgebraicGeometry.Scheme.Hom.ker_comp, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

theorem imageIdealSheaf_comp_comap_of_isIso {A B C : Scheme.{u}} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : B.IdealSheafData) :
    _root_.FunctorialResolution.Blowup.schemeImageIdeal (w ≫ g) (I.comap w) = _root_.FunctorialResolution.Blowup.schemeImageIdeal g I := by
  let θ := I.comapIso w ≪≫ asIso (Limits.pullback.snd w I.subschemeι)
  have hθ : θ.hom ≫ I.subschemeι = (I.comap w).subschemeι ≫ w := by
    dsimp only [θ]
    rw [Iso.trans_hom, asIso_hom, Scheme.IdealSheafData.comapIso_hom_snd,
      Scheme.IdealSheafData.subschemeMap_subschemeι]
  rw [imageIdealSheaf_eq_ker (w ≫ g) (I.comap w), imageIdealSheaf_eq_ker g I, ← Category.assoc, ← hθ,
    Category.assoc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

theorem imageIdealSheaf_strictTransform_of_comm_sq {X X₁ Y Y₁ : Scheme.{u}}
    (φ : X₁ ⟶ X) (ψ : Y₁ ⟶ Y) (u : X ⟶ Y) (u₁ : X₁ ⟶ Y₁) [IsIso u] [IsIso u₁]
    (hsq : u₁ ≫ ψ = φ ≫ u) (Z D : X.IdealSheafData) :
    _root_.FunctorialResolution.Blowup.schemeImageIdeal u₁ (Blowup.strictTransform φ Z D)
      = Blowup.strictTransform ψ (_root_.FunctorialResolution.Blowup.schemeImageIdeal u Z) (_root_.FunctorialResolution.Blowup.schemeImageIdeal u D) := by
  have hψ : ψ = inv u₁ ≫ φ ≫ u := by
    rw [← hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hmaps : ψ ≫ inv u = inv u₁ ≫ φ := by
    rw [hψ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcm : ∀ I : X.IdealSheafData,
      (_root_.FunctorialResolution.Blowup.schemeImageIdeal u I).comap ψ = (I.comap φ).comap (inv u₁) := by
    intro I
    rw [imageIdealSheaf_eq_comap_inv,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hmaps]
  let θ := (D.comap φ).comapIso (inv u₁) ≪≫
    asIso (Limits.pullback.snd (inv u₁) (D.comap φ).subschemeι)
  have hθ : θ.hom ≫ (D.comap φ).subschemeι =
      ((D.comap φ).comap (inv u₁)).subschemeι ≫ inv u₁ := by
    dsimp only [θ]
    rw [Iso.trans_hom, asIso_hom, Scheme.IdealSheafData.comapIso_hom_snd,
      Scheme.IdealSheafData.subschemeMap_subschemeι]
  have hVV' : ((D.comap φ).comap (inv u₁)).subschemeι ⁻¹ᵁ
        ((Z.comap φ).comap (inv u₁)).support.compl
      = θ.hom ⁻¹ᵁ ((D.comap φ).subschemeι ⁻¹ᵁ (Z.comap φ).support.compl) := by
    rw [← Scheme.Hom.comp_preimage, hθ, Scheme.Hom.comp_preimage]
    ext x
    simp [Scheme.IdealSheafData.support_comap]
  let c := ((D.comap φ).comap (inv u₁)).subscheme.isoOfEq hVV' ≪≫
    asIso (θ.hom ∣_ ((D.comap φ).subschemeι ⁻¹ᵁ (Z.comap φ).support.compl))
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq,
    hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker, ← Scheme.Hom.ker_comp_of_isIso c.hom]
  congr 1
  simp only [c, Iso.trans_hom, asIso_hom, Category.assoc, morphismRestrict_ι_assoc,
    Scheme.isoOfEq_hom_ι_assoc, reassoc_of% hθ, IsIso.inv_hom_id, Category.comp_id]

namespace IsPushforwardBlowupSeq

theorem of_isomorphic {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  obtain ⟨hlen2, e, he0, hestep, hecent⟩ := he
  have hestep' : ∀ (i : ℕ) (hp : i + 1 ≤ B.length) (hq : i ≤ B.length),
      (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hq).hom :=
    fun i hp _ => hestep i hp
  have hecent' : ∀ (i : ℕ) (hp : i < B.length) (hq : i ≤ B.length),
      (B'.center i).comap (e i hq).hom = B.center i := fun i hp _ => hecent i hp
  refine ⟨by omega, fun i hi => σ i hi ≫ (e i (by omega)).hom, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hci i hi
    infer_instance
  · have hgoal : (σ 0 (Nat.zero_le _) ≫ (e 0 (Nat.zero_le _)).hom) ≫ B'.isoZero.hom
        = BS.isoZero.hom ≫ j := by
      rw [Category.assoc, he0, h0]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom) ≫ B'.transitionMapSucc i
        = BS.transitionMapSucc i ≫ (σ i hi.le ≫ (e i hiB.le).hom) := by
      rw [Category.assoc, hestep' i hiB hiB.le, ← Category.assoc, hstep i hi, Category.assoc]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : _root_.FunctorialResolution.Blowup.schemeImageIdeal (σ i hi.le ≫ (e i hiB.le).hom) (BS.center i) = B'.center i := by
      rw [imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le,
        imageIdealSheaf_comap]
    exact hgoal.symm
  · intro i hi
    have hiB : i < B.length := by omega
    have hcen : _root_.FunctorialResolution.Blowup.schemeImageIdeal (e i hiB.le).hom (B.center i) = B'.center i := by
      rw [← hecent' i hiB hiB.le, imageIdealSheaf_comap]
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom).ker
        = Blowup.strictTransform (B'.transitionMapSucc i) (B'.center i)
            ((σ i hi.le ≫ (e i hiB.le).hom).ker) := by
      rw [ker_comp_eq_imageIdealSheaf_ker, hker i hi,
        imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i)
          (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i)
          ((σ i hi.le).ker),
        hcen, ker_comp_eq_imageIdealSheaf_ker]
    exact hgoal

theorem isIso_comp {S' S X : Scheme.{u}} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by
  obtain ⟨hlen2, τ, hτ0, hτsq, hτcent⟩ := hpb
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  have hτ0' : ∀ hp : (0 : ℕ) ≤ BS'.length,
      τ 0 hp ≫ BS.isoZero.hom = BS'.isoZero.hom ≫ e := fun _ => hτ0
  have hiso : ∀ (i : ℕ) (hi : i ≤ BS'.length), IsIso (τ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hzz : τ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv := by
          rw [← Category.assoc, ← hτ0' hi]
          simp
        rw [hzz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < BS'.length := by omega
        have := ih (by omega)
        exact (hτsq n hn).isIso_fst_of_isIso
  refine ⟨by omega, fun i hi => τ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    have := hci i (by omega)
    infer_instance
  · have hgoal : (τ 0 (Nat.zero_le _) ≫ σ 0 (Nat.zero_le _)) ≫ B.isoZero.hom
        = BS'.isoZero.hom ≫ j' := by
      rw [hj, Category.assoc, h0, ← Category.assoc, hτ0, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i
        = BS'.transitionMapSucc i ≫ (τ i hi.le ≫ σ i hiS.le) := by
      rw [Category.assoc, hstep i hiS, ← Category.assoc, (hτsq i hi).w, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso i hi.le
    have hgoal : _root_.FunctorialResolution.Blowup.schemeImageIdeal (τ i hi.le ≫ σ i hiS.le) (BS'.center i) = B.center i := by
      rw [hτcent i hi, hcent i hiS]
      exact imageIdealSheaf_comp_comap_of_isIso (τ i hi.le) (σ i hiS.le) (BS.center i)
    exact hgoal.symm
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso (i + 1) hi
    have := hiso i hi.le
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS).ker
        = Blowup.strictTransform (B.transitionMapSucc i) (B.center i) ((τ i hi.le ≫ σ i hiS.le).ker) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso,
        AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
      exact hker i hiS
    exact hgoal

theorem of_length_eq_zero {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := fun i hi => by omega
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
