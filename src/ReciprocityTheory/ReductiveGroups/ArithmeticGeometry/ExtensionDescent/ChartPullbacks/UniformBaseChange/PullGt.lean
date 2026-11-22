module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf

open Semi Geo.Tor

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)

variable {φ hφ e}

section MonHom

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

lemma isMonHom_of_grpPullback {G B : Over S} [GrpObj G] [GrpObj B] {G' B' : Over S'} [GrpObj G']
    [GrpObj B'] {φG : G'.left ⟶ G.left} {φB : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φG)
    (hB : IsGrpPullback B' B f φB) (q : G ⟶ B) [IsMonHom q] (q' : G' ⟶ B')
    (hq : q'.left ≫ φB = φG ≫ q.left) : IsMonHom q' := by
  have mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ q' = (x ≫ q') * (y ≫ q') := by
    intro T x y
    have hx : (pushPt hG.1.w x ≫ q).left = (x ≫ q').left ≫ φB := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hq]; rfl
    have hy : (pushPt hG.1.w y ≫ q).left = (y ≫ q').left ≫ φB := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hq]; rfl
    have e2 := hB.2 T (x ≫ q') (y ≫ q') (pushPt hG.1.w x ≫ q) (pushPt hG.1.w y ≫ q) hx hy
    have e1 := hG.2 T x y (pushPt hG.1.w x) (pushPt hG.1.w y) rfl rfl
    apply Over.OverMorphism.ext
    apply hB.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hq, ← Category.assoc, ← e1, ← Over.comp_left,
        MonObj.mul_comp, e2]
    · rw [Over.w, Over.w]
  refine ⟨?_, ?_⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G') ≫ q' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

end MonHom

section Q

variable (hφ e)
variable {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom]
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom]

variable {e} (g : GtCoord I D e G)

end Q

section Torus

variable (hφ e) {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ X)

instance specψ_hom : IsMonHom (specψ xe) :=
  ((bialgSpec ZU).map (CommBialgCat.ofHom (ψB xe)).op).isMonHom_hom

instance : IsIso (specψ xe).left := by
  rw [specψ_left]
  have : IsIso (CommRingCat.ofHom (ψR xe)) :=
    ⟨⟨CommRingCat.ofHom (ψR xe.symm), by
      rw [← CommRingCat.ofHom_comp, ψB_right_inv]; rfl, by
      rw [← CommRingCat.ofHom_comp, ψB_left_inv]; rfl⟩⟩
  exact (inferInstance : IsIso (Scheme.Spec.map (CommRingCat.ofHom (ψR xe)).op))

instance : IsMonHom (eψ xe).hom := by rw [eψ_hom]; infer_instance

end Torus

section Unit

lemma toUnit_left' {S : Scheme.{0}} (Z : Over S) : (toUnit Z).left = Z.hom := by
  first
  | rfl
  | (have h := Over.w (toUnit Z); simpa using h)

lemma IsGrpPullback.one_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) :
    η[G'].left ≫ φ = f ≫ η[G].left := by
  have h := hG.2 (𝟙_ _) 1 1 (pushPt hG.1.w 1) (pushPt hG.1.w 1) rfl rfl
  rw [_root_.mul_one] at h
  have h3 : pushPt hG.1.w (1 : 𝟙_ (Over S') ⟶ G') * pushPt hG.1.w 1 = pushPt hG.1.w 1 :=
    Over.OverMorphism.ext h
  have h2 := congrArg Over.Hom.left (mul_eq_left.1 h3)
  simp only [pushPt, Over.homMk_left, Hom.one_def, Over.comp_left, toUnit_left'] at h2
  simpa using h2

end Unit

section IK

variable (hφ) {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom] (xe : D'.X ≃+ D.X)
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom] {e : ℕ} (g : GtCoord I D e G)

end IK

end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
