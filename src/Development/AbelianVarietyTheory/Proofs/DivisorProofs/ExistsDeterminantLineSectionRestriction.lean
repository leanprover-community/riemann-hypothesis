import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem isCombination_pull_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x : Sp R ⟶ S') (y : Sp R ⟶ S)
    (hy : y = x ≫ f) {n : ℕ} (a : Fin n → R) (V : Fin n → (Sp (DualNumber R) ⟶ G'.left))
    (hV : ∀ k, V k ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (U : Fin n → (Sp (DualNumber R) ⟶ G.left)) (hU : ∀ k, V k ≫ φ = U k)
    (w : FramedFlatCoordinates.epsAt x ⟶ G') (w' : FramedFlatCoordinates.epsAt y ⟶ G) (hw : w.left ≫ φ = w'.left) :
    FramedFlatCoordinates.IsCombination x a V w ↔ FramedFlatCoordinates.IsCombination y a U w' := by
  subst hy
  obtain rfl : U = fun k => V k ≫ φ := funext fun k => (hU k).symm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (FramedFlatCoordinates.epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (k : Fin n) (u : FramedFlatCoordinates.epsAt x ⟶ G'), u.left = spMap (epsScaleR (a k)) ≫ V k ↔
      (e u).left = spMap (epsScaleR (a k)) ≫ V k ≫ φ := fun k u => by
    rw [he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR (a k)) ≫ ·) (hV k)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc (a k)))
  have pr : ∀ u : Fin n → (FramedFlatCoordinates.epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod :=
    fun u => by rw [map_list_prod, List.map_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _).2 (by rw [e.apply_symm_apply]; exact hu i), e.injective ?_⟩
    rw [pr]
    simp only [MulEquiv.apply_symm_apply]
    exact hw

theorem isCombination_iff_of_sameVecs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (x : Sp R ⟶ Xo.XF c) (x' : Sp R' ⟶ Xo.XF c) (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)) (v' : Fin n → (epsAt (x' ≫ toX Xo c) ⟶ Xo.univ.t.G)) (vb' : Fin n → (epsAt ((x' ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)), x' = spMap g ≫ x → SameVecs Y x v vb → SameVecs Y x' v' vb' → ∀ (a : Fin n → R') (i : Fin n), FramedFlatCoordinates.IsCombination (x' ≫ toX Xo c) a (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i) ↔ FramedFlatCoordinates.IsCombination ((x' ≫ Y.jQ) ≫ genι Y) a (fun k => spMap (Chart.dualMapR g) ≫ (vb k).left) (vb' i) := by
  intro E _ _ _ H D l Xo c O _ β Y R R' _ _ g x x' n v vb v' vb' hx h h' a i
  choose v₁ h₁ h₂ using h
  obtain ⟨w, hw₁, hw₂⟩ := h' i
  have hV : ∀ k, (spMap (Chart.dualMapR g) ≫ (v₁ k).left) ≫ Y.oF.t.G.hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x' := fun k => by
    subst hx
    exact Over.w (DetExtendZero.epsMap g x ≫ v₁ k)
  refine (isCombination_pull_iff Y.m0.toSABMap.cart x' _ rfl a _ hV _ (fun k => ?_) w _ hw₁).symm.trans
    (isCombination_pull_iff Y.m.cart x' _ (Category.assoc _ _ _) a _ hV _ (fun k => ?_) w _ hw₂)
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₁ k))
  · exact (Category.assoc _ _ _).trans (congrArg (spMap (Chart.dualMapR g) ≫ ·) (h₂ k))

end GlobalTheory.DetLine
end
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_bar (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R]
    {x : Sp R ⟶ Xo.XF c} {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} (h : ∃ j, FrU Xo c U τ j x v w) :
    ∃ vb wb, FrY Y (compactOf Y U) τ h.choose (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb :=
  (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R h.choose x).1 v w h.choose_spec

def restrictRule (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y) : RuleU Xo c :=
  fun R _ x v w =>
    haveI := Classical.propDecidable (∃ j, FrU Xo c U τ j x v w)
    if h : ∃ j, FrU Xo c U τ j x v w then
      σb R (x ≫ Y.jQ) (exists_bar Y U τ h).choose (exists_bar Y U τ h).choose_spec.choose
    else 0

theorem restrictRule_eq (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {σb : RuleY Y}
    (hσb : SecY Y (compactOf Y U) τ σb) {R : Type} [CommRing R] {j : c.F →+* R} {x : Sp R ⟶ Xo.XF c}
    {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin D.p → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} {wb : Fin D.q → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)}
    (h : FrU Xo c U τ j x v w) (hb : FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb) (hv : SameVecs Y x v vb)
    (hw : SameVecs Y x w wb) : restrictRule Y U τ σb R x v w = σb R (x ≫ Y.jQ) vb wb := by
  have hex : ∃ j, FrU Xo c U τ j x v w := ⟨j, h⟩
  obtain ⟨hb0, hv0, hw0⟩ := (exists_bar Y U τ hex).choose_spec.choose_spec
  have e : restrictRule Y U τ σb R x v w =
      σb R (x ≫ Y.jQ) (exists_bar Y U τ hex).choose (exists_bar Y U τ hex).choose_spec.choose := by
    unfold restrictRule
    rw [dif_pos hex]
  rw [e]
  have hx : x ≫ Y.jQ = spMap (RingHom.id R) ≫ (x ≫ Y.jQ) := by
    rw [DetExtendZero.spMap_id, Category.id_comp]
  have hx' : x = spMap (RingHom.id R) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
  have cv : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.p) (Fin D.p) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (vb k).left) ((exists_bar Y U τ hex).choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.p v vb v _ hx' hv hv0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.1.1 k).1) i
  have cw : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.q) (Fin D.q) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (wb k).left)
      ((exists_bar Y U τ hex).choose_spec.choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.q w wb w _ hx' hw hw0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have key := sec_chg hσb hb hb0 (g := RingHom.id R) (M := 1) (N := 1) ⟨hx, cv, cw⟩
  simpa using key.symm

theorem exists_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ σb hσb
  refine ⟨restrictRule Y U τ σb, isSection_of_chg ?_, ?_, ?_⟩
  · intro R R' _ _ g j j' x v w x' v' w' M N h h' hc
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    obtain ⟨vb', wb', hb', hv', hw'⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R' j' x').1 v' w' h'
    rw [restrictRule_eq Y U τ hσb h hb hv hw, restrictRule_eq Y U τ hσb h' hb' hv' hw']
    refine sec_chg hσb hb hb' ⟨by rw [hc.1, Category.assoc], fun i => ?_, fun i => ?_⟩
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.p v vb v' vb' hc.1 hv hv'
        _ i).mp (hc.2.1 i)
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.q w wb w' wb' hc.1 hw hw'
        _ i).mp (hc.2.2 i)
  · intro R _ j x v w vb wb h hb hv hw
    exact (restrictRule_eq Y U τ hσb h hb hv hw).symm
  · intro hnz R _ j x v w h
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    rw [restrictRule_eq Y U τ hσb h hb hv hw]
    exact hnz R j _ vb wb hb

end GlobalTheory.DetLine.Restrict
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_determinantLine_section_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  atlas_forward_decl GlobalTheory.DetLine.Restrict.exists_restriction
end
