import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsion

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.SegreSquare
open GlobalTheory.SegreCoord

variable {X Y : Scheme.{0}} {σ τ : Type}

theorem isUnit_of_mem {M : LB X} (s : M.Sec) (f : Y ⟶ X) (y : Y) (h : f y ∈ Out.nonzeroLocus s) {j : M.ι}
    (hj : f y ∈ M.U j) : IsUnit (gs f y _ (s.f j)) := by
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus s _).1 h
  rw [gs_sec s f y hj hk, Geo.Tor.gs_stalkMap f y _ hk]
  exact (Units.isUnit _).mul (u.map _)

theorem mem_of_isUnit {M : LB X} (s : M.Sec) (f : Y ⟶ X) (y : Y) {j : M.ι}
    (hj : f y ∈ M.U j) (h : IsUnit (gs f y _ (s.f j))) : f y ∈ Out.nonzeroLocus s := by
  rw [Geo.Tor.gs_stalkMap f y _ hj] at h
  exact (mem_nonzeroLocus s _).2 ⟨j, hj, (isUnit_map_iff (f.stalkMap y).hom _).1 h⟩

theorem lbIso_of_proportional {A B : LB Y} (a : τ → A.Sec) (b : τ → B.Sec) (hc : ⨆ i, Out.nonzeroLocus (a i) = ⊤)
    (h : ∀ (y : Y) (l : A.ι) (m : B.ι), y ∈ A.U l → y ∈ B.U m → ∃ u : (Y.presheaf.stalk y)ˣ,
      ∀ i, gs (𝟙 Y) y _ ((b i).f m) = u * gs (𝟙 Y) y _ ((a i).f l)) : LBIso A B := by
  have pt : ∀ y : Y, ∃ i, y ∈ Out.nonzeroLocus (a i) := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, Out.nonzeroLocus (a i) by rw [hc]; trivial)
  have key : ∀ (m : B.ι) (l : A.ι), ∃ w : Γ(Y, B.U m ⊓ A.U l)ˣ, ∀ y ∈ B.U m ⊓ A.U l, ∀ i,
      gs (𝟙 Y) y _ ((b i).f m) = (gm (𝟙 Y) y _ w).val * gs (𝟙 Y) y _ ((a i).f l) := by
    intro m l
    let W : τ → Y.Opens := fun i => B.U m ⊓ A.U l ⊓ Out.nonzeroLocus (a i)
    have lA : ∀ i, W i ≤ A.U l := fun i => inf_le_left.trans inf_le_right
    have lB : ∀ i, W i ≤ B.U m := fun i => inf_le_left.trans inf_le_left
    have ua : ∀ i, IsUnit (resG Y (lA i) ((a i).f l)) := fun i =>
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (gs_res (𝟙 Y) y (lA i) hy _))).mpr
          (isUnit_of_mem (a i) (𝟙 Y) y hy.2 hy.1.2)
    have ub : ∀ i, IsUnit (resG Y (lB i) ((b i).f m)) := fun i =>
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (gs_res (𝟙 Y) y (lB i) hy _))).mpr (by
          obtain ⟨u, hu⟩ := h y l m hy.1.2 hy.1.1
          rw [hu]
          exact u.isUnit.mul (isUnit_of_mem (a i) (𝟙 Y) y hy.2 hy.1.2))
    have val : ∀ i y (hy : y ∈ W i) (u : (Y.presheaf.stalk y)ˣ),
        (∀ i, gs (𝟙 Y) y _ ((b i).f m) = u * gs (𝟙 Y) y _ ((a i).f l)) →
        gm (𝟙 Y) y (W i) ((ub i).unit * (ua i).unit⁻¹) = u := fun i y hy u hu => by
      rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [Units.val_mul, ← gs_unit _ y _ hy, ← gs_unit _ y _ hy, IsUnit.unit_spec, IsUnit.unit_spec,
        gs_res (𝟙 Y) y (lA i) hy, gs_res (𝟙 Y) y (lB i) hy, hu]
    obtain ⟨w, hw⟩ := glue_unit (B.U m ⊓ A.U l) W (fun _ => inf_le_left) (fun y hy => by
      obtain ⟨i, hi⟩ := pt y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩) (fun i => (ub i).unit * (ua i).unit⁻¹) (fun i j y hy => by
      obtain ⟨u, hu⟩ := h y l m hy.1.1.2 hy.1.1.1
      rw [val i y hy.1 u hu, val j y hy.2 u hu])
    refine ⟨w, fun y hy i => ?_⟩
    obtain ⟨u, hu⟩ := h y l m hy.2 hy.1
    obtain ⟨k, hk⟩ := pt y
    have hy' : y ∈ W k := ⟨hy, hk⟩
    rw [← gm_res (𝟙 Y) y (inf_le_left : W k ≤ _) hy', hw, val k y hy' u hu, hu]
  choose w hw using key
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ?_).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 Y) y p q hy)
    (gm_res _ y _ hy _))).symm
  obtain ⟨i, hi⟩ := pt y
  have e₁ := hw p.1 p.2 y hy.1 i
  have e₂ := hw q.1 q.2 y hy.2 i
  rw [gs_sec (b i) (𝟙 Y) y hy.1.1 hy.2.1, gs_sec (a i) (𝟙 Y) y hy.1.2 hy.2.2, e₂, ← mul_assoc, ← mul_assoc] at e₁
  have e₃ := (isUnit_of_mem (a i) (𝟙 Y) y hi hy.2.2).mul_right_cancel e₁
  rw [← Units.val_mul, ← Units.val_mul, Units.val_inj] at e₃
  rw [mul_right_comm]
  exact eq_mul_inv_of_mul_eq e₃.symm

variable {M : LB X} {th : σ → M.Sec} {p q : Y ⟶ X} {M₂ : LB Y} {th₂ : σ × σ → M₂.Sec}

theorem germ_eq (hM : M.IsLB)
    (H : ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Y) (v₁ v₂ : σ → T), SecCoord M th (x ≫ p) v₁ → SecCoord M th (x ≫ q) v₂ →
      SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2))
    (y : Y) {j k : M.ι} {l : M₂.ι} (hj : p y ∈ M.U j) (hk : q y ∈ M.U k) (hl : y ∈ M₂.U l) :
    ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i : σ × σ,
      gs p y _ ((th i.1).f j) * gs q y _ ((th i.2).f k) = u * gs (𝟙 Y) y _ ((th₂ i).f l) := by
  obtain ⟨W, hW, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := p ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ M.U k) (x := y) ⟨hj, hk⟩
  let x : Sp Γ(Y, W) ⟶ Y := hW.fromSpec
  have hx : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  have hr : Set.range x = W := hW.range_fromSpec
  obtain ⟨z, rfl⟩ : y ∈ Set.range x := hr ▸ hy
  have hin : ∀ z, x z ∈ W := fun z => hr.le ⟨z, rfl⟩
  obtain ⟨v₁, h₁⟩ := exists_secCoord (th := th) (x := x ≫ p) hM (k := j) fun z => (hle (hin z)).1
  obtain ⟨v₂, h₂⟩ := exists_secCoord (th := th) (x := x ≫ q) hM (k := k) fun z => (hle (hin z)).2
  obtain ⟨u, hu⟩ := loc_of_secCoord (H _ x v₁ v₂ h₁ h₂) z l hl
  obtain ⟨u₁, hu₁⟩ := loc_of_secCoord h₁ z j hj
  obtain ⟨u₂, hu₂⟩ := loc_of_secCoord h₂ z k hk
  let e := (asIso (x.stalkMap z)).commRingCatIsoToRingEquiv
  refine ⟨Units.map e.symm.toMonoidHom (u₁ * u₂ * u⁻¹), fun i => e.injective ?_⟩
  rw [map_mul, map_mul]
  have a₁ : e (gs p (x z) _ ((th i.1).f j)) = _ := (SegreCoord.gs_stalkMap x p z _ hj _).symm.trans (hu₁ i.1)
  have a₂ : e (gs q (x z) _ ((th i.2).f k)) = _ := (SegreCoord.gs_stalkMap x q z _ hk _).symm.trans (hu₂ i.2)
  have a₃ : e (gs (𝟙 Y) (x z) _ ((th₂ i).f l)) = _ := (Geo.Tor.gs_stalkMap x z _ hl _).symm.trans (hu i)
  have a₄ : e (Units.map e.symm.toMonoidHom (u₁ * u₂ * u⁻¹)).val = (u₁ * u₂ * u⁻¹).val := e.apply_symm_apply _
  rw [a₁, a₂, a₃, a₄, map_mul, Units.val_mul, Units.val_mul]
  linear_combination (-(ev z (v₁ i.1) * ev z (v₂ i.2) * u₁.val * u₂.val)) * u.inv_mul

section
variable (hM : M.IsLB) (hM₂ : M₂.IsLB)
  (G : ∀ (y : Y) {j k : M.ι} {l : M₂.ι}, p y ∈ M.U j → q y ∈ M.U k → y ∈ M₂.U l →
    ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i : σ × σ,
      gs p y _ ((th i.1).f j) * gs q y _ ((th i.2).f k) = u * gs (𝟙 Y) y _ ((th₂ i).f l))
include hM hM₂ G

theorem locus_eq (i : σ × σ) : Out.nonzeroLocus (th₂ i) =
    p ⁻¹ᵁ Out.nonzeroLocus (th i.1) ⊓ q ⁻¹ᵁ Out.nonzeroLocus (th i.2) := by
  ext y
  obtain ⟨j, hj⟩ := exists_chart hM (p y)
  obtain ⟨k, hk⟩ := exists_chart hM (q y)
  obtain ⟨l, hl⟩ := exists_chart hM₂ y
  obtain ⟨u, hu⟩ := G y hj hk hl
  constructor
  · intro h
    have := u.isUnit.mul (isUnit_of_mem (th₂ i) (𝟙 Y) y h hl)
    rw [← hu] at this
    exact ⟨mem_of_isUnit _ p y hj (isUnit_of_mul_isUnit_left this), mem_of_isUnit _ q y hk (isUnit_of_mul_isUnit_right this)⟩
  · intro h
    have := (isUnit_of_mem (th i.1) p y h.1 hj).mul (isUnit_of_mem (th i.2) q y h.2 hk)
    rw [hu] at this
    exact mem_of_isUnit (th₂ i) (𝟙 Y) y hl (isUnit_of_mul_isUnit_right this)

omit hM₂ in
theorem sec_congr (i i' : σ × σ) (h₁ : ∀ j, (th i.1).f j = (th i'.1).f j) (h₂ : ∀ j, (th i.2).f j = (th i'.2).f j)
    (l : M₂.ι) : (th₂ i).f l = (th₂ i').f l := fn_ext fun y hl => by
  obtain ⟨j, hj⟩ := exists_chart hM (p y)
  obtain ⟨k, hk⟩ := exists_chart hM (q y)
  obtain ⟨u, hu⟩ := G y hj hk hl
  exact u.isUnit.mul_left_cancel ((hu i).symm.trans (by rw [h₁, h₂, hu i']))

theorem cover (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) : ⨆ i, Out.nonzeroLocus (th₂ i) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p y ∈ ⨆ i, Out.nonzeroLocus (th i) by rw [hc]; trivial)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show q y ∈ ⨆ i, Out.nonzeroLocus (th i) by rw [hc]; trivial)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ?_⟩
  rw [locus_eq hM hM₂ G]
  exact ⟨hi, hj⟩

theorem iso_box (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) : LBIso M₂ (boxLB M p q) :=
  lbIso_of_proportional th₂ (boxTh th p q) (cover hM hM₂ G hc) fun y l m hl hm => by
    obtain ⟨u, hu⟩ := G y (LB.wchart_le M ![p, q] m 0 hm) (LB.wchart_le M ![p, q] m 1 hm) hl
    refine ⟨u, fun i => (gs_boxF p q _ _ m (𝟙 Y) y hm).trans ?_⟩
    rw [Category.id_comp, Category.id_comp]
    exact hu i

omit hM₂ G in
theorem gs_ratio {i : σ} {r : σ → Γ(X, Out.nonzeroLocus (th i))}
    (hr : ∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) :
    (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : σ) {k : M.ι}, f y ∈ Out.nonzeroLocus (th i) → f y ∈ M.U k →
      gs f y _ ((th j).f k) = gs f y _ (r j) * gs f y _ ((th i).f k)) ∧ r i = 1 := by
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : σ) {k : M.ι}, f y ∈ Out.nonzeroLocus (th i) → f y ∈ M.U k →
      gs f y _ ((th j).f k) = gs f y _ (r j) * gs f y _ ((th i).f k) := fun f y j k h hk => by
    have hm : f y ∈ Out.nonzeroLocus (th i) ⊓ M.U k := ⟨h, hk⟩
    have e := congrArg (gs f y _) (hr j k)
    rwa [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  refine ⟨key, fn_ext fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM y
  refine (isUnit_of_mem (th i) (𝟙 X) y hy hk).mul_right_cancel ((key (𝟙 X) y i hy hk).symm.trans ?_)
  rw [gs_eq (𝟙 X) y _ hy 1, map_one, map_one, one_mul]

theorem vamp {K : Type} [Field K] {s : X ⟶ Sp K} (sq : IsPullback p q s s) (hV : VAmp s M th) :
    VAmp (p ≫ s) M₂ th₂ := by
  refine ⟨cover hM hM₂ G hV.1, fun a => ?_⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hV.2 a.1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := hV.2 a.2
  obtain ⟨g₁, o₁⟩ := gs_ratio hM hr₁
  obtain ⟨g₂, o₂⟩ := gs_ratio hM hr₂
  have loc := locus_eq hM hM₂ G a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => (p.appLE _ _ l₁).hom (r₁ b.1) * (q.appLE _ _ l₂).hom (r₂ b.2), fun b l => fn_ext fun y hy => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of K))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · obtain ⟨j, hj⟩ := exists_chart hM (p y)
    obtain ⟨k, hk⟩ := exists_chart hM (q y)
    obtain ⟨u, hu⟩ := G y hj hk hy.2
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_mul _ y _ hy.1,
      SegreCoord.gs_appLE p y l₁ hy.1, SegreCoord.gs_appLE q y l₂ hy.1]
    refine u.isUnit.mul_left_cancel ?_
    rw [← hu b, mul_left_comm, ← hu a, g₁ p y b.1 (l₁ hy.1) hj, g₂ q y b.2 (l₂ hy.1) hk, mul_mul_mul_comm]
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    let φ := MvPolynomial.eval₂Hom (RingHom.comp ((p ≫ s).appLE ⊤ (Out.nonzeroLocus (th₂ a)) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      (fun b : σ × σ => (p.appLE _ _ l₁).hom (r₁ b.1) * (q.appLE _ _ l₂).hom (r₂ b.2))
    suffices h : φ.range = ⊤ by
      intro f
      obtain ⟨F, hF⟩ := (RingHom.range_eq_top.1 h) f
      exact ⟨F, hF.symm⟩
    rw [← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change (p.appLE _ _ l₁).hom _ ∈ φ.range
      induction F using MvPolynomial.induction_on with
      | C c =>
        refine ⟨MvPolynomial.C c, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C, RingHom.comp_apply, RingHom.comp_apply]
        exact (RepBC.appLE_appLE p s _ _ _ _).symm
      | add F G hF hG => rw [MvPolynomial.eval₂_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [MvPolynomial.eval₂_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (i, a.2), ?_⟩
        simp only [φ, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂_X, o₂, map_one, mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change (q.appLE _ _ l₂).hom _ ∈ φ.range
      induction F using MvPolynomial.induction_on with
      | C c =>
        refine ⟨MvPolynomial.C c, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C, sq.w, RingHom.comp_apply, RingHom.comp_apply]
        exact (RepBC.appLE_appLE q s _ _ _ _).symm
      | add F G hF hG => rw [MvPolynomial.eval₂_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [MvPolynomial.eval₂_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (a.1, i), ?_⟩
        simp only [φ, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂_X, o₁, map_one, one_mul]

end

theorem vamp_iso_of_segre_coordinates : ∀ (K σ : Type) [Field K] [Finite σ] (Z : Over (Sp K)) (M : LB Z.left) (th : σ → M.Sec) (M₂ : LB (Z ⊗ Z).left) (th₂ : σ × σ → M₂.Sec), M.IsLB → M₂.IsLB → VAmp Z.hom M th → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ (Z ⊗ Z).left) (v₁ v₂ : σ → T), SecCoord M th (x ≫ (fst Z Z).left) v₁ → SecCoord M th (x ≫ (snd Z Z).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → VAmp (Z ⊗ Z).hom M₂ th₂ ∧ LBIso M₂ (LB.LinComb M (K := Fin 2) ![(fst Z Z).left, (snd Z Z).left] ![1, 1]) ∧ ∀ i i' : σ × σ, (∀ j, (th i.1).f j = (th i'.1).f j) → (∀ j, (th i.2).f j = (th i'.2).f j) → ∀ j, (th₂ i).f j = (th₂ i').f j := by
  intro K σ _ _ Z M th M₂ th₂ hM hM₂ hV H
  have hP : IsPullback (fst Z Z).left (snd Z Z).left Z.hom Z.hom := IsPullback.of_hasPullback Z.hom Z.hom
  have G := @germ_eq _ _ _ _ _ _ _ _ _ hM H
  refine ⟨?_, ?_, sec_congr hM G⟩
  · rw [← Over.w (fst Z Z)]
    exact vamp hM hM₂ G hP hV
  · rw [show (![1, 1] : Fin 2 → ℤ) = fun _ => 1 from funext fun i => by fin_cases i <;> rfl]
    exact iso_box hM hM₂ G hV.1

end GlobalTheory.ZV.SegreSquare
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AdditionGraph

open GlobalTheory.CechPic
open scoped Kronecker

section Algebra

variable {G H σ κ : Type} [CommGroup G] [CommGroup H] [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in

theorem apply_prod_single (Φ : H ≃* (σ → G)) (pt : κ → G) (a : σ × κ → ℕ) (b : σ) :
    Φ (∏ x : σ × κ, Φ.symm (Pi.mulSingle x.1 (pt x.2)) ^ a x) b = ∏ j, pt j ^ a (b, j) := by
  rw [map_prod, Finset.prod_apply, Fintype.prod_prod_type, Finset.prod_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.mulSingle_eq_of_ne' hc]
  · simp

omit [DecidableEq κ] in

theorem existsUnique_prod_single (Φ : H ≃* (σ → G)) {k : ℕ} (pt : κ → G)
    (h : ∀ y : G, y ^ k = 1 → ∃! c : κ → ZMod k, ∏ j, pt j ^ (c j).val = y) (y : H) (hy : y ^ k = 1) :
    ∃! c : σ × κ → ZMod k, ∏ x : σ × κ, Φ.symm (Pi.mulSingle x.1 (pt x.2)) ^ (c x).val = y := by
  have hb : ∀ b, Φ y b ^ k = 1 := fun b => by
    rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]
  choose c hc hu using fun b => h _ (hb b)
  refine ⟨fun x => c x.1 x.2, Φ.injective (funext fun b => ?_), fun c' hc' => funext fun x => ?_⟩
  · rw [apply_prod_single]
    exact hc b
  · refine congrFun (hu x.1 (fun j => c' (x.1, j)) ?_) x.2
    rw [← hc', apply_prod_single]

theorem act_prod_single (Φ : H ≃* (σ → G)) {k : ℕ} (pt : κ → G) (h : ∀ j, pt j ^ k = 1) (C : Matrix σ σ ℕ)
    (s : H → H) (hs : ∀ y b, Φ (s y) b = ∏ a, Φ y a ^ C b a) (x : σ × κ) :
    s (Φ.symm (Pi.mulSingle x.1 (pt x.2))) = ∏ x' : σ × κ, Φ.symm (Pi.mulSingle x'.1 (pt x'.2)) ^
      ((C.map (Nat.cast : ℕ → ZMod k) ⊗ₖ (1 : Matrix κ κ (ZMod k))) x' x).val := by
  refine Φ.injective (funext fun b => ?_)
  rw [apply_prod_single, hs, Finset.prod_eq_single x.1, Finset.prod_eq_single x.2]
  · simp [ZMod.val_natCast, ← pow_eq_pow_mod _ (h _)]
  · intro j _ hj
    simp [Matrix.one_apply_ne hj]
  · simp
  · intro a _ ha
    simp [Pi.mulSingle_eq_of_ne ha]
  · simp

theorem eq_of_forall_zmod {l a b : ℕ} (hl : l.Prime) (h : ∀ j, (a : ZMod (l ^ j)) = b) : a = b := by
  have hlt : a + b < l ^ (a + b) := Nat.lt_pow_self hl.one_lt
  exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).1 (h (a + b))) (by omega) (by omega)

end Algebra

section Geometry

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem linComb_equiv {T : Over S} {n : ℕ} {σ : Type} [Fintype σ] (ε : Fin n ≃ σ) (y : σ → (T ⟶ B)) (a : σ → ℕ) :
    Out.linComb (fun i => y (ε i)) (fun i => a (ε i)) = ∏ x, y x ^ a x := by
  rw [Out.linComb, List.prod_ofFn]
  exact ε.prod_comp fun x => y x ^ a x

def pointsEquiv (e : B ≅ A ⊗ A) [IsMonHom (e.hom ≫ fst A A)] [IsMonHom (e.hom ≫ snd A A)] (T : Over S) :
    (T ⟶ B) ≃* (Fin 2 → (T ⟶ A)) where
  toFun x := ![x ≫ e.hom ≫ fst A A, x ≫ e.hom ≫ snd A A]
  invFun y := lift (y 0) (y 1) ≫ e.inv
  left_inv x := by
    rw [← cancel_mono e.hom]
    ext <;> simp
  right_inv y := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i
    · exact MonObj.mul_comp x y (e.hom ≫ fst A A)
    · exact MonObj.mul_comp x y (e.hom ≫ snd A A)

omit [IsCommMonObj B] in

theorem isMonHom_mul (p q : B ⟶ A) [IsMonHom p] [IsMonHom q] : IsMonHom (p * q) where
  one_hom := by
    rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom]
    have e₁ : (η[A] : 𝟙_ _ ⟶ A) = 1 := by rw [Hom.one_def]; simp
    rw [e₁, _root_.mul_one]
  mul_hom := by
    have e₁ : μ[B] = fst B B * snd B B := by simp [Hom.mul_def]
    have e₂ : ((p * q) ⊗ₘ (p * q)) ≫ μ[A] = (fst B B ≫ (p * q)) * (snd B B ≫ (p * q)) := by
      rw [Hom.mul_def (fst B B ≫ (p * q))]
      congr 1
    rw [e₂, e₁]
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

omit [IsCommMonObj A] [IsCommMonObj B] in
theorem lam_add {T : Over S} (c d : Pic B.left) (x y : T ⟶ B) : lam (c + d) x y = lam c x y + lam d x y := by
  simp only [lam, map_add]
  abel

end Geometry

end GlobalTheory.AdditionGraph

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.AdditionGraph
open scoped Kronecker

theorem sectionsDim_additionGraph_principalPolarisation : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ), 1 ≤ N → ∀ e ≥ 1, SectionsHaveFiniteDimension (P.A ⊗ P.A).hom (lbPow (LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]) e) (3 ^ P.g * (N * e) ^ (2 * P.g)) := by
  intro laws laws₂ K _ _ P N hN e he
  obtain ⟨Q, φ, hp, hq, hg, hQ⟩ := SquarePol.exists_square K P
  have := P.isAb.comm
  have := Q.isAb.comm
  have := P.isAb.proper
  have := Q.isAb.proper
  have hL := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (laws.cube _ P ⟨P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  obtain ⟨-, -, hsym, -, -, htor⟩ := GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample laws laws₂ K P
  let Φ := pointsEquiv φ
  set p := φ.hom ≫ fst P.A P.A with hpd
  set q := φ.hom ≫ snd P.A P.A with hqd
  have hpq := isMonHom_mul p q
  set c := cls P.L hL with hc

  let M : LB Q.A.left := LB.LinComb P.L (K := Fin 3) ![p.left, q.left, (p * q).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have cM : cls M hM = N • (pull p.left c + pull q.left c + pull (p * q).left c) := by
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp [← hc]
  have cQ : cls Q.L Q.isLB = pull p.left c + pull q.left c := by
    rw [(cls_eq_iff Q.isLB (LB.isLB_linComb hL _ _)).2 hQ, cls_linComb hL, Fin.sum_univ_two]
    simp [← hc]

  have hamp : Out.RelAmple Q.A M := by
    obtain ⟨n, hn, hgen⟩ := ((relAmple_iff_isAmpleLB_of_isAffine P.A hL).1 P.ample).exists_isGenerated_pow
    have a₁ := (isAmpleLB_pow_iff Q.isLB (k := n * N) (Nat.mul_pos hn hN)).2
      ((relAmple_iff_isAmpleLB_of_isAffine Q.A Q.isLB).1 Q.ample)
    have a₂ := (hgen.pow N).pull (p * q).left
    have hMn : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
    refine (relAmple_iff_isAmpleLB_of_isAffine Q.A hM).2 ((isAmpleLB_pow_iff hM hn).1
      (a₁.tensor_isGenerated a₂ hMn ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hMn a₁.isLB) a₂.isLB)).1 ?_)))
    rw [cls_div (LB.isLB_div hMn a₁.isLB) a₂.isLB, cls_div hMn a₁.isLB, cls_pull (hgen.pow N).isLB,
      cls_lbPow hgen.isLB, cls_lbPow hL, cls_lbPow hM, cls_lbPow Q.isLB, cM, cQ, map_nsmul, map_nsmul, ← hc]
    module

  have hsymM : SymB M := by
    have e₁ : pull (GrpObj.inv : P.A ⟶ P.A).left c = c :=
      ((cls_eq_iff hL (pull_isLB hL _)).2 hsym).symm
    have e₂ : ∀ (r : Q.A ⟶ P.A) [IsMonHom r],
        pull (GrpObj.inv : Q.A ⟶ Q.A).left (pull r.left c) = pull r.left c := fun r _ => by
      rw [← pull_comp, ← Over.comp_left, GrpObj.inv_hom, Over.comp_left, pull_comp, e₁]
    refine (cls_eq_iff hM (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, cM, map_nsmul, map_add, map_add, e₂, e₂, e₂]

  let C : Matrix (Fin 2) (Fin 2) ℕ := !![2 * N, N; N, 2 * N]
  let s : Q.A ⟶ Q.A := (Φ Q.A).symm ![p ^ (2 * N) * q ^ N, p ^ N * q ^ (2 * N)]
  have sp : s ≫ p = p ^ (2 * N) * q ^ N := congrFun ((Φ Q.A).apply_symm_apply _) 0
  have sq : s ≫ q = p ^ N * q ^ (2 * N) := congrFun ((Φ Q.A).apply_symm_apply _) 1
  have hs : ∀ {T : Over (Sp K)} (y : T ⟶ Q.A) (b : Fin 2), Φ T (y ≫ s) b = ∏ a, Φ T y a ^ C b a := by
    intro T y b
    rw [Fin.prod_univ_two]
    fin_cases b
    · change (y ≫ s) ≫ p = (y ≫ p) ^ (2 * N) * (y ≫ q) ^ N
      rw [Category.assoc, sp, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]
    · change (y ≫ s) ≫ q = (y ≫ p) ^ N * (y ≫ q) ^ (2 * N)
      rw [Category.assoc, sq, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]
  have hform : FormIs Q M s := by
    refine ⟨laws.rigidity _ _ _ Q.isAb Q.isAb _ ?_, ?_⟩
    · have e₁ : (η[Q.A] : 𝟙_ _ ⟶ Q.A) = 1 := by rw [Hom.one_def]; simp
      rw [e₁]
      refine (Φ _).injective (funext fun b => ?_)
      rw [hs, map_one]
      simp
    · have mr : ∀ {T : Over (Sp K)} (x y z : T ⟶ P.A), lam c x (y * z) = lam c x y + lam c x z := fun x y z => by
        rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]
      refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb Q.isLB _ _)).1 ?_
      refine (cls_cube_two hM _ _ _).trans (Eq.trans ?_ (cls_cube_two Q.isLB _ _ _).symm)
      rw [cM, cQ, lam_nsmul]
      simp only [lam_add, lam_pull, Category.assoc, sp, sq, MonObj.comp_mul, MonObj.comp_pow, mr]
      simp only [hc, lam_mul_left hL hΘ, lam_pow_right hL hΘ]
      module

  obtain ⟨l, hl, hlK⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_cases h : ((2 : ℕ) : K) = 0
    · refine ⟨3, Nat.prime_three, fun h' => one_ne_zero (α := K) ?_⟩
      push_cast at h h'
      linear_combination h' - h
    · exact ⟨2, Nat.prime_two, h⟩
  obtain ⟨δ, -, hδ, hdet⟩ := GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion laws laws₂ K Q M s l hl hlK hM hamp hsymM hform
  have hsq : δ ^ 2 = ((3 * N ^ 2) ^ P.g) ^ 2 := by
    refine eq_of_forall_zmod hl fun j => ?_
    obtain ⟨pt, ⟨h₀, h₁, h₂⟩, -⟩ := htor (l ^ j) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
    let ε : Fin (2 * Q.g) ≃ Fin 2 × Fin (2 * P.g) := (finCongr (by rw [hg])).trans finProdFinEquiv.symm
    let z : Fin 2 × Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ Q.A) := fun x => (Φ _).symm (Pi.mulSingle x.1 (pt x.2))
    let D := C.map (Nat.cast : ℕ → ZMod (l ^ j)) ⊗ₖ (1 : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j)))
    have h₃ := hdet j (fun i => z (ε i)) (D.submatrix ε ε) ⟨h₀, fun i => ?_, fun y hy => ?_⟩
      ⟨h₀, fun i => ?_⟩
    · have hC : (C.map (Nat.cast : ℕ → ZMod (l ^ j))).det = 3 * (N : ZMod (l ^ j)) ^ 2 := by
        simp [C, Matrix.det_fin_two]
        ring
      rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, hC, Matrix.det_one, one_pow, _root_.mul_one,
        Fintype.card_fin] at h₃
      push_cast
      rw [h₃, ← pow_mul, _root_.mul_comm P.g]
    · rw [← map_pow, ← Pi.mulSingle_pow, h₁, Pi.mulSingle_one, map_one]
    · have h₄ := existsUnique_prod_single (Φ _) pt (fun y hy => by
        simpa only [Out.linComb, List.prod_ofFn] using h₂ y hy) y hy
      refine ((Equiv.arrowCongr ε.symm (Equiv.refl _)).existsUnique_congr fun a => ?_).1 h₄
      rw [← linComb_equiv ε z fun x => (a x).val]
      rfl
    · exact (act_prod_single (Φ _) pt h₁ C (· ≫ s) hs (ε i)).trans
        (linComb_equiv ε z fun x => (D x (ε i)).val).symm
  have hδ' : δ = (3 * N ^ 2) ^ P.g := Nat.pow_left_injective two_ne_zero hsq
  have H := hδ e he
  rw [show δ * e ^ Q.g = 3 ^ P.g * (N * e) ^ (2 * P.g) by rw [hδ', hg]; ring] at H

  let M' := LB.LinComb P.L (K := Fin 3)
    ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
  have hM' : M'.IsLB := LB.isLB_linComb hL _ _
  have hMe : (lbPow M e).IsLB := LB.isLB_linComb hM _ _
  have hMe' : (lbPow M' e).IsLB := LB.isLB_linComb hM' _ _
  refine ((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ (P.A ⊗ P.A).hom _ hMe').2.2.2.2.2 _ ((Over.forget _).mapIso φ) _).2 ?_
  change SectionsHaveFiniteDimension (φ.hom.left ≫ (P.A ⊗ P.A).hom) ((lbPow M' e).pull φ.hom.left) _
  rw [Over.w]
  refine ((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ Q.A.hom _ hMe).2.1 _ (pull_isLB hMe' _) ?_).1 _ H
  refine (cls_eq_iff hMe (pull_isLB hMe' _)).1 ?_
  rw [cls_pull hMe', cls_lbPow hM, cls_lbPow hM', cM, cls_linComb hL, Fin.sum_univ_three]
  have e₁ : ∀ r : P.A ⊗ P.A ⟶ P.A, pull φ.hom.left (pull r.left c) = pull (φ.hom ≫ r).left c := fun r => by
    rw [Over.comp_left, pull_comp]
  simp only [← hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_nsmul, map_add, map_zsmul, e₁,
    MonObj.comp_mul, ← hpd, ← hqd]
  module

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.AddGraph

open GlobalTheory.CechPic

theorem pull_inv_cls {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨U, hU, ht⟩ := hs (default : PrimeSpectrum K)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun q _ => by rw [Subsingleton.elim q (default : PrimeSpectrum K)]; exact hU
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ht
  rw [cls_linComb hL, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_comp] at e
  obtain ⟨ψ, k⟩ : ∃ ψ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, ψ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have e' := congrArg (pull ψ) (add_neg_eq_zero.1 e)
  rwa [← pull_comp ψ, ← pull_comp ψ, k, pull_id, pull_id] at e'

theorem pull_inv_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : B ⟶ A)
    (hf : (GrpObj.inv : B ⟶ B) ≫ f = f ≫ (GrpObj.inv : A ⟶ A)) (c : Pic A.left)
    (hc : pull (GrpObj.inv : A ⟶ A).left c = c) :
    pull (GrpObj.inv : B ⟶ B).left (pull f.left c) = pull f.left c := by
  rw [← pull_comp, ← Over.comp_left, hf, Over.comp_left, pull_comp, hc]

theorem lab_add {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (a a' : Ix g k) : t.lab (a + a') = t.lab a * t.lab a' := by
  haveI := t.ab.comm
  simp only [TObj.lab, Out.linComb, List.prod_ofFn]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, Pi.add_apply, ZMod.val_add]
  exact (pow_eq_pow_mod _ (t.torsion i)).symm

def red (g : ℕ) {k k' : ℕ} (h : k' ∣ k) (a : Ix g k) : Ix g k' := fun i => ZMod.castHom h (ZMod k') (a i)

theorem red_surjective (g : ℕ) {k k' : ℕ} (h : k' ∣ k) : Function.Surjective (red g h) := fun a =>
  ⟨fun i => (ZMod.castHom_surjective h (a i)).choose, funext fun i => (ZMod.castHom_surjective h (a i)).choose_spec⟩

theorem modEq_of_red {g k k' : ℕ} [NeZero k] (h : k' ∣ k) {a a' : Ix g k} (e : red g h a = red g h a') (i) :
    (a i).val ≡ (a' i).val [MOD k'] := by
  have := congrFun e i
  simp only [red, ZMod.castHom_apply, ZMod.cast_eq_val] at this
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this

theorem square_data {K : Type} [Field K] (P P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A)
    (h₁ : IsMonHom (e.hom ≫ fst P.A P.A)) (h₂ : IsMonHom (e.hom ≫ snd P.A P.A)) (Z : Over (Sp K)) (π : Z ⟶ P.A)
    [IsIso π] (N : ℕ) (M : LB (Z ⊗ Z).left) (hM : M.IsLB)
    (hc : cls M hM = N • pull (fst Z Z ≫ π).left (cls P.L P.isLB) + N • pull (snd Z Z ≫ π).left (cls P.L P.isLB) +
      N • pull ((fst Z Z ≫ π) * (snd Z Z ≫ π)).left (cls P.L P.isLB)) :
    ∃ (E : (Z ⊗ Z).left ≅ P₂.A.left), E.hom ≫ P₂.A.hom = (Z ⊗ Z).hom ∧ SymB (A := P₂.A) (M.pull E.inv) ∧
      (∀ n r, SectionsHaveFiniteDimension (P.A ⊗ P.A).hom (lbPow (LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left,
        (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]) n) r → SectionsHaveFiniteDimension (Z ⊗ Z).hom (lbPow M n) r) ∧
      (∀ x y : Out.baseOver (Sp K) ⟶ Z, (lift (x ≫ π) (y ≫ π) ≫ e.inv).left ≫ E.inv = (lift x y).left) ∧
      ∀ (k : ℕ) (I : Type) (u : I → (Out.baseOver (Sp K) ⟶ P.A)), (∀ x, x ^ k = 1 → ∃ i, u i = x) →
        ∀ x : Out.baseOver (Sp K) ⟶ P₂.A, x ^ k = 1 → ∃ i : I × I, lift (u i.1) (u i.2) ≫ e.inv = x := by
  haveI := P.isAb.comm
  let F : Z ⊗ Z ≅ P.A ⊗ P.A := tensorIso (asIso π) (asIso π)
  have F₁ : F.hom ≫ fst _ _ = fst Z Z ≫ π := tensorHom_fst _ _
  have F₂ : F.hom ≫ snd _ _ = snd Z Z ≫ π := tensorHom_snd _ _
  let G : Z ⊗ Z ≅ P₂.A := F ≪≫ e.symm
  have G₁ : G.inv ≫ fst Z Z ≫ π = e.hom ≫ fst _ _ := by
    rw [← F₁]; simp [G]
  have G₂ : G.inv ≫ snd Z Z ≫ π = e.hom ≫ snd _ _ := by
    rw [← F₂]; simp [G]
  have hinv := pull_inv_cls P.A P.L P.isLB P.sym
  refine ⟨(Over.forget _).mapIso G, Over.w G.hom, ?_, fun n r H => ?_, fun x y => ?_,
    fun k I u hu x hx => ?_⟩
  · show LBIso (M.pull G.inv.left) ((M.pull G.inv.left).pull (GrpObj.inv : P₂.A ⟶ P₂.A).left)
    refine (cls_eq_iff (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)).1 ?_
    rw [cls_pull (pull_isLB hM _), cls_pull hM, hc]
    simp only [map_add, map_nsmul, ← pull_comp G.inv.left, ← Over.comp_left, Hom.mul_def, ← Category.assoc G.inv (lift _ _), comp_lift, G₁, G₂]
    have i₁ : (GrpObj.inv : P₂.A ⟶ P₂.A) ≫ e.hom ≫ fst _ _ = (e.hom ≫ fst _ _) ≫ (GrpObj.inv : P.A ⟶ P.A) :=
      GrpObj.inv_hom _
    have i₂ : (GrpObj.inv : P₂.A ⟶ P₂.A) ≫ e.hom ≫ snd _ _ = (e.hom ≫ snd _ _) ≫ (GrpObj.inv : P.A ⟶ P.A) :=
      GrpObj.inv_hom _
    rw [pull_inv_hom _ i₁ _ hinv, pull_inv_hom _ i₂ _ hinv, pull_inv_hom _ _ _ hinv]
    rw [← Hom.mul_def, MonObj.comp_mul, i₁, i₂, ← Hom.inv_def, ← Hom.inv_def, ← Hom.inv_def, mul_inv]
  · have hN := LB.isLB_linComb P.isLB (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left,
        (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
    have hNn := LB.isLB_linComb hN (K := PUnit) (fun _ => 𝟙 _) (fun _ => (n : ℤ))
    have hMn := LB.isLB_linComb hM (K := PUnit) (fun _ => 𝟙 _) (fun _ => (n : ℤ))
    have H' : SectionsHaveFiniteDimension (F.hom.left ≫ (P.A ⊗ P.A).hom) (LB.pull _ F.hom.left) r := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ hNn).2.2.2.2.2 _ ((Over.forget _).mapIso F) r).1 H
    rw [Over.w F.hom] at H'
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ (pull_isLB hNn _)).2.1 _ hMn ?_).1 r H'
    refine (cls_eq_iff (pull_isLB hNn _) hMn).1 ?_
    rw [cls_pull hNn, cls_lbPow hN, cls_lbPow hM, hc, cls_linComb P.isLB, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, natCast_zsmul, map_add, map_nsmul,
      ← pull_comp, ← Over.comp_left, MonObj.comp_mul, F₁, F₂]
  · show (lift (x ≫ π) (y ≫ π) ≫ e.inv).left ≫ G.inv.left = _
    rw [← Over.comp_left]
    congr 1
    simp [G, F]
  · obtain ⟨a₁, ha₁⟩ := hu (x ≫ e.hom ≫ fst _ _) (by rw [← MonObj.pow_comp, hx, MonObj.one_comp])
    obtain ⟨a₂, ha₂⟩ := hu (x ≫ e.hom ≫ snd _ _) (by rw [← MonObj.pow_comp, hx, MonObj.one_comp])
    refine ⟨(a₁, a₂), ?_⟩
    rw [ha₁, ha₂, Iso.comp_inv_eq]
    ext1 <;> simp

end GlobalTheory.AddGraph

open GlobalTheory.AddGraph GlobalTheory.CechPic in

theorem GlobalTheory.cutBy_graph_addition : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (M₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (th₂ : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2) → M₂.Sec), M₂.IsLB → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (v₁ v₂ : _ → T), SecCoord _ σ (x ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₁ → SecCoord _ σ (x ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h)) → CutBy (graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K)))) ((fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A))).left) Q d (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  have hn1 := hn.one_lt
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, H⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion hL hL2 (2 * g) (2 * (n ^ 2) ^ 2)
    ((Ix g ((n ^ 2) ^ 2) × Ix g ((n ^ 2) ^ 2)) × Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdiv : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdiv' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdiv 2
  have hδ : 3 ^ g * ((n ^ 2) ^ 2) ^ (2 * g) ≤ (2 * (n ^ 2) ^ 2) ^ (2 * g) := by
    rw [mul_pow 2, pow_mul 2]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) g)
  obtain ⟨Q, HQ⟩ := H _ hδ ((Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2))
    (Prod.map (Prod.map (red g hdiv') (red g hdiv')) (red g hdiv'))
    (((red_surjective g hdiv').prodMap (red_surjective g hdiv')).prodMap (red_surjective g hdiv'))
  refine ⟨Q, d, fun K _ _ β t σ p M₂ th₂ hM₂ hemb hseg hp => ?_⟩
  obtain ⟨hiso, hH, hva, hHiso, hper, -, hlab⟩ := GlobalTheory.embSec_veryAmple_periodic hL hL2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdiv
    (hn.two_le.trans (Nat.le_self_pow two_ne_zero n)) hemb
  haveI := t.ab.comm
  haveI hπ : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A) := by
    haveI : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp K))) t.A)) := hiso
    exact isIso_of_reflects_iso _ (Over.forget _)
  have hZ : (fst (Over.mk (𝟙 (Sp K))) t.A).left = ((Over.mk (𝟙 (Sp K))) ⊗ t.A).hom := (Category.comp_id _).symm.trans (Over.w (fst (Over.mk (𝟙 (Sp K))) t.A))
  rw [hZ] at hva
  obtain ⟨hva₂, hiso₂, hper₂⟩ := GlobalTheory.ZV.SegreSquare.vamp_iso_of_segre_coordinates K _ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) _ σ M₂ th₂ hH hM₂ hva hseg
  suffices key : ∀ add : ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⊗ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⟶ (Over.mk (𝟙 (Sp K))) ⊗ t.A, add ≫ snd (Over.mk (𝟙 (Sp K))) t.A =
      (fst ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ≫ snd _ t.A) * (snd ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ≫ snd _ t.A) →
      CutBy (graphIdeal (((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⊗ ((Over.mk (𝟙 (Sp K))) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ add.left) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) from
    key _ (lift_snd _ _)
  intro add hadd'
  obtain ⟨M, th, hM, hvaM, hisoM, hI, hco, hperM⟩ := GlobalTheory.ZV.GraphSystem.exists_product_system K _ _ _ _ _ _ _ _ M₂ _ th₂ σ (𝟙 _) add.left hM₂ hH hva₂ hva
    inferInstance (Category.id_comp _) (Over.w add)
  obtain ⟨P₂, e, h₁, h₂, hg, -⟩ := GlobalTheory.SquarePol.exists_square K t.pol
  have cH := (cls_eq_iff hH (pull_isLB (LB.isLB_linComb t.isLB _ _) _)).2 hHiso
  rw [cls_pull (LB.isLB_linComb t.isLB _ _), cls_lbPow t.isLB, map_nsmul] at cH
  have c₂ := (cls_eq_iff hM₂ (LB.isLB_linComb hH _ _)).2 hiso₂
  rw [cls_linComb hH, Fin.sum_univ_two, cH] at c₂
  have cM := (cls_eq_iff (LB.isLB_div hM (pull_isLB hM₂ _)) (pull_isLB hH _)).2 hisoM
  rw [cls_div hM (pull_isLB hM₂ _), cls_pull hM₂, cls_pull hH, pull_id, sub_eq_iff_eq_add', c₂, cH] at cM
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, map_nsmul, ← pull_comp, ← Over.comp_left, hadd'] at cM
  obtain ⟨E, hE, hsym, hH0, hpt, htor⟩ := @square_data K _ t.pol P₂ e h₁ h₂ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) (snd (Over.mk (𝟙 (Sp K))) t.A) hπ ((n ^ 2) ^ 2) M hM cM
  rw [hI, ← hE]
  refine HQ K P₂ hg _ E M th (n ^ j) _ (fun h => lift (t.lab h.1 ^ n ^ j) (t.lab h.2 ^ n ^ j) ≫ e.inv) _ hM hsym
    (hE ▸ hvaM) (fun a a' haa => ?_) (fun m hm => ?_) ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn1).le) ?_
    (htor _ _ (fun h => t.lab h ^ n ^ j) hlab) (fun h => ?_)
  · have e₁ := congrArg (fun z => z.1.1) haa
    have e₂ := congrArg (fun z => z.1.2) haa
    have e₃ := congrArg (fun z => z.2) haa
    exact hperM a a' (hper₂ _ _ (hper _ _ (modEq_of_red hdiv' e₁)) (hper _ _ (modEq_of_red hdiv' e₂)))
      (hper _ _ (modEq_of_red hdiv' e₃))
  · rw [hE, Nat.mul_assoc, ← mul_pow]
    exact hH0 m _ (GlobalTheory.sectionsDim_additionGraph_principalPolarisation hL hL2 K t.pol _ (Nat.one_le_iff_ne_zero.2 (NeZero.ne _)) m hm)
  · have u := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow] at u
    exact ne_zero_pow two_ne_zero u
  · have k : (lift (t.lab h.1 ^ n ^ j) (t.lab h.2 ^ n ^ j) ≫ e.inv).left ≫ E.inv =
        (lift (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.1 ^ n ^ j)) (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.2 ^ n ^ j))).left := by
      refine Eq.trans ?_ (hpt _ _)
      exact congrArg (fun z => (z ≫ e.inv).left ≫ E.inv) (congrArg₂ lift (lift_snd _ _).symm (lift_snd _ _).symm)
    refine k ▸ hco K _ (fun i => p h.1 i.1 * p h.2 i.2) (p (h.1 + h.2)) (hseg K _ _ _ ?_ ?_) ?_
    · rw [Category.comp_id, ← Over.comp_left, lift_fst]; exact hp _
    · rw [Category.comp_id, ← Over.comp_left, lift_snd]; exact hp _
    · have : lift (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.1 ^ n ^ j)) (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.2 ^ n ^ j)) ≫ add =
          lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (h.1 + h.2) ^ n ^ j) := by
        rw [← cancel_mono (snd (Over.mk (𝟙 (Sp K))) t.A), Category.assoc, hadd', MonObj.comp_mul, lab_add, mul_pow]
        simp
      rw [← Over.comp_left, this]; exact hp _
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionGraph_thetaObject_cutOut_bounded_degree : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (M₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (th₂ : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2) → M₂.Sec), M₂.IsLB → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (v₁ v₂ : _ → T), SecCoord _ σ (x ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₁ → SecCoord _ σ (x ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h)) → CutBy (graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K)))) ((fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A))).left) Q d (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) := by
  first | exact @GlobalTheory.cutBy_graph_addition | exact GlobalTheory.cutBy_graph_addition | (intros; apply GlobalTheory.cutBy_graph_addition <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.BuildAdd

theorem isPullback_square {S S' : Scheme.{0}} {A : Over S'} {Z : Over S} {φ : A.left ⟶ Z.left} {x : S' ⟶ S}
    (hA : IsPullback φ A.hom Z.hom x) (φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A ⊗ A).hom (Z ⊗ Z).hom x := by
  have w₁ : (fst Z Z).left ≫ Z.hom = (Z ⊗ Z).hom := Over.w _
  have w₂ : (snd Z Z).left ≫ Z.hom = (Z ⊗ Z).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst Z Z).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd Z Z).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst Z Z).left = _ ≫ (fst Z Z).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd Z Z).left = _ ≫ (snd Z Z).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, Category.assoc, v₁, h2]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, Category.assoc, v₂, h2]

theorem exists_isSquare {S S' : Scheme.{0}} {A : Over S'} {Z : Over S} {φ : A.left ⟶ Z.left} {x : S' ⟶ S}
    (w : φ ≫ Z.hom = A.hom ≫ x) : ∃ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  exact ⟨pullback.lift ((fst A A).left ≫ φ) ((snd A A).left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (e : Y' ⟶ Y) [IsIso e]
    (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R) (hs : e ≫ s = s')
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y') (v : σ₁ → T),
      SecCoord M₁' th₁' (y ≫ a₁') v ↔ SecCoord M₁ th₁ (y ≫ e ≫ a₁) v)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y') (v : σ₂ → T),
      SecCoord M₂' th₂' (y ≫ a₂') v ↔ SecCoord M₂ th₂ (y ≫ e ≫ a₂) v) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [graphIdeal, Ideal.mem_iInf]
  constructor
  · rintro H T iT β y v₁ v₂ ⟨k₀, k₁, k₂⟩
    refine H T iT β (y ≫ inv e) v₁ v₂ ⟨?_, ?_, ?_⟩
    · rw [← hs, Category.assoc, IsIso.inv_hom_id_assoc, k₀]
    · rw [h₁, Category.assoc, IsIso.inv_hom_id_assoc]; exact k₁
    · rw [h₂, Category.assoc, IsIso.inv_hom_id_assoc]; exact k₂
  · rintro H T iT β y v₁ v₂ ⟨k₀, k₁, k₂⟩
    refine H T iT β (y ≫ e) v₁ v₂ ⟨?_, ?_, ?_⟩
    · rw [Category.assoc, hs, k₀]
    · rw [Category.assoc, ← h₁]; exact k₁
    · rw [Category.assoc, ← h₂]; exact k₂

instance isIso_snd_base {S : Scheme.{0}} (A : Over S) : IsIso (snd (Over.mk (𝟙 S)) A) :=
  ⟨lift (Over.homMk A.hom (by simp)) (𝟙 A), by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · simp, by simp⟩

theorem graph_transport {R K D : Type} [CommRing R] [Field K] (x : R →+* K) (Z : Over (Sp R)) (M : LB Z.left)
    (th : D → M.Sec) (M₂ : LB (Z ⊗ Z).left) (th₂ : D × D → M₂.Sec) (hM₂ : M₂.IsLB)
    (hseg : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Z ⊗ Z).left) (v₁ v₂ : D → T), SecCoord M th (y ≫ (fst Z Z).left) v₁ →
      SecCoord M th (y ≫ (snd Z Z).left) v₂ → SecCoord M₂ th₂ y (fun i => v₁ i.1 * v₂ i.2))
    (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ Z.left) (L : LB (Over.mk (𝟙 (Sp K)) ⊗ A).left) (σ : D → L.Sec)
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : D → T),
      SecCoord L σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w)
    (e : (A ⊗ A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)) [IsIso e]
    (hsq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (e ≫ pullback.fst _ _)) (he : e ≫ pullback.snd _ _ = (A ⊗ A).hom)
    (f : pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) (hf : e ≫ f = (μ[A]).left ≫ φ) :
    ∃ (N₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A)).left) (t₂ : D × D → N₂.Sec), N₂.IsLB ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A)).left) (v₁ v₂ : D → T),
        SecCoord L σ (y ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left) v₁ → SecCoord L σ (y ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left) v₂ →
        SecCoord N₂ t₂ y (fun i => v₁ i.1 * v₂ i.2)) ∧
      graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A)).hom N₂ t₂ (𝟙 _) L σ
        (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K))))
          ((fst (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A) ≫ snd _ A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A) ≫ snd _ A))).left =
      graphIdeal (pullback.snd (Z ⊗ Z).hom (spMap x)) M₂ th₂ (pullback.fst _ _) M th f := by
  set r := snd (Over.mk (𝟙 (Sp K))) A with hr
  let q : (Over.mk (𝟙 (Sp K)) ⊗ A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ A) ⟶ A ⊗ A := r ⊗ₘ r
  have : IsIso q := inferInstanceAs (IsIso (r ⊗ₘ r))
  have : IsIso q.left := inferInstanceAs (IsIso ((Over.forget _).map q))
  have q₁ : q.left ≫ (fst A A).left = (fst (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left ≫ r.left := by
    rw [← Over.comp_left, ← Over.comp_left]; simp [q]
  have q₂ : q.left ≫ (snd A A).left = (snd (Over.mk (𝟙 (Sp K)) ⊗ A) (Over.mk (𝟙 (Sp K)) ⊗ A)).left ≫ r.left := by
    rw [← Over.comp_left, ← Over.comp_left]; simp [q]
  have s₁ := hsq.1
  have s₂ := hsq.2
  obtain ⟨t₂, ht₂⟩ := (GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus _ M₂ _ th₂ hM₂).1 _ (q.left ≫ e ≫ pullback.fst _ _)
  refine ⟨_, t₂, pull_isLB hM₂ _, fun T _ y v₁ v₂ k₁ k₂ => ?_, ?_⟩
  · rw [ht₂]
    rw [hσ] at k₁ k₂
    apply hseg
    · rw [Category.assoc, Category.assoc, s₁, reassoc_of% q₁]
      simpa only [Category.assoc] using k₁
    · rw [Category.assoc, Category.assoc, s₂, reassoc_of% q₂]
      simpa only [Category.assoc] using k₂
  · refine graphIdeal_eq (q.left ≫ e) _ _ ?_ _ _ _ _ _ _ _ _ _ _ _ _ (fun T _ y v => ?_) (fun T _ y v => ?_)
    · rw [Category.assoc, he, Over.w]
    · rw [ht₂, Category.comp_id, Category.assoc]
    · rw [hσ, Category.assoc, Category.assoc, hf, ← Over.comp_left_assoc, ← Over.comp_left_assoc, hr, lift_snd,
        Hom.mul_def, lift_fst_comp_snd_comp]

theorem exists_add : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ m : Z ⊗ Z ⟶ Z, (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) := by
  intro L1 L2 g J _ Mat κ n hn ho
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.additionGraph_thetaObject_cutOut_bounded_degree L1 L2 g J Mat κ n hn ho
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hVD ⟨hP, hS, _, hp⟩ hfib => ?_⟩
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨I₂, M₂, th₂, hP₂, hseg⟩ := GlobalTheory.SegreCoord.exists_segre_coordinates R _ I Z M th hP
  have hsm : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have hsm₂ : Smooth (Z ⊗ Z).hom := by
    rw [← Over.w (fst Z Z)]
    have : Smooth (fst Z Z).left := inferInstanceAs (Smooth (pullback.fst Z.hom Z.hom))
    infer_instance
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback (Z ⊗ Z).hom (spMap x) ⟶ Z.left) → Prop :=
    fun K _ x f => IsAlgClosed K ∧ ∃ (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
      ∃ e : (t'.A ⊗ t'.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x), IsIso e ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (e ≫ pullback.fst _ _) ∧ e ≫ pullback.snd _ _ = (t'.A ⊗ t'.A).hom ∧
        e ≫ f = (μ[t'.A]).left ≫ φ
  have hG : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ →
      ∃ (e : (t'.A ⊗ t'.A).left ⟶ pullback (Z ⊗ Z).hom (spMap x)) (f : _), G K x f ∧ e ≫ pullback.fst _ _ = φ₂ ∧
        e ≫ f = (μ[t'.A]).left ≫ φ := by
    intro K _ hK x t' φ hF φ₂ h₂
    have hpb := isPullback_square hF.1 φ₂ h₂
    refine ⟨hpb.isoPullback.hom, hpb.isoPullback.inv ≫ (μ[t'.A]).left ≫ φ,
      ⟨hK, t', φ, hF, hpb.isoPullback.hom, inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [IsPullback.isoPullback_hom_fst]; exact h₂
    · exact IsPullback.isoPullback_hom_snd _
    · exact Iso.hom_inv_id_assoc _ _
    · exact IsPullback.isoPullback_hom_fst _
    · exact Iso.hom_inv_id_assoc _ _
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_family_morphism_from_veryDense_graphs R _ _ (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Z ⊗ Z) Z I₂ I M₂ M th₂ th
    (fun h i => p h.1 i.1 * p h.2 i.2) (fun h => p (h.1 + h.2)) Q d G hP₂ hP
    (GlobalTheory.ZM.projRep_projective_ample R _ I₂ _ M₂ th₂ hP₂).2.1 (GlobalTheory.ZM.projRep_projective_ample R _ I _ M th hP).2.1 hsm₂ (by
      rintro K _ x f ⟨hK, t', φ, ⟨hpb, ⟨σ, hE, hσ⟩, -, hl⟩, e, hi, hsq, he, hf⟩
      refine ⟨?_, ?_⟩
      · rw [← cancel_epi e, reassoc_of% hf, reassoc_of% he, hpb.w, Over.w_assoc]
      obtain ⟨N₂, t₂, hN₂, hs₂, hgr⟩ := graph_transport x Z M th M₂ th₂ hP₂.1 hseg t'.A φ _ σ hσ e hsq he f hf
      rw [← hgr]
      have hc : spMap x ≫ spMap β = spMap (x.comp β) := by
        rw [← Spec.map_comp]; rfl
      have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left (fun i => x (p h i)) := by
        intro h
        rw [hσ, ← Over.comp_left_assoc, lift_snd, hl]
        exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R _ _ hP.1 (hp h)).1 K x
      simp only [map_mul]
      clear hgr hf he hsq hi e hl hσ hpb φ
      generalize spMap x ≫ spMap β = s at *
      subst hc
      exact hQ K (x.comp β) t' σ (fun h i => x (p h i)) N₂ t₂ hN₂ hE hs₂ hpt) (by
      intro q r hq hr
      obtain ⟨P, ⟨K, iK, hK, x, t', hx, hsh, hth⟩, hP'⟩ := hVD q r hq hr
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      obtain ⟨φ₂, h₂⟩ := exists_isSquare hφ.1.w
      obtain ⟨e, f, hf, -⟩ := hG K x t' φ hφ φ₂ h₂
      exact ⟨P, ⟨K, iK, x, f, hx, hf⟩, hP'⟩)
  refine ⟨F, fun K _ _ x t' φ hφ φ₂ h₂ => ?_⟩
  obtain ⟨e, f, hf, e₁, e₂⟩ := hG K x t' φ hφ φ₂ h₂
  rw [← e₂, hF K x f hf, reassoc_of% e₁]

end GlobalTheory.ZM.BuildAdd
end
end
