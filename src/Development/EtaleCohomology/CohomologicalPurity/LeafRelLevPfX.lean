import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (i : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R i.hom F n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R i.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, i.inv_hom_id, pull_id]
  · rw [← pull_comp, i.hom_inv_id, pull_id]

theorem eqv_of_arrowIso (R : Type) [CommRing R] {E' E G' G : Spc} {f : E' ⟶ E} {g : G' ⟶ G} (F : Shv R)
    (e : Arrow.mk f ≅ Arrow.mk g) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have w : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  have k : (pull R e.hom.left F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R e.hom.right F n) := by
    funext x
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, w]
  have hl : Function.Bijective (pull R e.hom.left F n) :=
    pull_iso_bij R ((Arrow.leftFunc).mapIso e) F n
  have hr : Function.Bijective (pull R e.hom.right F n) :=
    pull_iso_bij R ((Arrow.rightFunc).mapIso e) F n
  have hc : Function.Bijective ((pull R e.hom.left F n) ∘ (pull R g F n)) := by
    rw [k]; exact (hf n).comp hr
  exact (Function.Bijective.of_comp_iff' hl _).mp hc

theorem eqv_sum_RRelH (hS : LeafSum) (R : Type) [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E') (c : Cofan E)
    (hc' : Nonempty (IsColimit c')) (hc : Nonempty (IsColimit c)) (f : ∀ a, E' a ⟶ E a) (φ : c'.pt ⟶ c.pt)
    (hφ : ∀ a, c'.inj a ≫ φ = f a ≫ c.inj a) (hf : ∀ a, Eqv R (f a) F) : Eqv R φ F := by
  intro n
  have k : (fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n) =
      (fun (z : ∀ a, H R (E a) F n) (a : A) => pull R (f a) F n (z a)) ∘
        (fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hφ]
  have h1 := hS R F A E' c' hc' n
  have h2 := hS R F A E c hc n
  have hc3 : Function.Bijective ((fun (y : H R c'.pt F n) (a : A) => pull R (c'.inj a) F n y) ∘ (pull R φ F n)) := by
    rw [k]
    exact (Function.Bijective.piMap (fun a => hf a n)).comp h2
  exact (Function.Bijective.of_comp_iff' h1 _).mp hc3

def LeafRelLev : Prop := LeafLevel → ∀ (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) (h' : (hocF J).map α ≫ aug c hc = aug c' hc')
  (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (ι : A → J) (E' E : A → Spc) (k' : Cofan E') (k : Cofan E) (f : ∀ a, E' a ⟶ E a) (φ : k'.pt ⟶ k.pt),
    Nonempty (IsColimit k') ∧ Nonempty (IsColimit k) ∧ (∀ a, k'.inj a ≫ φ = f a ≫ k.inj a) ∧
    (∀ a, Nonempty (Arrow.mk (pbRel (disc.map g) (disc.map (α.app (ι a))) (disc.map (c' (ι a))) (disc.map (c (ι a)))
      (h (ι a))) ≅ Arrow.mk (f a))) ∧
    Nonempty (Arrow.mk φ ≅ Arrow.mk (disc.map ((pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').app n)))

theorem LeafRelHoc_of (hL : LeafLevel) (hS : LeafSum) (hB : LeafRelLev) : LeafRelHoc := by
  intro hA3 R _ F J _ D' D α Y G g c' c hc' hc h h' hE
  apply hA3
  intro n
  obtain ⟨A, ι, E', E, k', k, f, φ, h1, h2, h3, h4, ⟨e⟩⟩ := hB hL J D' D α Y G g c' c hc' hc h h' n
  refine eqv_of_arrowIso R F e ?_
  exact eqv_sum_RRelH hS R F k' k h1 h2 f φ h3 fun a => eqv_of_arrowIso R F (h4 a).some (hE (ι a))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

instance discPL : PreservesLimitsOfSize.{0, 0} disc :=
  inferInstanceAs (PreservesLimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))
instance discPC : PreservesColimitsOfSize.{0, 0} disc :=
  inferInstanceAs (PreservesColimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))

def pbMapIso {C D : Type*} [Category C] [Category D] (Fn : C ⥤ D) {B G A' A : C} (g : G ⟶ B) (a : A' ⟶ A)
    (π' : A' ⟶ B) (π : A ⟶ B) (h : a ≫ π = π') [HasPullback π' g] [HasPullback π g]
    [HasPullback (Fn.map π') (Fn.map g)] [HasPullback (Fn.map π) (Fn.map g)]
    [PreservesLimit (cospan π' g) Fn] [PreservesLimit (cospan π g) Fn] :
    Arrow.mk (Fn.map (pullback.map π' g π g a (𝟙 _) (𝟙 _) (by simp [h]) (by simp))) ≅
    Arrow.mk (pullback.map (Fn.map π') (Fn.map g) (Fn.map π) (Fn.map g) (Fn.map a) (𝟙 _) (𝟙 _)
      (by simp [← Fn.map_comp, h]) (by simp)) :=
  Arrow.isoMk (PreservesPullback.iso Fn π' g) (PreservesPullback.iso Fn π g) (by
    apply pullback.hom_ext
    · simp only [Arrow.mk_hom, Category.assoc, pullback.lift_fst, PreservesPullback.iso_hom_fst,
        PreservesPullback.iso_hom_fst_assoc, ← Fn.map_comp]
    · simp only [Arrow.mk_hom, Category.assoc, pullback.lift_snd, PreservesPullback.iso_hom_snd, ← Fn.map_comp, Category.comp_id])

theorem types_pb {A : Type} {E : A → Type} {P Y G : Type} (ι : ∀ a, E a ⟶ P) (hP : Nonempty (IsColimit (Cofan.mk P ι)))
    (p : P ⟶ Y) (g : G ⟶ Y) (e : ∀ a, E a ⟶ Y) (he : ∀ a, ι a ≫ p = e a)
    {Q : Type} (fst : Q ⟶ P) (snd : Q ⟶ G) (w : fst ≫ p = snd ≫ g) (hQ : IsLimit (PullbackCone.mk fst snd w))
    {Q' : A → Type} (fst' : ∀ a, Q' a ⟶ E a) (snd' : ∀ a, Q' a ⟶ G) (w' : ∀ a, fst' a ≫ e a = snd' a ≫ g)
    (hQ' : ∀ a, IsLimit (PullbackCone.mk (fst' a) (snd' a) (w' a)))
    (j : ∀ a, Q' a ⟶ Q) (hj1 : ∀ a, j a ≫ fst = fst' a ≫ ι a) (hj2 : ∀ a, j a ≫ snd = snd' a) :
    Nonempty (IsColimit (Cofan.mk Q j)) := by
  rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma] at hP ⊢
  have J1 : ∀ a y, fst (j a y) = ι a (fst' a y) := fun a y => ConcreteCategory.congr_hom (hj1 a) y
  have J2 : ∀ a y, snd (j a y) = snd' a y := fun a y => ConcreteCategory.congr_hom (hj2 a) y
  constructor
  · rintro ⟨a, y⟩ ⟨b, z⟩ hyz
    have hyz' : j a y = j b z := hyz
    have h1 : ι a (fst' a y) = ι b (fst' b z) := by rw [← J1, ← J1, hyz']
    have h2 : snd' a y = snd' b z := by rw [← J2, ← J2, hyz']
    have h3 := hP.1 (a₁ := ⟨a, fst' a y⟩) (a₂ := ⟨b, fst' b z⟩) h1
    obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.mp h3
    have h4' : fst' a y = fst' a z := eq_of_heq h4
    have : y = z := PullbackCone.IsLimit.type_ext (hQ' a) h4' h2
    subst this; rfl
  · intro q
    obtain ⟨⟨a, u⟩, hu⟩ := hP.2 (fst q)
    have hu' : ι a u = fst q := hu
    have hc : e a u = g (snd q) := by
      rw [← ConcreteCategory.congr_hom (he a) u]
      change p (ι a u) = g (snd q)
      rw [hu']
      exact ConcreteCategory.congr_hom w q
    let y : Q' a := (PullbackCone.IsLimit.equivPullbackObj (hQ' a)).symm ⟨(u, snd q), hc⟩
    have y1 : fst' a y = u := PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (hQ' a) _
    have y2 : snd' a y = snd q := PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (hQ' a) _
    refine ⟨⟨a, y⟩, ?_⟩
    change j a y = q
    refine PullbackCone.IsLimit.type_ext hQ ?_ ?_
    · change fst (j a y) = fst q
      rw [J1, y1, hu']
    · change snd (j a y) = snd q
      rw [J2, y2]

theorem psh_pb {A : Type} {E : A → PSh} {P Y G : PSh} (ι : ∀ a, E a ⟶ P) (hP : Nonempty (IsColimit (Cofan.mk P ι)))
    (p : P ⟶ Y) (g : G ⟶ Y) (e : ∀ a, E a ⟶ Y) (he : ∀ a, ι a ≫ p = e a) :
    Nonempty (IsColimit (Cofan.mk (pullback p g) fun a =>
      pullback.map (e a) g p g (ι a) (𝟙 _) (𝟙 _) (by simp [he]) (by simp))) := by
  obtain ⟨hP⟩ := hP
  refine ⟨evaluationJointlyReflectsColimits _ fun U => (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_⟩
  have hPU := isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj U) _ _ hP
  have hQ := isLimitPullbackConeMapOfIsLimit ((evaluation _ _).obj U) pullback.condition (pullbackIsPullback p g)
  have hQ' := fun a => isLimitPullbackConeMapOfIsLimit ((evaluation _ _).obj U) pullback.condition
    (pullbackIsPullback (e a) g)
  exact (types_pb _ ⟨hPU⟩ _ _ _ (fun a => congrArg (fun t => NatTrans.app t U) (he a)) _ _ _ hQ _ _ _ hQ' _
    (fun a => by rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst])
    (fun a => by rw [← Functor.map_comp, pullback.lift_snd, Category.comp_id])).some

theorem inj_aug_RRelL {J : Type} [SmallCategory J] {Y : PSh} (Dx : J ⥤ PSh) (cx : ∀ j, Dx.obj j ⟶ Y) (hcx : Coc Dx cx)
    (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : inj Dx n σ ≫ (aug cx hcx).app n = cx (σ.obj 0) := by
  ext U x
  have e : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1))) : (0 : Fin _) ⟶ 0) = 𝟙 _ := Subsingleton.elim _ _
  change (cx (σ.obj 0)).app U ((Dx.map (σ.map (homOfLE (Fin.zero_le 0)))).app U x) = (cx (σ.obj 0)).app U x
  rw [e, σ.map_id, Dx.map_id]; rfl

theorem inj_nat {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  exact mkChn_congr (F := D.flip.obj U) σ
    (funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x) _ _

theorem LeafRelLev_of : LeafRelLev := by
  intro hL J _ D' D α Y G g c' c hc' hc h h' n
  have hj : ∀ j, α.app j ≫ c j = c' j := fun j => congrArg (fun t => NatTrans.app t (op (SimplexCategory.mk 0))) (h j)
  have hn : ((hocF J).map α).app n ≫ (aug c hc).app n = (aug c' hc').app n := congrArg (fun t => NatTrans.app t n) h'
  refine ⟨Fin (n.unop.len + 1) ⥤ J, fun σ => σ.obj 0, fun σ => disc.obj (pullback (c' (σ.obj 0)) g),
    fun σ => disc.obj (pullback (c (σ.obj 0)) g),
    Cofan.mk (disc.obj (pullback ((aug c' hc').app n) g)) (fun σ => disc.map (pullback.map _ _ _ _ (inj D' n σ)
      (𝟙 _) (𝟙 _) (by simp [inj_aug_RRelL]) (by simp))),
    Cofan.mk (disc.obj (pullback ((aug c hc).app n) g)) (fun σ => disc.map (pullback.map _ _ _ _ (inj D n σ)
      (𝟙 _) (𝟙 _) (by simp [inj_aug_RRelL]) (by simp))),
    fun σ => disc.map (pullback.map _ _ _ _ (α.app (σ.obj 0)) (𝟙 _) (𝟙 _) (by simp [hj]) (by simp)),
    disc.map (pullback.map _ _ _ _ (((hocF J).map α).app n) (𝟙 _) (𝟙 _) (by simp [hn]) (by simp)),
    ⟨isColimitCofanMkObjOfIsColimit disc _ _ (psh_pb _ (hL J D' n) _ g _ (inj_aug_RRelL D' c' hc' n)).some⟩,
    ⟨isColimitCofanMkObjOfIsColimit disc _ _ (psh_pb _ (hL J D n) _ g _ (inj_aug_RRelL D c hc n)).some⟩, ?_, ?_, ?_⟩
  · intro σ
    change disc.map _ ≫ disc.map _ = disc.map _ ≫ disc.map _
    rw [← disc.map_comp, ← disc.map_comp]
    congr 1
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.comp_id]
    rw [inj_nat]
  · intro σ
    exact ⟨(pbMapIso disc g (α.app (σ.obj 0)) (c' (σ.obj 0)) (c (σ.obj 0)) (hj _)).symm⟩
  · exact ⟨disc.mapArrow.mapIso (pbMapIso ((evaluation _ _).obj n) (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').symm⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end
