import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem comp_ap {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C) (x : A) :
    (u ≫ v) x = v (u x) := by simp

private def lvlIso {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) :
    yoneda.obj (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)) ≅
      widePullback (yoneda.obj Y) (fun _ : Fin (p + 1) => yoneda.obj V)
        (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan
      (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f) ⋙ yoneda))

private theorem lvlIso_base {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) :
    (lvlIso f p).hom ≫ WidePullback.base (fun _ : Fin (p + 1) => yoneda.map f) =
      yoneda.map (WidePullback.base (fun _ : Fin (p + 1) => f)) := by
  have h := HasLimit.isoOfNatIso_hom_π (WidePullbackShape.diagramIsoWideCospan
    (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f) ⋙ yoneda)) none
  have h2 := preservesLimitIso_hom_π yoneda
    (WidePullbackShape.wideCospan Y (fun _ : Fin (p + 1) => V) (fun _ => f)) none
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h.trans (Category.comp_id _))).trans h2)

private theorem piece_open {V Y : Scheme.{0}} (f : V ⟶ Y) (p : ℕ) {T : Fin (p + 1) → Scheme.{0}}
    (j : ∀ i, T i ⟶ V) (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, IsOpenImmersion (j i ≫ f))
    (O : (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)).Opens)
    (hO : (O : Set _) = ⋂ i, (WidePullback.π (fun _ : Fin (p + 1) => f) i) ⁻¹' Set.range (j i)) :
    IsOpenImmersion (O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f)) := by
  have hb : ∀ (i : Fin (p + 1)) z, (WidePullback.base (fun _ : Fin (p + 1) => f)) z =
      f ((WidePullback.π (fun _ : Fin (p + 1) => f) i) z) := by
    intro i z
    rw [← comp_ap, WidePullback.π_arrow]
  have hxO : ∀ (x : O.toScheme) (i : Fin (p + 1)),
      (WidePullback.π (fun _ : Fin (p + 1) => f) i) (O.ι x) ∈ Set.range (j i) := by
    intro x i
    have hx : O.ι x ∈ (O : Set _) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    rw [hO] at hx
    exact Set.mem_iInter.1 hx i
  let W : Y.Opens := ⟨⋂ i, Set.range (j i ≫ f),
    isOpen_iInter_of_finite fun i => (j i ≫ f).opensRange.2⟩
  have hW : ∀ (w : W.toScheme) (i : Fin (p + 1)), W.ι w ∈ Set.range (j i ≫ f) := by
    intro w i
    have hw : W.ι w ∈ (W : Set _) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
    exact Set.mem_iInter.1 hw i
  have hr : Set.range (O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine Set.mem_iInter.2 fun i => ?_
    obtain ⟨y, hy⟩ := hxO x i
    exact ⟨y, by rw [comp_ap, hy, comp_ap, hb i]⟩
  let r := IsOpenImmersion.lift W.ι _ hr
  have hl : ∀ i, Set.range W.ι ⊆ Set.range (j i ≫ f) := by
    rintro i _ ⟨w, rfl⟩
    exact hW w i
  let l : ∀ i, W.toScheme ⟶ T i := fun i => IsOpenImmersion.lift (j i ≫ f) W.ι (hl i)
  have hlf : ∀ i, l i ≫ j i ≫ f = W.ι := fun i => IsOpenImmersion.lift_fac _ _ _
  let L : W.toScheme ⟶ widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f) :=
    WidePullback.lift W.ι (fun i => l i ≫ j i) (fun i => by simpa using hlf i)
  have hLπ : ∀ i, L ≫ WidePullback.π (fun _ : Fin (p + 1) => f) i = l i ≫ j i :=
    fun i => WidePullback.lift_π _ _ _ _ i
  have hLb : L ≫ WidePullback.base (fun _ : Fin (p + 1) => f) = W.ι :=
    WidePullback.lift_base _ _ _ _
  have hs : Set.range L ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι, hO]
    rintro _ ⟨w, rfl⟩
    refine Set.mem_iInter.2 fun i => ?_
    refine ⟨l i w, ?_⟩
    have := congr($(hLπ i) w)
    rw [comp_ap, comp_ap] at this
    exact this.symm
  let s := IsOpenImmersion.lift O.ι L hs
  have hsO : s ≫ O.ι = L := IsOpenImmersion.lift_fac _ _ _
  have hrW : r ≫ W.ι = O.ι ≫ WidePullback.base (fun _ : Fin (p + 1) => f) :=
    IsOpenImmersion.lift_fac _ _ _
  have hm : ∀ i, Set.range (O.ι ≫ WidePullback.π (fun _ : Fin (p + 1) => f) i) ⊆
      Set.range (j i) := by
    rintro i _ ⟨x, rfl⟩
    rw [comp_ap]
    exact hxO x i
  have hrs : r ≫ s = 𝟙 _ := by
    rw [← cancel_mono O.ι, Category.assoc, hsO, Category.id_comp]
    apply WidePullback.hom_ext
    · intro i
      rw [Category.assoc, hLπ, ← IsOpenImmersion.lift_fac (j i) _ (hm i), ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i ≫ f), Category.assoc, hlf, hrW,
        IsOpenImmersion.lift_fac_assoc, Category.assoc, WidePullback.π_arrow]
    · rw [Category.assoc, hLb, hrW]
  have hsr : s ≫ r = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, hrW, ← Category.assoc, hsO, hLb, Category.id_comp]
  have : IsIso r := ⟨s, hrs, hsr⟩
  rw [← hrW]
  infer_instance

theorem UpperTheory.cech_nerve_representable_disjoint :
    ∀ {V Y : Scheme.{0}} (f : V ⟶ Y), (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) → ∀ p : ℕ, ∃ (Z : Scheme.{0}) (g : Z ⟶ Y) (e : yoneda.obj Z ≅ (cech f).obj (op (SimplexCategory.mk p))),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk p)) = yoneda.map g ∧ (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : Z, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ g)) := by
  rintro V Y f ⟨ι, O, j, hj, hd, hc, hf⟩ p
  let π := fun i => WidePullback.π (fun _ : Fin (p + 1) => f) i
  let U : (Fin (p + 1) → ι) → (widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f)).Opens :=
    fun a => ⟨⋂ i, (π i) ⁻¹' Set.range (j (a i)),
      isOpen_iInter_of_finite fun i => (j (a i)).opensRange.2.preimage (π i).continuous⟩
  have hU : ∀ a z, z ∈ Set.range (U a).ι ↔ ∀ i, (π i) z ∈ Set.range (j (a i)) := by
    intro a z
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter
  refine ⟨widePullback Y (fun _ : Fin (p + 1) => V) (fun _ => f),
    WidePullback.base (fun _ : Fin (p + 1) => f), lvlIso f p,
    lvlIso_base f p, Fin (p + 1) → ι, fun a => (U a).toScheme, fun a => (U a).ι,
    fun a => inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
    refine Set.disjoint_left.2 fun z hza hzb => ?_
    exact Set.disjoint_left.1 (hd _ _ hi) ((hU a z).1 hza i) ((hU b z).1 hzb i)
  · intro z
    choose a ha using fun i => hc ((π i) z)
    exact ⟨a, (hU a z).2 ha⟩
  · intro a
    exact piece_open f p (fun i => j (a i)) (fun i => hj _) (fun i => hf _) (U a) rfl

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

private theorem cechNerve_level_isPullback {C : Type*} [Category C] {a b : Arrow C}
    [∀ n : ℕ, HasWidePullback a.right (fun _ : Fin (n + 1) => a.left) fun _ => a.hom]
    [∀ n : ℕ, HasWidePullback b.right (fun _ : Fin (n + 1) => b.left) fun _ => b.hom]
    (F : a ⟶ b) (h : IsPullback F.left a.hom b.hom F.right) (n : SimplexCategoryᵒᵖ) :
    IsPullback ((Arrow.mapCechNerve F).app n) (WidePullback.base _) (WidePullback.base _) F.right := by
  have hc : (Arrow.mapCechNerve F).app n ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right := by
    simp [Arrow.mapCechNerve]
  refine ⟨⟨hc⟩, ⟨PullbackCone.IsLimit.mk hc
    (fun s => WidePullback.lift s.snd
      (fun i => h.lift (s.fst ≫ WidePullback.π _ i) s.snd (by
        simp only [Category.assoc, WidePullback.π_arrow]
        simpa using s.condition)) (by simp)) ?_ ?_ ?_⟩⟩
  · intro s
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp [Arrow.mapCechNerve]
    · simpa [Arrow.mapCechNerve] using s.condition.symm
  · intro s
    simp
  · intro s m h1 h2
    refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
    · simp only [WidePullback.lift_π]
      refine h.hom_ext ?_ ?_
      · rw [h.lift_fst, ← h1]
        simp [Arrow.mapCechNerve]
      · rw [h.lift_snd, ← h2, Category.assoc]
        simp
    · simpa using h2

private theorem comp_eq_of_comp_inv {C : Type*} [Category C] {A B D E : C} {i : A ⟶ B} {ψ : B ⟶ D} {t : A ⟶ E}
    (e : E ≅ D) (h : i ≫ ψ ≫ e.inv = t) : i ≫ ψ = t ≫ e.hom := by
  rw [← h]
  simp

theorem UpperTheory.cech_nerve_restrict_open :
    ∀ {V Y : Scheme.{0}} (f : V ⟶ Y) (W : Y.Opens), ∃ ψ : cech (f ∣_ W) ⟶ cech f, ψ ≫ cechAug f = cechAug (f ∣_ W) ≫ sch.map W.ι ∧
      ∀ (p : ℕ) (Z : Scheme.{0}) (g : Z ⟶ Y) (e : yoneda.obj Z ≅ (cech f).obj (op (SimplexCategory.mk p))), e.hom ≫ (cechAug f).app (op (SimplexCategory.mk p)) = yoneda.map g →
        ∃ e' : yoneda.obj (g ⁻¹ᵁ W : Scheme.{0}) ≅ (cech (f ∣_ W)).obj (op (SimplexCategory.mk p)), e'.hom ≫ ψ.app (op (SimplexCategory.mk p)) = yoneda.map (g ⁻¹ᵁ W).ι ≫ e.hom := by
  intro V Y f W
  have hP0 := isPullback_morphismRestrict f W
  have hP1 := hP0.map yoneda
  let F : Arrow.mk (yoneda.map (f ∣_ W)) ⟶ Arrow.mk (yoneda.map f) :=
    Arrow.homMk (yoneda.map (f ⁻¹ᵁ W).ι) (yoneda.map W.ι) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, morphismRestrict_ι])
  have hF : IsPullback F.left (Arrow.mk (yoneda.map (f ∣_ W))).hom (Arrow.mk (yoneda.map f)).hom F.right :=
    hP1.flip
  have hL := cechNerve_level_isPullback F hF
  refine ⟨Arrow.mapCechNerve F, ?_, ?_⟩
  · exact NatTrans.ext (funext fun n => (hL n).w)
  · intro p Z g e he
    have hA := ((isPullback_morphismRestrict g W).map yoneda).flip
    have hL' : IsPullback ((Arrow.mapCechNerve F).app (op (SimplexCategory.mk p)) ≫ e.inv)
        ((cechAug (f ∣_ W)).app (op (SimplexCategory.mk p))) (yoneda.map g) (yoneda.map W.ι) :=
      IsPullback.of_iso (hL (op (SimplexCategory.mk p))) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp; rfl) (by
          simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
          exact (Iso.eq_inv_comp e).2 he) (by simp; rfl)
    refine ⟨hA.isoIsPullback _ _ hL', ?_⟩
    have h1 := hA.isoIsPullback_hom_fst _ _ hL'
    exact comp_eq_of_comp_inv e h1

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_mono {R : Type} [CommRing R] {F : Shv R} {c c' : ℤ} (h : c' ≤ c) {E E' : Spc} {f : E ⟶ E'}
    (hf : Conn R F c f) : Conn R F c' f :=
  fun n => ⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩

private theorem conn_square {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {E₁ E₂ E₃ E₄ : Spc} {u : E₁ ⟶ E₂}
    {v : E₃ ⟶ E₄} {a : E₁ ⟶ E₃} {b : E₂ ⟶ E₄} (w : u ≫ b = a ≫ v) (ha : Eqv R a F) (hb : Eqv R b F)
    (hu : Conn R F c u) : Conn R F c v := by
  have key : ∀ (n : ℤ) (x : H R E₄ F n), pull R a F n (pull R v F n x) = pull R u F n (pull R b F n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, w]
  have inj : ∀ n : ℤ, Function.Injective (pull R u F n) → Function.Injective (pull R v F n) := by
    intro n hi x y h
    exact (hb n).1 (hi ((key n x).symm.trans ((congrArg _ h).trans (key n y))))
  have sur : ∀ n : ℤ, Function.Surjective (pull R u F n) → Function.Surjective (pull R v F n) := by
    intro n hs y
    obtain ⟨z, hz⟩ := hs (pull R a F n y)
    obtain ⟨x, rfl⟩ := (hb n).2 z
    exact ⟨x, (ha n).1 ((key n x).trans hz)⟩
  intro n
  exact ⟨fun hn => ⟨inj n ((hu n).1 hn).1, sur n ((hu n).1 hn).2⟩, fun hn => inj n ((hu n).2 hn)⟩

private theorem eqv_of_iso {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

private theorem conn_level {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {P Q : PSh} (ψ : P ⟶ Q) {Z Z' : Scheme.{0}}
    (k : Z' ⟶ Z) (e : yoneda.obj Z ≅ Q) (e' : yoneda.obj Z' ≅ P) (h : e'.hom ≫ ψ = yoneda.map k ≫ e.hom)
    (hk : Conn R F c (sch.map k)) : Conn R F c (disc.map ψ) := by
  refine conn_square (u := sch.map k) (a := (disc.mapIso e').hom) (b := (disc.mapIso e).hom) ?_
    (eqv_of_iso _) (eqv_of_iso _) hk
  change disc.map (yoneda.map k) ≫ disc.map e.hom = disc.map e'.hom ≫ disc.map ψ
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem cech_zero {V Y : Scheme.{0}} (f : V ⟶ Y) :
    ∃ e : yoneda.obj V ≅ (cech f).obj (op (SimplexCategory.mk 0)),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk 0)) = yoneda.map f := by
  let π₀ : Fin 1 → (yoneda.obj V ⟶ yoneda.obj Y) := fun _ => yoneda.map f
  let h : yoneda.obj V ⟶ widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ :=
    WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  let k : widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ ⟶ yoneda.obj V :=
    WidePullback.π π₀ 0
  have hk : h ≫ k = 𝟙 _ := WidePullback.lift_π _ _ _ _ _
  have hb : h ≫ WidePullback.base π₀ = yoneda.map f := WidePullback.lift_base _ _ _ _
  have kh : k ≫ h = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [Category.assoc, Category.id_comp]
      change k ≫ h ≫ k = k
      rw [hk, Category.comp_id]
    · rw [Category.assoc, hb, Category.id_comp]
      exact WidePullback.π_arrow π₀ 0
  exact ⟨⟨h, k, hk, kh⟩, hb⟩

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_cover {V Y : Scheme.{0}} (f : V ⟶ Y)
    (hcov : ∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) :
    Smooth f := by
  obtain ⟨ι, O, j, hj, -, hc, hf⟩ := hcov
  let 𝒰 : V.OpenCover := Scheme.Cover.mkOfCovers ι O j (fun y => by
    obtain ⟨a, x, hx⟩ := hc y
    exact ⟨a, x, hx⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun a => ?_
  have := hf a
  change Smooth (j a ≫ f)
  infer_instance

theorem UpperTheory.connectivity_of_cech_disjoint_cover :
    LeafLevel → A1 → A2 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {V Y : Scheme.{0}} (f : V ⟶ Y) [Surjective f], (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) → ∀ W : Y.Opens,
      Conn R F c (sch.map (f ⁻¹ᵁ W).ι) → (∀ (Z : Scheme.{0}) (g : Z ⟶ Y), (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : Z, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ g)) → Conn R F (c - 1) (sch.map (g ⁻¹ᵁ W).ι)) → Conn R F c (sch.map W.ι) := by
  intro hL a1 a2 R _ F c V Y f _ hcov W h0 hp
  obtain ⟨ψ, hψ, hlev⟩ := UpperTheory.cech_nerve_restrict_open f W
  have hsm : Smooth f := smooth_of_cover f hcov
  have hsmW : Smooth (f ∣_ W) := MorphismProperty.of_isPullback (P := @Smooth) (isPullback_morphismRestrict f W).flip hsm
  have hsuW : Surjective (f ∣_ W) := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict f W).flip inferInstance
  have eV := a2 R f F
  have eW := a2 R (f ∣_ W) F
  have hψc : Conn R F c ψ := by
    refine hL a1 R F c ψ fun p => ?_
    rcases p with _ | p
    · obtain ⟨e, he⟩ := cech_zero f
      obtain ⟨e', he'⟩ := hlev 0 V f e he
      have h0' : Conn R F (c - ((0 : ℕ) : ℤ)) (sch.map (f ⁻¹ᵁ W).ι) := by simpa using h0
      exact conn_level _ _ e e' he' h0'
    · obtain ⟨Z, g, e, hg, hc⟩ := UpperTheory.cech_nerve_representable_disjoint f hcov (p + 1)
      obtain ⟨e', he'⟩ := hlev (p + 1) Z g e hg
      exact conn_level _ _ e e' he' (conn_mono (by push_cast; omega) (hp Z g hc))
  exact conn_square hψ eW eV hψc

end
end
