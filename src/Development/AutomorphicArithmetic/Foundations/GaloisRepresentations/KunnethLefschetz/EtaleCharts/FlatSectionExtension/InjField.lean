import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.USelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.homExt :
    ∀ {V X : Scheme.{0}} (a b : V ⟶ X), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι ≫ a = U.ι ≫ b) → a = b := by
  intro V X a b h
  choose W hxW hW using h
  have hcov : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr ?_)
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  exact (V.openCoverOfIsOpenCover W hcov).hom_ext _ _ hW
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appLE_univ_congr_of_eq {V Z : Scheme.{0}} {f g : V ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (e : ⊤ ≤ f ⁻¹ᵁ U) (e' : ⊤ ≤ g ⁻¹ᵁ U) : f.appLE U ⊤ e = g.appLE U ⊤ e' := by
  subst hfg; rfl

private lemma appLE_lift_eq {Y V : Scheme.{0}} (C : Y.Opens) (l : V ⟶ (C : Scheme.{0}))
    (h : ⊤ ≤ (l ≫ C.ι) ⁻¹ᵁ C) : (l ≫ C.ι).appLE C ⊤ h = C.topIso.inv ≫ l.appTop := by
  rw [← Scheme.Hom.appLE_comp_appLE l C.ι C ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  simp
  congr 1

private lemma eq_of_appLE_eq {Y V : Scheme.{0}} (C : Y.Opens) (hC : IsAffineOpen C) (y y' : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (h' : ⊤ ≤ y' ⁻¹ᵁ C) (e : y.appLE C ⊤ h = y'.appLE C ⊤ h') : y = y' := by
  have r : ∀ z : V ⟶ Y, ⊤ ≤ z ⁻¹ᵁ C → Set.range z ⊆ Set.range C.ι := by
    rintro z hz _ ⟨x, rfl⟩
    simpa using hz (Set.mem_univ x)
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ C.ι = y := ⟨_, IsOpenImmersion.lift_fac C.ι y (r y h)⟩
  obtain ⟨l', rfl⟩ : ∃ l, l ≫ C.ι = y' := ⟨_, IsOpenImmersion.lift_fac C.ι y' (r y' h')⟩
  haveI : IsAffine (C : Scheme.{0}) := hC
  rw [appLE_lift_eq, appLE_lift_eq] at e
  have e2 : l.appTop = l'.appTop := (cancel_epi C.topIso.inv).mp e
  rw [ext_of_isAffine e2]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), y ≫ π = y' ≫ π → uV B α k y h = uV B α k y' h' → y = y' := by
  intro K _ W Z Y q i π D d B α k V y y' h h' hπ hu
  have hle := (B.c α).C_le k
  refine eq_of_appLE_eq _ ((B.c α).C_aff k) y y' h h' ?_
  have hpi : ∀ r : Γ(Z, B.V α), (y.appLE _ ⊤ h).hom ((π.appLE (B.V α) _ hle).hom r) =
      (y'.appLE _ ⊤ h').hom ((π.appLE (B.V α) _ hle).hom r) := by
    intro r
    have e1 := Scheme.Hom.appLE_comp_appLE y π (B.V α) ((B.c α).C k) ⊤ hle h
    have e2 := Scheme.Hom.appLE_comp_appLE y' π (B.V α) ((B.c α).C k) ⊤ hle h'
    have e3 := e1.trans ((appLE_univ_congr_of_eq hπ (B.V α) _ _).trans e2.symm)
    exact congrArg (fun t => t.hom r) e3
  have hP := MvPolynomial.ringHom_ext
    (f := (y.appLE _ ⊤ h).hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (g := (y'.appLE _ ⊤ h').hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (fun r => by simpa using hpi r)
    (fun m => by simpa [uV] using congrFun hu m)
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  obtain ⟨P, rfl⟩ := (B.c α).surj k s
  exact congrArg (fun t => t P) hP
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem mem_of_unit {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (hu : IsUnit (uV B β m y h l)) : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := by
  have h1 : V.basicOpen (uV B β m y h l) = ⊤ := Scheme.basicOpen_of_isUnit V hu
  have h2 : V.basicOpen (uV B β m y h l) ≤ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := by
    unfold uV
    rw [Scheme.Hom.appLE]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    exact inf_le_right
  intro x hx
  have h3 : x ∈ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := h2 (h1.ge hx)
  have h4 : y x ∈ Y.basicOpen ((B.c β).u m l) := h3
  rw [← (B.c β).inter m l] at h4
  exact h4.2

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ratioInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (p : V ⟶ W) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c β).C l) (s : (Γ(V, ⊤))ˣ), y ≫ π = p ≫ i → y' ≫ π = p ≫ i → uV B β m y h = (s : Γ(V, ⊤)) • uV B β l y' h' → y = y' := by
  intro K _ W Z Y q i π D d B β m l V y y' p h h' s hy hy' e
  have hl : uV B β m y h l = (s : Γ(V, ⊤)) := by
    have := congrFun e l
    simpa [uSelf B β l y' h'] using this
  have h'' : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := mem_of_unit B β m l y h (hl ▸ s.isUnit)
  have hV : ∀ x : V, (p ≫ i) x ∈ B.V β := by
    intro x
    rw [← hy, Scheme.Hom.comp_apply]
    exact (B.c β).C_le m (h (Set.mem_univ x))
  have hg := gvChart B y p hy β β m l h h'' 1 (locMatOne B β p hV)
  rw [Matrix.one_mulVec] at hg
  obtain ⟨c, hc⟩ : ∃ c : (Γ(V, ⊤))ˣ, uV B β m y h = (c : Γ(V, ⊤)) • uV B β l y h'' := ⟨_, hg⟩
  have hcs : (c : Γ(V, ⊤)) = s := by
    have := congrFun hc l
    rw [hl, Pi.smul_apply, uSelf B β l y h'', smul_eq_mul, mul_one] at this
    exact this.symm
  have hvv : uV B β l y h'' = uV B β l y' h' := by
    funext j
    have h1 := congrFun hc j
    have h2 := congrFun e j
    rw [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [hcs] at h1
    exact s.isUnit.mul_left_cancel (h1.symm.trans h2)
  exact chartInj B β l y y' h'' h' (hy.trans hy'.symm) hvv
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem injKey {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hw : j ≫ π = r ≫ i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}} (p p' : B.ι × Fin d)
    (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hp : ((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B = ((b₁ ≫ tI B j p') ≫ rhoP B j r hw) ≫ cP B)
    (hG : GMat B ((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ((b₁ ≫ tI B j p') ≫ rhoP B j r hw) M)
    (u : (Γ(V, ⊤))ˣ)
    (hyp : M.mulVec ((a₁ ≫ tI B j p).appTop.hom ∘ v) = (u : Γ(V, ⊤)) • ((b₁ ≫ tI B j p').appTop.hom ∘ v))
    (m : Fin d) (hm : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C m) :
    (a₁ ≫ tI B j p) ≫ eP B j ≫ j = (b₁ ≫ tI B j p') ≫ eP B j ≫ j := by
  obtain ⟨h₁, e₁, -, r₁⟩ := pieceFacts B j r hw v hv p a₁
  obtain ⟨h₂, e₂, -, r₂⟩ := pieceFacts B j r hw v hv p' b₁
  have hL := gMatLoc B _ _ M p.1 p'.1 _ _ r₁ r₂ hG
  have hc := (coverComm B j r hw).1
  have hy : ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B) ≫ i := by
    rw [Category.assoc (a₁ ≫ tI B j p) (rhoP B j r hw) (cP B), hc]
    simp only [Category.assoc, hw]
  have hy' : ((b₁ ≫ tI B j p') ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B) ≫ i := by
    rw [hp, Category.assoc (b₁ ≫ tI B j p') (rhoP B j r hw) (cP B), hc]
    simp only [Category.assoc, hw]
  have hg := gvChart B _ _ hy p.1 p'.1 p.2 m h₁ hm M hL
  rw [e₁, e₂, hg] at hyp
  refine ratioInj B p'.1 m p'.2 _ _ _ hm h₂ ((D.u _ _ ((secOf_f B p.1 p.2 _ h₁).trans (secOf_f B p'.1 m _ hm).symm)) * u) hy hy' ?_
  rw [Units.val_mul, mul_smul, ← hyp, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.injField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (a ≫ rhoP B j r hsq.w) ≫ cP B = (b ≫ rhoP B j r hsq.w) ≫ cP B → GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M → ∀ u : (Γ(V, ⊤))ˣ, M.mulVec (a.appTop.hom ∘ v) = (u : Γ(V, ⊤)) • (b.appTop.hom ∘ v) → a ≫ eP B j = b ≫ eP B j := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a b M hp hG u hyp
  have hc := (coverComm B j r hsq.w).1
  have hrr : a ≫ eP B j ≫ r = b ≫ eP B j ≫ r := by
    have h := hp
    simp only [Category.assoc] at h
    rwa [hc] at h
  have hππ : (a ≫ eP B j ≫ j) ≫ π = (b ≫ eP B j ≫ j) ≫ π := by
    simp only [Category.assoc, hsq.w]
    simp only [← Category.assoc] at hrr ⊢
    rw [hrr]
  refine hsq.hom_ext ?_ (by simpa only [Category.assoc] using hrr)
  refine homExt _ _ fun x => ?_
  obtain ⟨U₁, p, a₁, hx₁, ha⟩ := sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) a x
  obtain ⟨U₂, p', b₁, hx₂, hb⟩ := sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) b x

  have hbx : (b ≫ eP B j ≫ j) x ∈ (B.c p'.1).C p'.2 := by
    obtain ⟨h₂, -, -, -⟩ := pieceFacts B j r hsq.w v hv p' b₁
    have h3 : ((b₁ ≫ tI B j p') ≫ eP B j ≫ j) (⟨x, hx₂⟩ : U₂) ∈ (B.c p'.1).C p'.2 := h₂ (Set.mem_univ _)
    have h4 : b₁ ≫ tI B j p' = U₂.ι ≫ b := hb.symm
    rw [h4] at h3
    have h6 : ((U₂.ι ≫ b) ≫ eP B j ≫ j) (⟨x, hx₂⟩ : U₂) = (b ≫ eP B j ≫ j) x := by
      rw [Category.assoc, Scheme.Hom.comp_apply]
      rfl
    rwa [h6] at h3
  have hπx : π ((a ≫ eP B j ≫ j) x) ∈ B.V p'.1 := by
    have h5 : π ((a ≫ eP B j ≫ j) x) = π ((b ≫ eP B j ≫ j) x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hππ]
    rw [h5]
    exact (B.c p'.1).C_le p'.2 hbx
  obtain ⟨m, hmx⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c p'.1).C_cover hπx)
  let U₃ : V.Opens := (a ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C m
  let U : V.Opens := U₁ ⊓ U₂ ⊓ U₃
  have hxU : x ∈ U := ⟨⟨hx₁, hx₂⟩, hmx⟩
  have l₁ : U ≤ U₁ := inf_le_left.trans inf_le_left
  have l₂ : U ≤ U₂ := inf_le_left.trans inf_le_right
  have l₃ : U ≤ U₃ := inf_le_right
  have ea : U.ι ≫ a = (V.homOfLE l₁ ≫ a₁) ≫ tI B j p := by
    have h : a₁ ≫ tI B j p = U₁.ι ≫ a := ha.symm
    rw [Category.assoc, h, Scheme.homOfLE_ι_assoc]
  have eb : U.ι ≫ b = (V.homOfLE l₂ ≫ b₁) ≫ tI B j p' := by
    have h : b₁ ≫ tI B j p' = U₂.ι ≫ b := hb.symm
    rw [Category.assoc, h, Scheme.homOfLE_ι_assoc]
  refine ⟨U, hxU, ?_⟩
  have hk := injKey B j r hsq.w v hv p p' (V.homOfLE l₁ ≫ a₁) (V.homOfLE l₂ ≫ b₁) (M.map U.ι.appTop.hom)
    (by rw [← ea, ← eb]; simp only [Category.assoc]; simp only [Category.assoc] at hp; rw [hp])
    (by
      rw [← ea, ← eb]
      have h := gMatNat B U.ι _ _ M hG
      simpa only [Category.assoc] using h)
    (Units.map (U.ι.appTop.hom : Γ(V, ⊤) →+* Γ((U : Scheme.{0}), ⊤)).toMonoidHom u)
    (by
      rw [← ea, ← eb]
      have hca : ∀ (c : V ⟶ TP B j), (U.ι ≫ c).appTop.hom ∘ v = U.ι.appTop.hom ∘ (c.appTop.hom ∘ v) := by
        intro c
        funext n
        rw [Scheme.Hom.comp_appTop]
        rfl
      rw [hca a, hca b]
      funext n
      have h2 := congrArg (U.ι.appTop.hom : Γ(V, ⊤) →+* Γ((U : Scheme.{0}), ⊤)) (congrFun hyp n)
      rw [RingHom.map_mulVec] at h2
      refine h2.trans ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Function.comp_apply]
      rfl)
    m
    (by
      rw [← ea, Category.assoc U.ι a]
      intro z _
      exact l₃ z.2)
  rw [← ea, ← eb] at hk
  simpa only [Category.assoc] using hk
end
