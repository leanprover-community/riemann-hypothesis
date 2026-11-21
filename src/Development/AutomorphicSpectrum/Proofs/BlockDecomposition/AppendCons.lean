import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}

def pairU (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) :
    CH.Pairing (W.ι ⋙ F₁) (W.ι ⋙ F₂) (W.ι ⋙ F₃) :=
  ⟨fun T => P.μ T.obj, fun φ => P.nat φ.hom⟩


def incl (F : C ⥤ ModuleCat.{0} R) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q) :
    Cx.Hom (RC F W hQ) (CH.cx (W.ι ⋙ F)) (RingHom.id R) :=
  ⟨fun n => Submodule.subtype _, fun _ _ => rfl⟩

theorem cup_mem_rel (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    {p n m : ℕ} (h : p + n = m) (b : CH.Cn (W.ι ⋙ F₁) p) (x : (RC F₂ W hQ).X n) :
    (pairU P W).cupC h b x.1 ∈ relS (W.ι ⋙ F₃) (fun T => Q T.obj) m := by
  intro s hs
  have hx : x.1 ((CH.back_mono h).functor ⋙ s) = 0 :=
    x.2 _ (cosieve_res hQ W (s.map (homOfLE (Fin.zero_le _))) hs)
  change (pairU P W).μ _ _ (CH.term (W.ι ⋙ F₂) s x.1 (CH.back h) (CH.back_mono h)) = 0
  unfold CH.term
  rw [hx, map_zero, map_zero]

def relCup (P : CH.Pairing F₁ F₂ F₃) (W : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    {p n m : ℕ} (h : p + n = m) (b : CH.Cn (W.ι ⋙ F₁) p) : (RC F₂ W hQ).X n →ₗ[R] (RC F₃ W hQ).X m :=
  (((pairU P W).cupC h b).comp (Submodule.subtype _)).codRestrict _ fun x => cup_mem_rel P W hQ h b x




end Abs

section Cone
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} {ι : Type} [DecidableEq ι]

theorem capU_le (U : ι → ObjectProperty C) (S : Finset ι) {α : ι} (hα : α ∈ S) : capU U S ≤ U α :=
  fun _ h => h.2 α hα

def rhoS (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    (r : CH.Cn F₁ 2) (S : Finset ι) (n : ℕ) :
    ((covSy F₂ U hQ).K S).X n →ₗ[R] ((covSy F₃ U hQ).K S).X (n + 2) :=
  relCup P (capU U S) hQ (by omega : 2 + n = n + 2) ((CH.Mor.restrict F₁ (capU U S).ι).pullC 2 r)

def etaS (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)
    (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1) (α : ι) (S : Finset ι) (hS : α ∈ S) (n : ℕ) :
    ((covSy F₂ U hQ).K S).X n →ₗ[R] ((covSy F₃ U hQ).K S).X (n + 1) :=
  relCup P (capU U S) hQ (by omega : 1 + n = n + 1) ((resU F₁ (capU_le U S hS)).pullC 1 (β α))

theorem cone_apply (hCK : ConeKill) (hCD : CovDesc) (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C)
    (hU : ∀ α, Cosieve (U α)) {Q : ObjectProperty C} (hQ : Cosieve Q) (a : ℕ)
    (h1 : (covSy F₂ U hQ).One a) (h2 : (covSy F₃ U hQ).One (a + 1))
    (r : CH.Cn F₁ 2) (hr : CH.d F₁ 2 r = 0) (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1)
    (hβ : ∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict F₁ (U α).ι).pullC 2 r)
    (lam : ∀ (α : ι) (S : Finset ι), α ∈ S →
      (((covSy F₂ U hQ).K S).H a →ₗ[R] ((covSy F₃ U hQ).K S).H (a + 1)))
    (lam_nat : ∀ α {S T : Finset ι} (h : S ⊆ T) hS x, lam α T (h hS) (((covSy F₂ U hQ).res h).mapH a x) =
      ((covSy F₃ U hQ).res h).mapH _ (lam α S hS x))
    (lam_diff : ∀ α α' S hS hS' x hx hz,
      ((covSy F₃ U hQ).K S).cls (etaS P U hQ β α S hS a x - etaS P U hQ β α' S hS' a x) hz =
        lam α S hS (((covSy F₂ U hQ).K S).cls x hx) - lam α' S hS' (((covSy F₂ U hQ).K S).cls x hx))
    (n : ℕ) (x : ((covSy F₂ U hQ).K ∅).X n) (hx : ((covSy F₂ U hQ).K ∅).d n x = 0) :
    rhoS P U hQ r ∅ n x ∈ ((covSy F₃ U hQ).K ∅).B (n + 2) := by
  refine hCK R ι (covSy F₂ U hQ) (covSy F₃ U hQ) a (hCD R ι C F₂ U Q hQ hU) (hCD R ι C F₃ U Q hQ hU) h1 h2
    (rhoS P U hQ r) (etaS P U hQ β) ?_ ?_ ?_ ?_ lam lam_nat lam_diff n x hx
  · intro S n x
    refine Subtype.ext ?_
    change CH.d _ (n + 2) ((pairU P (capU U S)).cupC _ _ x.1) = (pairU P (capU U S)).cupC _ _ (CH.d _ n x.1)
    rw [CrystallineSemistableComparison.P.leibniz, CH.Mor.d_pullC, hr]
    simp
  · intro S T h n x
    rfl
  · intro α S T h hS n x
    rfl
  · intro α S hS n x
    refine Subtype.ext ?_
    change CH.d _ (n + 1) ((pairU P (capU U S)).cupC _ _ x.1) + (pairU P (capU U S)).cupC _ _ (CH.d _ n x.1) =
      (pairU P (capU U S)).cupC _ _ x.1
    rw [CrystallineSemistableComparison.P.leibniz, CH.Mor.d_pullC, hβ]
    simp
    rfl

end Cone

section Top
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem relNull_top (hT : TopRes) (F : C ⥤ ModuleCat.{0} R) {Q : ObjectProperty C} (hQ : Cosieve Q)
    (Wt Wp : ObjectProperty C) (hWt : ∀ T, Wt T) (h : Wp ≤ Wt) {n : ℕ}
    (hb : Function.Bijective ((RC.res F hQ h).mapH (n + 2))) (y : CH.Cn F (n + 2)) (hy : CH.d F (n + 2) y = 0)
    (hyr : y ∈ relS F Q (n + 2)) (x : (RC F Wp hQ).X (n + 2)) (hx : x.1 = (CH.Mor.restrict F Wp.ι).pullC (n + 2) y)
    (hB : x ∈ (RC F Wp hQ).B (n + 2)) : RelNull F Q (n + 2) y := by
  obtain ⟨hb2, hm2⟩ := hT R C F Wt Q hWt (n + 2)
  obtain ⟨hb1, hm1⟩ := hT R C F Wt Q hWt (n + 1)
  let y' : (RC F Wt hQ).X (n + 2) := ⟨(CH.Mor.restrict F Wt.ι).pullC (n + 2) y, (hm2 y).2 hyr⟩
  have hy' : (RC F Wt hQ).d (n + 2) y' = 0 := by
    refine Subtype.ext ?_
    change CH.d _ (n + 2) ((CH.Mor.restrict F Wt.ι).pullC (n + 2) y) = 0
    rw [CH.Mor.d_pullC, hy, map_zero]
  have hxy : (RC.res F hQ h).f (n + 2) y' = x := Subtype.ext hx.symm
  have hdx : (RC F Wp hQ).d (n + 2) x = 0 := by
    rw [← hxy, (RC.res F hQ h).comm, hy', map_zero]
  have h0 : (RC.res F hQ h).mapH (n + 2) ((RC F Wt hQ).cls y' hy') = 0 := by
    have e : (RC.res F hQ h).mapH (n + 2) ((RC F Wt hQ).cls y' hy') = (RC F Wp hQ).cls x hdx := by
      refine congrArg Submodule.Quotient.mk (Subtype.ext hxy)
    rw [e]
    exact (Submodule.Quotient.mk_eq_zero _).2 hB
  have h1 : (RC F Wt hQ).cls y' hy' = 0 := hb.1 (h0.trans (map_zero _).symm)
  have h2 : (⟨y', hy'⟩ : (RC F Wt hQ).Z (n + 2)) ∈ ((RC F Wt hQ).B (n + 2)).submoduleOf ((RC F Wt hQ).Z (n + 2)) :=
    (Submodule.Quotient.mk_eq_zero _).1 h1
  have h3 : y' ∈ (RC F Wt hQ).B (n + 2) := h2
  obtain ⟨b', hb'⟩ := h3
  obtain ⟨b, hbb⟩ := hb1.2 b'.1
  refine ⟨b, (hm1 b).1 (hbb ▸ b'.2), hb2.1 ?_⟩
  rw [← CH.Mor.d_pullC, hbb]
  exact congrArg Subtype.val hb'

end Top

section Forms
variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem lin_ext (hFL : FormLaws) {a : ℕ} {M : Type*} [AddCommGroup M] [Module K M] (g g' : Om K A a →ₗ[K] M)
    (h : ∀ g₀ (v : Fin a → A), g (form K g₀ v) = g' (form K g₀ v)) : g = g' :=
  LinearMap.ext_on (hFL K A A a).1 (by rintro _ ⟨g₀, v, rfl⟩; exact h g₀ v)

theorem form_cons_mul {a : ℕ} (g₀ u f : A) (v : Fin a → A) :
    form K g₀ (Fin.cons (u * f) v : Fin (a + 1) → A) =
      u • form K g₀ (Fin.cons f v : Fin (a + 1) → A) + f • form K g₀ (Fin.cons u v : Fin (a + 1) → A) := by
  have e : ∀ x : A, (fun k => KaehlerDifferential.D K A ((Fin.cons x v : Fin (a + 1) → A) k)) =
      (Fin.cons (KaehlerDifferential.D K A x) (fun k => KaehlerDifferential.D K A (v k)) : Fin (a + 1) → Ω[A⁄K]) := by
    intro x
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  unfold form
  rw [e, e, e, Derivation.leibniz]
  have h1 := (exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).toMultilinearMap.cons_add
    (fun k => KaehlerDifferential.D K A (v k)) (u • KaehlerDifferential.D K A f) (f • KaehlerDifferential.D K A u)
  have h2 := (exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).toMultilinearMap.cons_smul
    (fun k => KaehlerDifferential.D K A (v k)) u (KaehlerDifferential.D K A f)
  have h3 := (exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).toMultilinearMap.cons_smul
    (fun k => KaehlerDifferential.D K A (v k)) f (KaehlerDifferential.D K A u)
  simp only [AlternatingMap.coe_multilinearMap] at h1 h2 h3
  rw [h1, h2, h3, smul_add, smul_comm g₀ u, smul_comm g₀ f]

theorem wedge_mul (hFL : FormLaws) {a : ℕ} (u f : A) (wuf wf wu : Om K A a →ₗ[A] Om K A (a + 1))
    (huf : ∀ g₀ (g : Fin a → A), wuf (form K g₀ g) = form K g₀ (Fin.cons (u * f) g))
    (hf : ∀ g₀ (g : Fin a → A), wf (form K g₀ g) = form K g₀ (Fin.cons f g))
    (hu : ∀ g₀ (g : Fin a → A), wu (form K g₀ g) = form K g₀ (Fin.cons u g)) (ω : Om K A a) :
    wuf ω = u • wf ω + f • wu ω := by
  have := lin_ext (K := K) hFL (wuf.restrictScalars K) (u • wf.restrictScalars K + f • wu.restrictScalars K) (by
    intro g₀ v
    simp [huf, hf, hu, form_cons_mul])
  exact LinearMap.congr_fun this ω


theorem wedge_map (hFL : FormLaws) {a : ℕ} (φ : A →ₐ[K] B) (f : A) (w : Om K A a →ₗ[A] Om K A (a + 1))
    (w' : Om K B a →ₗ[B] Om K B (a + 1))
    (hw : ∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g))
    (hw' : ∀ g₀ (g : Fin a → B), w' (form K g₀ g) = form K g₀ (Fin.cons (φ f) g)) (ω : Om K A a) :
    omMap φ (a + 1) (w ω) = w' (omMap φ a ω) := by
  have := lin_ext (K := K) hFL ((omMap φ (a + 1)).comp (w.restrictScalars K))
    ((w'.restrictScalars K).comp (omMap φ a)) (by
      intro g₀ v
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hw]
      rw [(hFL K A B a).2 φ |>.1, (hFL K A B (a + 1)).2 φ |>.1, hw']
      congr 1
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp)
  exact LinearMap.congr_fun this ω

theorem eta_diff (hFL : FormLaws) {a : ℕ} (u : Aˣ) (f f' : A) (huf : f = u * f')
    (hnz : ∀ ω : Om K A (a + 1), f • ω = 0 → ω = 0) (w w' wu : Om K A a →ₗ[A] Om K A (a + 1))
    (hw : ∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g))
    (hw' : ∀ g₀ (g : Fin a → A), w' (form K g₀ g) = form K g₀ (Fin.cons f' g))
    (hwu : ∀ g₀ (g : Fin a → A), wu (form K g₀ g) = form K g₀ (Fin.cons (u : A) g)) (ω : Om K A a)
    (η η' : Om K A (a + 1)) (hη : f • η = w ω) (hη' : f' • η' = w' ω) :
    η - η' = (↑u⁻¹ : A) • wu ω := by
  subst huf
  have e := wedge_mul hFL (u : A) f' w w' wu hw hw' hwu ω
  have : ((u : A) * f') • (η - η' - (↑u⁻¹ : A) • wu ω) = 0 := by
    have e2 : ((u : A) * f') • ((↑u⁻¹ : A) • wu ω) = f' • wu ω := by
      rw [smul_smul, mul_comm (u : A), mul_assoc, Units.mul_inv, mul_one]
    rw [smul_sub, smul_sub, hη, e, e2, ← hη', smul_smul]
    abel
  exact sub_eq_zero.1 (hnz _ this)

end Forms

section abelian₂
variable {K : Type} [CommRing K]

theorem lin_out {Hr X O : Type*} [AddCommGroup Hr] [Module K Hr] [AddCommGroup X] [Module K X] [AddCommGroup O] [Module K O]
    (i : Hr →ₗ[K] X) (e : O →ₗ[K] X) (N : Submodule K O) (he : Function.Bijective e)
    (hr : ∀ ω, e ω ∈ LinearMap.range i ↔ ω ∈ N) : ∃ g : Hr →ₗ[K] N, ∀ y, e (g y) = i y := by
  let E := LinearEquiv.ofBijective e he
  refine ⟨((E.symm : X →ₗ[K] O).comp i).codRestrict N fun y => (hr _).1 ?_, fun y => ?_⟩
  · refine ⟨y, ?_⟩
    exact (E.apply_symm_apply (i y)).symm
  · exact E.apply_symm_apply (i y)

theorem lin_in {Hr X O : Type*} [AddCommGroup Hr] [Module K Hr] [AddCommGroup X] [Module K X] [AddCommGroup O] [Module K O]
    (i : Hr →ₗ[K] X) (e : O →ₗ[K] X) (N : Submodule K O) (hi : Function.Injective i)
    (hr : ∀ ω, e ω ∈ LinearMap.range i ↔ ω ∈ N) : ∃ g : N →ₗ[K] Hr, ∀ ω, i (g ω) = e ω := by
  let E := LinearEquiv.ofInjective i hi
  refine ⟨(E.symm : LinearMap.range i →ₗ[K] Hr).comp ((e.domRestrict N).codRestrict _ fun ω => (hr ω).2 ω.2), fun ω => ?_⟩
  have := E.apply_symm_apply ((e.domRestrict N).codRestrict _ (fun ω => (hr ω).2 ω.2) ω)
  exact congrArg Subtype.val this

variable {A : Type} [CommRing A] [Algebra K A]

theorem lam_one (hDW : DWedge) (hDL : DLog) {a : ℕ} {H₂ X₂ H₃ X₃ : Type*} [AddCommGroup H₂] [Module K H₂]
    [AddCommGroup X₂] [Module K X₂] [AddCommGroup H₃] [Module K H₃] [AddCommGroup X₃] [Module K X₃] (hFL : FormLaws)
    (i₂ : H₂ →ₗ[K] X₂) (i₃ : H₃ →ₗ[K] X₃) (e₂ : Om K A a →ₗ[K] X₂) (e₃ : Om K A (a + 1) →ₗ[K] X₃)
    (he₂ : Function.Bijective e₂) (hi₃ : Function.Injective i₃) (I : Ideal A)
    (hr₂ : ∀ ω, e₂ ω ∈ LinearMap.range i₂ ↔ ω ∈ relOm K I a)
    (hr₃ : ∀ ω, e₃ ω ∈ LinearMap.range i₃ ↔ ω ∈ relOm K I (a + 1)) (f : A) (hI : I = Ideal.span {f})
    (hnz : ∀ ω : Om K A (a + 1), f • ω = 0 → ω = 0) (c : ℤ) :
    ∃ l : H₂ →ₗ[K] H₃, ∀ (y : H₂) (ω : Om K A a) (η : Om K A (a + 1)) (w : Om K A a →ₗ[A] Om K A (a + 1)),
      (∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g)) → i₂ y = e₂ ω → f • η = w ω →
      i₃ (l y) = e₃ (c • η) := by
  subst hI
  obtain ⟨w₀, hw₀⟩ := hDW K A a f
  have hex := hDL K A a f hnz w₀ hw₀
  have uniq : ∀ η η' : Om K A (a + 1), f • η = f • η' → η = η' := fun η η' h =>
    sub_eq_zero.1 (hnz _ (by rw [smul_sub, h, sub_self]))
  let N := (relOm K (Ideal.span {f}) a).restrictScalars K
  let N' := (relOm K (Ideal.span {f}) (a + 1)).restrictScalars K
  have hch : ∀ ω : N, ∃ η : N', f • (η : Om K A (a + 1)) = w₀ ω.1 := fun ω => by
    obtain ⟨η, ⟨h1, h2⟩, -⟩ := hex ω.1 ω.2
    exact ⟨⟨η, h1⟩, h2⟩
  choose T hT using hch
  let TL : N →ₗ[K] N' :=
    { toFun := T
      map_add' := fun x y => Subtype.ext (uniq _ _ (by
        change f • ((T (x + y) : N') : Om K A (a + 1)) = f • (((T x : N') : Om K A (a + 1)) + (T y : N'))
        rw [smul_add, hT, hT, hT]
        exact map_add w₀ _ _))
      map_smul' := fun r x => Subtype.ext (uniq _ _ (by
        change f • ((T (r • x) : N') : Om K A (a + 1)) = f • (r • ((T x : N') : Om K A (a + 1)))
        rw [smul_comm f r, hT, hT]
        exact LinearMap.map_smul_of_tower w₀ r x.1)) }
  obtain ⟨g, hg⟩ := lin_out i₂ e₂ N he₂ hr₂
  obtain ⟨g', hg'⟩ := lin_in i₃ e₃ N' hi₃ hr₃
  refine ⟨g' ∘ₗ (c • TL) ∘ₗ g, fun y ω η w hw hy hη => ?_⟩
  have hww : w = w₀ := by
    have := lin_ext (K := K) hFL (w.restrictScalars K) (w₀.restrictScalars K) (fun g₀ v => by
      simp [hw, hw₀])
    exact LinearMap.ext fun x => LinearMap.congr_fun this x
  subst hww
  have hgy : (g y : Om K A a) = ω := he₂.1 ((hg y).trans hy)
  have hTy : ((T (g y) : N') : Om K A (a + 1)) = η := uniq _ _ (by rw [hT, hη, hgy])
  change i₃ (g' (c • T (g y))) = _
  rw [hg']
  congr 1
  rw [← hTy]
  rfl

end abelian₂

end GlobalTheory.CompanionTheory.RelKill
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Fam
variable {K : Type} [CommRing K] {ι : Type} {a : ℕ}

theorem lam_family (hDW : DWedge) (hDL : DLog) (hFL : FormLaws) (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    {H₂ X₂ H₃ X₃ : Finset ι → Type*} [∀ S, AddCommGroup (H₂ S)] [∀ S, Module K (H₂ S)]
    [∀ S, AddCommGroup (X₂ S)] [∀ S, Module K (X₂ S)] [∀ S, AddCommGroup (H₃ S)] [∀ S, Module K (H₃ S)]
    [∀ S, AddCommGroup (X₃ S)] [∀ S, Module K (X₃ S)]
    (i₂ : ∀ S, H₂ S →ₗ[K] X₂ S) (i₃ : ∀ S, H₃ S →ₗ[K] X₃ S)
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] X₂ S)) (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] X₃ S))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS)) (hi₃ : ∀ S, S.Nonempty → Function.Injective (i₃ S))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range (i₂ S) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range (i₃ S) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (ρ₂ : ∀ {S T : Finset ι}, S ⊆ T → (H₂ S →ₗ[K] H₂ T)) (ρ₃ : ∀ {S T : Finset ι}, S ⊆ T → (H₃ S →ₗ[K] H₃ T))
    (x₂ : ∀ {S T : Finset ι}, S ⊆ T → (X₂ S →ₗ[K] X₂ T)) (x₃ : ∀ {S T : Finset ι}, S ⊆ T → (X₃ S →ₗ[K] X₃ T))
    (hρ₂ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₂ T (ρ₂ h y) = x₂ h (i₂ S y))
    (hρ₃ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₃ T (ρ₃ h y) = x₃ h (i₃ S y))
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₂ h (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₃ h (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω)) :
    ∃ lam : ∀ (α : ι) (S : Finset ι), α ∈ S → (H₂ S →ₗ[K] H₃ S),
      (∀ α {S T : Finset ι} (h : S ⊆ T) hS y, lam α T (h hS) (ρ₂ h y) = ρ₃ h (lam α S hS y)) ∧
      ∀ α S hα y ω η (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
        (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (f α S hα) g)) →
        i₂ S y = e₂ S ⟨α, hα⟩ ω → f α S hα • η = w ω → i₃ S (lam α S hα y) = e₃ S ⟨α, hα⟩ (c • η) := by
  have key := fun (α : ι) (S : Finset ι) (hα : α ∈ S) =>
    lam_one hDW hDL hFL (i₂ S) (i₃ S) (e₂ S ⟨α, hα⟩) (e₃ S ⟨α, hα⟩) (he₂ S _) (hi₃ S ⟨α, hα⟩) (I S) (hr₂ S _)
      (hr₃ S _) (f α S hα) (hI α S hα) (hnz α S hα) c
  choose lam hlam using key
  refine ⟨lam, fun α S T h hα y => ?_, hlam⟩
  have hS : S.Nonempty := ⟨α, hα⟩
  have hT : T.Nonempty := ⟨α, h hα⟩
  refine hi₃ T hT ?_
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 (i₂ S y)
  have hm : ω ∈ relOm K (Ideal.span {f α S hα}) a := by
    rw [← hI α S hα]
    exact (hr₂ S hS ω).1 ⟨y, hω.symm⟩
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm
  obtain ⟨w', hw'⟩ := hDW K (A T) a (f α T (h hα))
  have wm := wedge_map hFL (φ h) (f α S hα) w w' hw (by rw [hφ]; exact hw') ω
  have s1 := hlam α S hα y ω η w hw hω.symm hη
  have s2 := hlam α T (h hα) (ρ₂ h y) (omMap (φ h) a ω) (omMap (φ h) (a + 1) η) w' hw'
    (by rw [hρ₂, ← hω, hx₂ h hS hT]) (by
      rw [← wm, ← hη, ((hFL K (A S) (A T) (a + 1)).2 (φ h)).2.1, hφ])
  rw [s2, hρ₃, s1, hx₃ h hS hT, map_zsmul (omMap (φ h) (a + 1))]

end Fam

section Kill
variable {K : Type} [CommRing K] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} K} {ι : Type} [DecidableEq ι]

theorem cov_kill (hCK : ConeKill) (hCD : CovDesc) (hDW : DWedge) (hDL : DLog) (hFL : FormLaws)
    (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C)
    (hU : ∀ α, Cosieve (U α)) {Q : ObjectProperty C} (hQ : Cosieve Q) (a : ℕ)
    (h1 : (covSy F₂ U hQ).One a) (h2 : (covSy F₃ U hQ).One (a + 1))
    (r : CH.Cn F₁ 2) (hr : CH.d F₁ 2 r = 0) (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1)
    (hβ : ∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict F₁ (U α).ι).pullC 2 r)
    (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] HU F₂ (capU U S) a))
    (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] HU F₃ (capU U S) (a + 1)))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS))
    (hi₃ : ∀ S, S.Nonempty → Function.Injective ((incl F₃ (capU U S) hQ).mapH (a + 1)))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range ((incl F₂ (capU U S) hQ).mapH a) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range ((incl F₃ (capU U S) hQ).mapH (a + 1)) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (k : ∀ {S T : Finset ι}, S ⊆ T → capU U T ≤ capU U S)
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₂ (k h)).pull a (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₃ (k h)).pull (a + 1) (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω))
    (u : ∀ (α α' : ι) (S : Finset ι), α ∈ S → α' ∈ S → (A S)ˣ)
    (huf : ∀ α α' S hα hα', f α S hα = u α α' S hα hα' * f α' S hα')
    (hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU U S).ι ⋙ F₂) a) (hy : CH.d _ a y = 0) (ω : Om K (A S) a)
      (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
      (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (u α α' S hα hα' : A S) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU U S).ι ⋙ F₃)).cls ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ (c • ((↑(u α α' S hα hα')⁻¹ : A S) • w ω)))
    (n : ℕ) (x : ((covSy F₂ U hQ).K ∅).X n) (hx : ((covSy F₂ U hQ).K ∅).d n x = 0) :
    rhoS P U hQ r ∅ n x ∈ ((covSy F₃ U hQ).K ∅).B (n + 2) := by
  obtain ⟨lam, lam_nat, lam_spec⟩ := lam_family (K := K) (a := a) hDW hDL hFL A
    (H₂ := fun S => ((covSy F₂ U hQ).K S).H a) (X₂ := fun S => HU F₂ (capU U S) a)
    (H₃ := fun S => ((covSy F₃ U hQ).K S).H (a + 1)) (X₃ := fun S => HU F₃ (capU U S) (a + 1))
    (fun S => (incl F₂ (capU U S) hQ).mapH a) (fun S => (incl F₃ (capU U S) hQ).mapH (a + 1))
    e₂ e₃ he₂ hi₃ I hr₂ hr₃ f hI hnz c φ hφ
    (fun h => ((covSy F₂ U hQ).res h).mapH a) (fun h => ((covSy F₃ U hQ).res h).mapH (a + 1))
    (fun h => (resU F₂ (k h)).pull a) (fun h => (resU F₃ (k h)).pull (a + 1))
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    hx₂ hx₃
  refine cone_apply hCK hCD P U hU hQ a h1 h2 r hr β hβ lam (fun α S T h hS x => lam_nat α h hS x) ?_ n x hx
  intro α α' S hα hα' x hx hz
  have hS : S.Nonempty := ⟨α, hα⟩
  refine hi₃ S hS ?_
  have hy : CH.d _ a x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 ((CH.cx _).cls x.1 hy)
  have hi : (incl F₂ (capU U S) hQ).mapH a (((covSy F₂ U hQ).K S).cls x hx) = e₂ S hS ω := hω.symm
  have hm : ω ∈ relOm K (I S) a := (hr₂ S hS ω).1 ⟨_, hi⟩
  have hm₁ : ω ∈ relOm K (Ideal.span {f α S hα}) a := hI α S hα ▸ hm
  have hm₂ : ω ∈ relOm K (Ideal.span {f α' S hα'}) a := hI α' S hα' ▸ hm
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨w', hw'⟩ := hDW K (A S) a (f α' S hα')
  obtain ⟨wu, hwu⟩ := hDW K (A S) a (u α α' S hα hα' : A S)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm₁
  obtain ⟨η', ⟨-, hη'⟩, -⟩ := hDL K (A S) a (f α' S hα') (hnz α' S hα') w' hw' ω hm₂
  have d := eta_diff hFL (u α α' S hα hα') (f α S hα) (f α' S hα') (huf α α' S hα hα') (hnz α S hα) w w' wu hw hw' hwu
    ω η η' hη hη'
  have s1 := lam_spec α S hα _ ω η w hw hi hη
  have s2 := lam_spec α' S hα' _ ω η' w' hw' hi hη'
  have hz' : CH.d ((capU U S).ι ⋙ F₃) (a + 1) ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
      ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    exact congrArg Subtype.val hz
  have s3 := hcup α α' S hα hα' x.1 hy ω wu hwu hω.symm hz'
  have e1 : (incl F₃ (capU U S) hQ).mapH (a + 1) (((covSy F₃ U hQ).K S).cls
      (etaS P U hQ β α S hα a x - etaS P U hQ β α' S hα' a x) hz) = (CH.cx ((capU U S).ι ⋙ F₃)).cls
      ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) hz' := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (LinearMap.congr_fun (map_sub ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)) _ _) x.1).symm
  have e2 := (map_sub ((incl F₃ (capU U S) hQ).mapH (a + 1)) (lam α S hα (((covSy F₂ U hQ).K S).cls x hx))
    (lam α' S hα' (((covSy F₂ U hQ).K S).cls x hx))).trans (congrArg₂ (· - ·) s1 s2)
  refine (e1.trans s3).trans (Eq.trans ?_ e2.symm)
  have e3 : (e₃ S ⟨α', hα'⟩ : _) = e₃ S ⟨α, hα⟩ := rfl
  rw [e3, ← map_sub, ← smul_sub, d]

end Kill

end GlobalTheory.CompanionTheory.RelKill
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Map
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}

theorem d_cup_one (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a m : ℕ} (h : 1 + a = m) (y : CH.Cn F₂ a) :
    CH.d F₃ m (P.cupC h b y) = -P.cupC (by omega : 1 + (a + 1) = m + 1) b (CH.d F₂ a y) := by
  rw [CrystallineSemistableComparison.P.leibniz, hb]
  simp

def cupMap (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) (a : ℕ) :
    CH.H F₂ a →ₗ[R] CH.H F₃ (a + 1) :=
  Submodule.mapQ _ _ ((((P.cupC (Nat.add_comm 1 a) b).comp (Submodule.subtype _))).codRestrict _ fun y => by
    change CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y.1) = 0
    rw [d_cup_one P b hb]
    have : CH.d F₂ a y.1 = 0 := y.2
    rw [this, map_zero, neg_zero]) (by
      intro y hy
      change P.cupC (Nat.add_comm 1 a) b y.1 ∈ (CH.cx F₃).B (a + 1)
      have hy' : y.1 ∈ (CH.cx F₂).B a := hy
      cases a with
      | zero =>
        have : y.1 = 0 := hy'
        rw [this, map_zero]
        exact Submodule.zero_mem _
      | succ m =>
        obtain ⟨t, ht⟩ := hy'
        refine ⟨-P.cupC (Nat.add_comm 1 m) b t, ?_⟩
        change CH.d F₃ _ _ = _
        rw [map_neg, d_cup_one P b hb, neg_neg]
        change P.cupC _ b (CH.d F₂ m t) = _
        exact congrArg _ ht)

theorem cupMap_cls (P : CH.Pairing F₁ F₂ F₃) (b : CH.Cn F₁ 1) (hb : CH.d F₁ 1 b = 0) {a : ℕ} (y : CH.Cn F₂ a)
    (hy : CH.d F₂ a y = 0) (hz : CH.d F₃ (a + 1) (P.cupC (Nat.add_comm 1 a) b y) = 0) :
    cupMap P b hb a ((CH.cx F₂).cls y hy) = (CH.cx F₃).cls (P.cupC (Nat.add_comm 1 a) b y) hz := rfl

def castH (F : C ⥤ ModuleCat.{0} R) {W W' : ObjectProperty C} (h : W = W') (j : ℕ) : HU F W' j ≃ₗ[R] HU F W j := by
  subst h
  exact LinearEquiv.refl R _

end Map

section Sch
variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem append_cons {M : Type*} {a : ℕ} (t : M) (g : Fin a → M) :
    Fin.append ![t] g ∘ Fin.cast (Nat.add_comm 1 a).symm = (Fin.cons t g : Fin (a + 1) → M) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · have e : Fin.cast (Nat.add_comm 1 a).symm (0 : Fin (a + 1)) = Fin.castAdd a (0 : Fin 1) := Fin.ext (by simp)
    simp only [Function.comp, e, Fin.append_left, Fin.cons_zero]
    rfl
  · have e : Fin.cast (Nat.add_comm 1 a).symm k.succ = Fin.natAdd 1 k := Fin.ext (by simp [Nat.add_comm])
    simp only [Function.comp, e, Fin.append_right, Fin.cons_succ]

theorem form_cup' (hFC : FormCup) {a c : ℕ} (hc : 1 + a = c) (g₁ g₀ : Sec q V) (t : Sec q V) (g : Fin a → Sec q V)
    (x : CH.Cn ((inU q V).ι ⋙ G q 1) 1) (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hx : CH.d _ 1 x = 0) (hy : CH.d _ a y = 0)
    (h₁ : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls x hx)) (h₂ : IsForm q V g₀ g ((CH.cx _).cls y hy)) :
    ∃ hz, IsForm q V (a := c) (g₁ * g₀) (Fin.append ![t] g ∘ Fin.cast hc.symm)
      ((CH.cx ((inU q V).ι ⋙ G q c)).cls (cupU q (inU q V) hc hc x y) hz) := by
  subst hc
  exact hFC K Z q V 1 a g₁ g₀ ![t] g x y hx hy h₁ h₂

theorem cup_form (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V) (b : CH.Cn ((inU q V).ι ⋙ G q 1) 1)
    (hb : CH.d _ 1 b = 0) (hf : IsForm q V (a := 1) g₁ ![t] ((CH.cx _).cls b hb))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn ((inU q V).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = E₂ ω)
    (hz : CH.d ((inU q V).ι ⋙ G q (a + 1)) (a + 1) (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) = 0) :
    (CH.cx ((inU q V).ι ⋙ G q (a + 1))).cls (cupU q (inU q V) (Nat.add_comm 1 a) (Nat.add_comm 1 a) b y) hz =
      E₃ (g₁ • w ω) := by
  let P := pairU (grOk (smFun Z q) (Nat.add_comm 1 a)).pair (inU q V)
  have key : (cupMap P b hb a).restrictScalars K ∘ₗ E₂ = E₃ ∘ₗ ((g₁ • w).restrictScalars K) := by
    refine lin_ext hFL _ _ fun g₀ v => ?_
    obtain ⟨⟨y', hy'⟩, hyy⟩ := Submodule.Quotient.mk_surjective _ (E₂ (form K g₀ v))
    have hy'' : CH.d _ a y' = 0 := hy'
    have hc' : (CH.cx _).cls y' hy'' = E₂ (form K g₀ v) := hyy
    have hI := h₂ g₀ v
    rw [← hc'] at hI
    obtain ⟨hz', hform⟩ := form_cup' hFC (Nat.add_comm 1 a) g₁ g₀ t v b y' hb hy'' hf hI
    rw [append_cons] at hform
    have hu := ((hFU K Z q V).2 (a + 1) (g₁ * g₀) (Fin.cons t v)).unique hform (h₃ _ _)
    change cupMap P b hb a (E₂ (form K g₀ v)) = E₃ (g₁ • w (form K g₀ v))
    rw [← hc', hw]
    refine (cupMap_cls P b hb y' hy'' hz').trans (hu.trans ?_)
    congr 1
    exact mul_smul _ _ _
  have := LinearMap.congr_fun key ω
  change cupMap P b hb a (E₂ ω) = E₃ (g₁ • w ω) at this
  rw [← hcls] at this
  exact (cupMap_cls P b hb y hy hz).symm.trans this

end Sch

end GlobalTheory.CompanionTheory.RelKill
end
end
