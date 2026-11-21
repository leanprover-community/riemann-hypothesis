import Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine ⟨fun x y h => ?_, fun y => ⟨pull R (inv f) F n y, ?_⟩⟩
  · have := congrArg (pull R (inv f) F n) h
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_of_section {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {r : E' ⟶ E} {F : Shv R}
    (h : f ≫ r = 𝟙 _) (hr : Eqv R r F) : Eqv R f F := by
  intro n
  have hc : (pull R f F n : _ → _) ∘ pull R r F n = id := by
    funext x; change pull R f F n (pull R r F n x) = x; rw [← pull_comp, h, pull_id]
  have : Function.Bijective ((pull R f F n : _ → _) ∘ pull R r F n) := by rw [hc]; exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ (hr n)).1 this

def fW (d : ℕ) (R : Type) [CommRing R] :
    Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin d) R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : MvPolynomial (Fin d) R →+* _))

theorem smooth_C (A : Type) [CommRing A] : (LaurentPolynomial.C : A →+* LaurentPolynomial A).Smooth := by
  have h1 : (Polynomial.C : A →+* Polynomial A).Smooth := by
    rw [show (Polynomial.C : A →+* Polynomial A) = algebraMap A (Polynomial A) from rfl]
    exact RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  have h2 : (algebraMap (Polynomial A) (LaurentPolynomial A)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (R := Polynomial A) (S := LaurentPolynomial A) Polynomial.X
  have h3 := RingHom.Smooth.comp h1 h2
  convert h3 using 1
  ext a
  simp

instance (d : ℕ) (R : Type) [CommRing R] : Smooth (fW d R) := by
  rw [fW, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_C _

instance (d : ℕ) (R : Type) [CommRing R] : Surjective (fW d R) := by
  let s : LaurentPolynomial (MvPolynomial (Fin d) R) →+* MvPolynomial (Fin d) R := LaurentPolynomial.eval₂ (RingHom.id _) 1
  have hs : s.comp LaurentPolynomial.C = RingHom.id _ := by ext x <;> simp [s]
  have : Spec.map (CommRingCat.ofHom s) ≫ fW d R = 𝟙 _ := by
    rw [fW, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]; exact Spec.map_id _
  have : Surjective (Spec.map (CommRingCat.ofHom s) ≫ fW d R) := by rw [this]; infer_instance
  exact Surjective.of_comp (Spec.map (CommRingCat.ofHom s)) (fW d R)

def LeafWCech : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ ψ : W d R ⟶ cech (fW d R), IsIso ψ ∧ wa d R ≫ ψ ≫ cechAug (fW d R) = 𝟙 _

theorem LeafWEqvR_of (hW : LeafWCech) : LeafWEqvR := by
  intro hH q _ d R _ _ i
  obtain ⟨ψ, hψ, he⟩ := hW d R
  have hA : Eqv _ (cechAug (fW d R)) (tw q i) := hH.2.1 (ZMod q) (fW d R) (tw q i)
  exact eqv_of_section (by rw [← he]) (eqv_comp (eqv_of_isIso ψ _) hA)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev vtx (n : ℕ) (i : Fin (n + 1)) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk n :=
  SimplexCategory.const _ _ i

def LeafCechRec : Prop := ∀ (X : Spc) (P Z : PSh) (φ : P ⟶ Z) (r : X ⟶ disc.obj Z)
  (g : X.obj (op (SimplexCategory.mk 0)) ⟶ P), g ≫ φ = r.app (op (SimplexCategory.mk 0)) →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : (X.obj (op (SimplexCategory.mk n))).obj U),
    (∀ i, g.app U ((X.map (vtx n i).op).app U x) = g.app U ((X.map (vtx n i).op).app U x')) → x = x') →
  (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → P.obj U) (z : Z.obj U), (∀ i, φ.app U (y i) = z) →
    ∃ x, ∀ i, g.app U ((X.map (vtx n i).op).app U x) = y i) →
  ∃ ψ : X ⟶ (Arrow.mk φ).cechNerve, IsIso ψ ∧ ψ ≫ (Arrow.mk φ).augmentedCechNerve.hom = r

def LeafWData : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (r : W d R ⟶ disc.obj (yoneda.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) R)))))
    (g : (W d R).obj (op (SimplexCategory.mk 0)) ⟶
      yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (MvPolynomial (Fin d) R))))),
    wa d R ≫ r = 𝟙 _ ∧ g ≫ yoneda.map (fW d R) = r.app (op (SimplexCategory.mk 0)) ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : ((W d R).obj (op (SimplexCategory.mk n))).obj U),
      (∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = g.app U (((W d R).map (vtx n i).op).app U x')) →
        x = x') ∧
    (∀ (n : ℕ) (U : Scheme.{0}ᵒᵖ) (y : Fin (n + 1) → (yoneda.obj (Spec (CommRingCat.of
        (LaurentPolynomial (MvPolynomial (Fin d) R))))).obj U) (z : (yoneda.obj (Spec (CommRingCat.of
        (MvPolynomial (Fin d) R)))).obj U), (∀ i, (yoneda.map (fW d R)).app U (y i) = z) →
      ∃ x, ∀ i, g.app U (((W d R).map (vtx n i).op).app U x) = y i)

theorem LeafWCech_of (hC : LeafCechRec) (hD : LeafWData) : LeafWCech := by
  intro d R _
  obtain ⟨r, g, hr, hg, hi, hs⟩ := hD d R
  obtain ⟨ψ, hψ, he⟩ := hC (W d R) _ _ (yoneda.map (fW d R)) r g hg hi hs
  refine ⟨ψ, hψ, ?_⟩
  change wa d R ≫ ψ ≫ (Arrow.mk (yoneda.map (fW d R))).augmentedCechNerve.hom = 𝟙 _
  subst he
  exact hr

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem psh_limit_ext {J : Type} [SmallCategory J] (F : J ⥤ PSh) (U : Scheme.{0}ᵒᵖ) (w w' : (limit F).obj U)
    (h : ∀ j, (limit.π F j).app U w = (limit.π F j).app U w') : w = w' := by
  apply (mono_iff_injective (limitObjIsoLimitCompEvaluation F U).hom).1 inferInstance
  apply Types.limit_ext
  intro j
  have e := limitObjIsoLimitCompEvaluation_hom_π F j (k := U)
  have e1 := congrArg (fun f => f w) (congrArg ConcreteCategory.hom e)
  have e2 := congrArg (fun f => f w') (congrArg ConcreteCategory.hom e)
  simp only [types_comp_apply] at e1 e2
  rw [e1, e2]; exact h j

theorem wpb_ext {B : PSh} {n : ℕ} {P : PSh} (φ : P ⟶ B) (U : Scheme.{0}ᵒᵖ)
    (w w' : (widePullback B (fun _ : Fin (n + 1) => P) fun _ => φ).obj U)
    (h : ∀ i, NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w =
      NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w') : w = w' := by
  apply psh_limit_ext _ U
  rintro (_ | i)
  · have e := WidePullback.π_arrow (fun _ : Fin (n + 1) => φ) 0
    have e1 := congrArg (fun f => (f.app U) w) e
    have e2 := congrArg (fun f => (f.app U) w') e
    simp only [NatTrans.comp_app, types_comp_apply] at e1 e2
    change NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w =
      NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w'
    rw [← e1, ← e2, h 0]
  · exact h i

theorem leafCechRec : LeafCechRec := by
  intro X P Z φ r g hg hinj hsurj
  let Xa : SimplicialObject.Augmented PSh := { left := X, right := Z, hom := r }
  let G : SimplicialObject.Augmented.toArrow.obj Xa ⟶ Arrow.mk φ :=
    Arrow.homMk g (𝟙 Z) (by change g ≫ φ = r.app _ ≫ 𝟙 Z; exact hg.trans (Category.comp_id _).symm)
  let Ψ := SimplicialObject.equivalenceLeftToRight Xa (Arrow.mk φ) G
  have hπ : ∀ (m : ℕ) (U : Scheme.{0}ᵒᵖ) x (i : Fin (m + 1)),
      NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U
        (NatTrans.app (Ψ.left.app (op (SimplexCategory.mk m))) U x) = g.app U ((X.map (vtx m i).op).app U x) := by
    intro m U x i
    have e : Ψ.left.app (op (SimplexCategory.mk m)) ≫ WidePullback.π (fun _ : Fin (m + 1) => φ) i =
        X.map (vtx m i).op ≫ g := WidePullback.lift_π _ _ _ _ _
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) x
    exact this
  refine ⟨Ψ.left, ?_, ?_⟩
  · have : ∀ n, IsIso (Ψ.left.app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ m => ?_
      have : ∀ U, IsIso ((Ψ.left.app (op (SimplexCategory.mk m))).app U) := by
        intro U
        rw [isIso_iff_bijective]
        constructor
        · intro x x' hx
          apply hinj m U x x'
          intro i
          rw [← hπ, ← hπ]
          exact congrArg _ hx
        · intro w
          obtain ⟨x, hx⟩ := hsurj m U (fun i => NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U w)
            (NatTrans.app (WidePullback.base (fun _ : Fin (m + 1) => φ)) U w) (fun i => by
              have e := WidePullback.π_arrow (fun _ : Fin (m + 1) => φ) i
              have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) w
              exact this)
          refine ⟨x, wpb_ext φ U _ _ fun i => ?_⟩
          rw [hπ]; exact hx i
      exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ Ψ.left this
  · refine (Ψ.w : _).trans ?_
    change r ≫ (SimplicialObject.const PSh).map (𝟙 Z) = r
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem LeafWCech_of_data (hD : LeafWData) : LeafWCech := LeafWCech_of leafCechRec hD

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end
