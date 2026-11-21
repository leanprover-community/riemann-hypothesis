import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry

noncomputable section

namespace GlobalTheory.SmoothLocusAdd

open GlobalTheory.WeierstrassCurve

theorem exists_hom_of_locally_rel {T Y S : Scheme.{0}} [IsReduced T] (t : T ⟶ S) (s : Y ⟶ S)
    [IsSeparated s]
    (Rel : ∀ (k : Type) [Field k], (Spec (.of k) ⟶ T) → (Spec (.of k) ⟶ Y) → Prop)
    (huniq : ∀ (k : Type) [Field k] x y y', Rel k x y → Rel k x y' → y = y')
    (H : ∀ z : T, ∃ (V : Scheme.{0}) (j : V ⟶ T) (_ : IsOpenImmersion j) (f : V ⟶ Y),
      z ∈ Set.range j ∧ f ≫ s = j ≫ t ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V), Rel k (x ≫ j) (x ≫ f)) :
    ∃ f : T ⟶ Y, f ≫ s = t ∧ ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), Rel k x (x ≫ f) := by
  choose V j hj f hz hs hf using H
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T V j (fun z => ⟨z, hz z⟩) hj
  have hc : ∀ a b, pullback.fst (j a) (j b) ≫ f a = pullback.snd _ _ ≫ f b := by
    intro a b
    have : IsReduced (pullback (j a) (j b)) :=
      isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
    refine (hom_eq_iff_forall_field s ?_).mpr fun k _ x => ?_
    · rw [Category.assoc, Category.assoc, hs, hs, pullback.condition_assoc]
    · have h₁ := hf a k (x ≫ pullback.fst (j a) (j b))
      have h₂ := hf b k (x ≫ pullback.snd (j a) (j b))
      rw [Category.assoc, Category.assoc] at h₁ h₂
      rw [← pullback.condition] at h₂
      exact huniq k _ _ _ h₁ h₂
  have hg : ∀ z, j z ≫ 𝒰.glueMorphisms f hc = f z := 𝒰.ι_glueMorphisms f hc
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun z => ?_, fun k _ x => ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s) (hg z))).trans (hs z)
  · let z : T := x (IsLocalRing.closedPoint k)
    have hr : Set.range x ⊆ Set.range (j z) := by
      rintro _ ⟨y, rfl⟩
      obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hz z
    have hy : IsOpenImmersion.lift (j z) x hr ≫ j z = x := IsOpenImmersion.lift_fac ..
    have := hf z k (IsOpenImmersion.lift (j z) x hr)
    rw [← hg z, ← Category.assoc, hy] at this
    exact this

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def IsSumAt {k : Type} [Field k] (a b c : Spec (.of k) ⟶ scheme W) : Prop :=
  ∀ (ρ : R →+* k) (P Q : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P)
    (hQ : IsUnimodularSol (W.map ρ) Q), a = ptHom W ρ P hP → b = ptHom W ρ Q hQ →
    ∃ h : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), c = ptHom W ρ _ h

def IsNonsingularAt {k : Type} [Field k] (a : Spec (.of k) ⟶ scheme W) : Prop :=
  ∀ (ρ : R →+* k) (P : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P),
    a = ptHom W ρ P hP → (W.map ρ).toProjective.Nonsingular P

theorem exists_triples {k : Type} [Field k] (a b : Spec (.of k) ⟶ scheme W)
    (hab : a ≫ toSpec W = b ≫ toSpec W) :
    ∃ (ρ : R →+* k) (P Q : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P)
      (hQ : IsUnimodularSol (W.map ρ) Q), a = ptHom W ρ P hP ∧ b = ptHom W ρ Q hQ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec W)
  obtain ⟨P, hP, eP⟩ := exists_eq_ptHom W φ.hom a hφ.symm
  obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptHom W φ.hom b (hab.symm.trans hφ.symm)
  exact ⟨φ.hom, P, Q, hP, hQ, eP, eQ⟩

theorem IsSumAt.unique {k : Type} [Field k] {a b c c' : Spec (.of k) ⟶ scheme W}
    (hab : a ≫ toSpec W = b ≫ toSpec W) (h : IsSumAt W a b c) (h' : IsSumAt W a b c') :
    c = c' := by
  obtain ⟨ρ, P, Q, hP, hQ, eP, eQ⟩ := exists_triples W a b hab
  obtain ⟨_, e⟩ := h ρ P Q hP hQ eP eQ
  obtain ⟨_, e'⟩ := h' ρ P Q hP hQ eP eQ
  exact e.trans e'.symm

open WeierstrassCurve.Projective in

theorem isSumAt_ptHom {k : Type} [Field k] (ρ : R →+* k) {P Q S : Fin 3 → k}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hS : IsUnimodularSol (W.map ρ) S) (nP : (W.map ρ).toProjective.Nonsingular P)
    (nQ : (W.map ρ).toProjective.Nonsingular Q)
    (e : S ≈ (W.map ρ).toProjective.add P Q) :
    IsSumAt W (ptHom W ρ P hP) (ptHom W ρ Q hQ) (ptHom W ρ S hS) := by
  intro ρ' P' Q' hP' hQ' eP eQ
  obtain rfl : ρ = ρ' := by
    have := congrArg (· ≫ toSpec W) eP
    simp only [ptHom_toSpec] at this
    exact congrArg (·.hom) (Spec.map_injective this)
  obtain ⟨u, hu⟩ := (ptHom_eq_ptHom_iff W hP' hP).mp eP.symm
  obtain ⟨v, hv⟩ := (ptHom_eq_ptHom_iff W hQ' hQ).mp eQ.symm
  have e₁ : P ≈ P' := ⟨u, hu.symm⟩
  have e₂ : Q ≈ Q' := ⟨v, hv.symm⟩
  have nP' := (nonsingular_of_equiv e₁).mp nP
  have nQ' := (nonsingular_of_equiv e₂).mp nQ
  have hA : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P' Q') :=
    .of_nonsingular (nonsingular_add nP' nQ')
  refine ⟨hA, ?_⟩
  obtain ⟨w, hw⟩ := Setoid.trans e (add_equiv e₁ e₂)
  exact ((ptHom_eq_ptHom_iff W hA hS).mpr ⟨w, hw.symm⟩).symm

open WeierstrassCurve.Projective in

theorem exists_sum_of_isUnit {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q S : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q))
    (hS : ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q))
    (i : Fin 3) (hi : IsUnit (S i)) :
    ∃ h : IsUnimodularSol (W.map ρ) S, ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Spec (.of C)),
      IsSumAt W (x ≫ ptHom W ρ P hP) (x ≫ ptHom W ρ Q hQ) (x ≫ ptHom W ρ S h) := by
  have hS' : ∀ (k : Type) [Field k] (φ : C →+* k),
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q) := fun k _ φ =>
    hS k φ fun h0 => (hi.map φ).ne_zero (congrFun h0 i)
  have h : IsUnimodularSol (W.map ρ) S := .of_isUnit (equation_of_forall_field fun k _ φ =>
    ((nonsingular_of_equiv (hS' k φ)).mpr (nonsingular_add (nP k φ) (nQ k φ))).left) i hi
  refine ⟨h, fun k _ x => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  obtain ⟨φ, rfl⟩ : ∃ ψ : C →+* k, CommRingCat.ofHom ψ = φ := ⟨φ.hom, rfl⟩
  rw [SpecMap_ptHom, SpecMap_ptHom, SpecMap_ptHom]
  exact isSumAt_ptHom W _ _ _ _ (nP k φ) (nQ k φ) (hS' k φ)

open WeierstrassCurve.Projective in

theorem exists_sum_near_prime {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q)) (z : Spec (.of C)) :
    ∃ (V : Scheme.{0}) (j : V ⟶ Spec (.of C)) (_ : IsOpenImmersion j) (f : V ⟶ scheme W),
      z ∈ Set.range j ∧ f ≫ toSpec W = j ≫ Spec.map (CommRingCat.ofHom ρ) ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V),
          IsSumAt W (x ≫ j ≫ ptHom W ρ P hP) (x ≫ j ≫ ptHom W ρ Q hQ) (x ≫ f) := by
  have key : ∃ (S : Fin 3 → C) (i : Fin 3), S i ∉ z.asIdeal ∧
      ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
        φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q) := by
    have eA : ∀ (k : Type) [Field k] (φ : C →+* k),
        (W.map (φ.comp ρ)).toProjective.addXYZ (φ ∘ P) (φ ∘ Q) =
          φ ∘ (W.map ρ).toProjective.addXYZ P Q := fun k _ φ =>
      map_addXYZ (W' := (W.map ρ).toProjective) φ P Q
    have eD : ∀ (k : Type) [Field k] (φ : C →+* k),
        AddLaw.diagXYZ (W.map (φ.comp ρ)).toProjective (φ ∘ P) (φ ∘ Q) =
          φ ∘ AddLaw.diagXYZ (W.map ρ).toProjective P Q := fun k _ φ =>
      AddLaw.map_diagXYZ (W := (W.map ρ).toProjective) φ P Q
    have := z.isPrime
    let κ := algebraMap C z.asIdeal.ResidueField
    rcases AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero (nP _ κ) (nQ _ κ) with h | h
    · rw [eA] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine ⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩
      rw [← eA] at h ⊢
      exact AddLaw.addXYZ_equiv_add (nP k φ) (nQ k φ) h
    · rw [eD] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine ⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩
      rw [← eD] at h ⊢
      exact AddLaw.diagXYZ_equiv_add (nP k φ) (nQ k φ) h
  obtain ⟨S, i, hi, hS⟩ := key
  let C' := Localization.Away (S i)
  let g : C →+* C' := algebraMap C C'
  have : _root_.IsReduced C' := inferInstanceAs (_root_.IsReduced (Localization (.powers (S i))))
  obtain ⟨h, hsum⟩ := exists_sum_of_isUnit W (g.comp ρ) (S := g ∘ S) (hP.map_comp g)
    (hQ.map_comp g) (fun k _ φ => nP k (φ.comp g)) (fun k _ φ => nQ k (φ.comp g))
    (fun k _ φ => hS k (φ.comp g)) i (IsLocalization.Away.algebraMap_isUnit (S i))
  refine ⟨Spec (.of C'), Spec.map (CommRingCat.ofHom g),
    IsOpenImmersion.of_isLocalization (S i), ptHom W _ _ h, ?_, ?_, fun k _ x => ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range C' (S i)).ge hi
  · rw [ptHom_toSpec, ← Spec.map_comp, CommRingCat.ofHom_comp]
  · rw [SpecMap_ptHom, SpecMap_ptHom]
    exact hsum k x

theorem exists_sum {T : Scheme.{0}} [IsReduced T] (p q : T ⟶ scheme W)
    (hpq : p ≫ toSpec W = q ≫ toSpec W)
    (np : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ p))
    (nq : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ q)) :
    ∃ s : T ⟶ scheme W, s ≫ toSpec W = p ≫ toSpec W ∧
      ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsSumAt W (x ≫ p) (x ≫ q) (x ≫ s) := by
  refine exists_hom_of_locally_rel (p ≫ toSpec W) (toSpec W)
    (fun k _ x y => IsSumAt W (x ≫ p) (x ≫ q) y)
    (fun k _ x y y' h h' => h.unique W (by simp only [Category.assoc, hpq]) h') fun z => ?_
  have hc : ∀ e : scheme W, ∃ i, e ∈ coordOpen W i := fun e => by
    rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ e) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨a, ha⟩ := hc (p z)
  obtain ⟨b, hb⟩ := hc (q z)
  obtain ⟨C, ι, _, ⟨z', rfl⟩, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := z) (U := p ⁻¹ᵁ coordOpen W a ⊓ q ⁻¹ᵁ coordOpen W b) ⟨ha, hb⟩
  have : _root_.IsReduced C := (affine_isReduced_iff C).mp (isReduced_of_isOpenImmersion ι)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (ι ≫ p ≫ toSpec W)
  obtain ⟨P, hP, -, eP⟩ := exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ p)
    (by rw [Category.assoc]; exact hφ.symm) a (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).1)
  obtain ⟨Q, hQ, -, eQ⟩ := exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ q)
    (by rw [Category.assoc, ← hpq]; exact hφ.symm) b (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).2)
  obtain ⟨V, j, _, f, ⟨v, rfl⟩, hf, hsum⟩ := exists_sum_near_prime W (C := C) φ.hom hP hQ
    (fun k _ ψ => np k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hP.map_comp ψ) (by
      rw [Category.assoc, ← SpecMap_ptHom W _ _ hP, ← eP]))
    (fun k _ ψ => nq k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hQ.map_comp ψ) (by
      rw [Category.assoc, ← SpecMap_ptHom W _ _ hQ, ← eQ])) z'
  refine ⟨V, j ≫ ι, inferInstance, f, ⟨v, by simp⟩, ?_, fun k _ x => ?_⟩
  · rw [hf, Category.assoc, ← hφ]; rfl
  · have := hsum k x
    rw [← eP, ← eQ] at this
    simpa only [Category.assoc] using this

end GlobalTheory.SmoothLocusAdd

namespace GlobalTheory

open MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open SmoothLocusAdd in

theorem exists_add_smoothLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∃ add : (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⊗ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ add).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) := by
  intro R _ _ _ W U hU hs hg
  let G : Over (Spec (.of R)) := Over.mk (U.ι ≫ WeierstrassCurve.toSpec W)
  have hG : IsIntegral (U : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)
  have hN : IsLocallyNoetherian (U : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)
  have hGG : IsIntegral (G ⊗ G).left := inferInstanceAs (IsIntegral
    (pullback (U.ι ≫ WeierstrassCurve.toSpec W) (U.ι ≫ WeierstrassCurve.toSpec W)))
  have hns : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ (U : Scheme)),
      IsNonsingularAt W (x ≫ U.ι) := fun k _ x ρ P hP e => (hU k ρ P hP).mp (by
    rw [← e]
    intro y _
    exact (x y).2)
  let p : (G ⊗ G).left ⟶ (U : Scheme) := (fst G G).left
  let q : (G ⊗ G).left ⟶ (U : Scheme) := (snd G G).left
  have hp : p ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom := Over.w (fst G G)
  have hq : q ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom := Over.w (snd G G)
  have hpq : (p ≫ U.ι) ≫ WeierstrassCurve.toSpec W = (q ≫ U.ι) ≫ WeierstrassCurve.toSpec W := by
    rw [Category.assoc, Category.assoc, hp, hq]
  obtain ⟨s, hs₁, hs₂⟩ := exists_sum W (p ≫ U.ι) (q ≫ U.ι) hpq
    (fun k _ x => by rw [← Category.assoc]; exact hns k _)
    (fun k _ x => by rw [← Category.assoc]; exact hns k _)
  have hr : Set.range s ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    let x := (G ⊗ G).left.fromSpecResidueField z
    obtain ⟨ρ, P, Q, hP, hQ, eP, eQ⟩ := exists_triples W (k := (G ⊗ G).left.residueField z)
      (x ≫ p ≫ U.ι) (x ≫ q ≫ U.ι) (by rw [Category.assoc, Category.assoc x, hpq])
    obtain ⟨h, e⟩ := hs₂ ((G ⊗ G).left.residueField z) x ρ P Q hP hQ eP eQ
    have nP := hns ((G ⊗ G).left.residueField z) (x ≫ p) ρ P hP ((Category.assoc _ _ _).trans eP)
    have nQ := hns ((G ⊗ G).left.residueField z) (x ≫ q) ρ Q hQ ((Category.assoc _ _ _).trans eQ)
    have := (hU _ ρ _ h).mpr (WeierstrassCurve.Projective.nonsingular_add nP nQ)
    rw [← e] at this
    have h2 : s (x (IsLocalRing.closedPoint _)) ∈ U := this (Set.mem_univ _)
    have h3 : x (IsLocalRing.closedPoint _) = z := Scheme.fromSpecResidueField_apply z _
    rw [h3] at h2
    rw [Scheme.Opens.range_ι]
    exact h2
  have hl : IsOpenImmersion.lift U.ι s hr ≫ U.ι = s := IsOpenImmersion.lift_fac ..
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι s hr) ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι s hr ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom
    rw [← Category.assoc, hl, hs₁, Category.assoc, hp]
  · intro k _ ρ x y P Q hP hQ ex ey
    let w : Spec (.of k) ⟶ (G ⊗ G).left := (lift x y).left
    have e₁ : w ≫ p = x.left := congrArg (·.left) (lift_fst x y)
    have e₂ : w ≫ q = y.left := congrArg (·.left) (lift_snd x y)
    obtain ⟨h, e⟩ := hs₂ k w ρ P Q hP hQ
      (by rw [← Category.assoc, e₁]; exact ex) (by rw [← Category.assoc, e₂]; exact ey)
    refine ⟨h, ?_⟩
    change (w ≫ IsOpenImmersion.lift U.ι s hr) ≫ U.ι = _
    rw [Category.assoc, hl, e]

end GlobalTheory
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace WeierstrassCurve

namespace SmoothNeg

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem equation_neg {A : Type*} [CommRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) : V.toProjective.Equation (V.toProjective.neg P) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination h

theorem span_le_span_neg {A : Type*} [CommRing A] (V : WeierstrassCurve A) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (V.toProjective.neg P)) := by
  have h0 : P 0 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := Ideal.subset_span ⟨0, rfl⟩
  have h2 : P 2 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := Ideal.subset_span ⟨2, rfl⟩
  have h1 : -P 1 - V.a₁ * P 0 - V.a₃ * P 2 ∈ Ideal.span (Set.range (V.toProjective.neg P)) :=
    Ideal.subset_span ⟨1, rfl⟩
  have h1' : P 1 ∈ Ideal.span (Set.range (V.toProjective.neg P)) := by
    have : P 1 = -((-P 1 - V.a₁ * P 0 - V.a₃ * P 2) + V.a₁ * P 0 + V.a₃ * P 2) := by ring
    rw [this]
    exact neg_mem (add_mem (add_mem h1 (Ideal.mul_mem_left _ _ h0)) (Ideal.mul_mem_left _ _ h2))
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem isUnimodularSol_neg {A : Type*} [CommRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : IsUnimodularSol V P) : IsUnimodularSol V (V.toProjective.neg P) :=
  ⟨equation_neg h.equation, top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_neg V P))⟩

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def negCoord : Fin 3 → HomRing W := (W.map (algebraMap R (HomRing W))).toProjective.neg (coord W)

theorem negCoord_mem (i : Fin 3) : negCoord W i ∈ grading W 1 := by
  fin_cases i
  · exact coord_mem W 0
  · change -coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2 ∈ _
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact sub_mem (sub_mem (neg_mem (coord_mem W 1)) (Submodule.smul_mem _ _ (coord_mem W 0)))
      (Submodule.smul_mem _ _ (coord_mem W 2))
  · exact coord_mem W 2

def negRingHom : HomRing W →+* HomRing W :=
  evalHom W (algebraMap R (HomRing W)) (negCoord W) (equation_neg (equation_coord W))

def negGraded : grading W →+*ᵍ grading W where
  toRingHom := negRingHom W
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    have hp' : p.IsHomogeneous n := hp
    change MvPolynomial.eval₂ (algebraMap R (HomRing W)) (negCoord W) p ∈ _
    rw [MvPolynomial.eval₂_eq]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have := SetLike.prod_pow_mem_graded (grading W) (fun _ => 1) (negCoord W) (F := d.support) d
      (fun i _ => negCoord_mem W i)
    rw [hp'.degree_eq_sum_deg_support hd]
    simpa using this

theorem irrelevant_le_map_negGraded :
    irrelevant (grading W) ≤ (irrelevant (grading W)).map (negGraded W) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord]
  refine (span_le_span_neg (W.map (algebraMap R (HomRing W))) (coord W)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : (W.map (algebraMap R (HomRing W))).toProjective.neg (coord W) i =
      negGraded W (coord W i) :=
    (evalHom_coord W (algebraMap R (HomRing W)) (negCoord W)
      (equation_neg (equation_coord W)) i).symm
  rw [this]
  exact Ideal.mem_map_of_mem (negGraded W) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))

def negMap : scheme W ⟶ scheme W := Proj.map (negGraded W) (irrelevant_le_map_negGraded W)

@[reassoc]
theorem ptHom_negMap {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ negMap W = ptHom W ρ _ (isUnimodularSol_neg hP) := by
  refine (ProjPoint.ofHom_map (negGraded W) (irrelevant_le_map_negGraded W) _
    (map_irrelevant_evalHom W hP)).trans ?_
  have : (evalHom W ρ P hP.equation).comp (negGraded W).toRingHom =
      evalHom W ρ _ (isUnimodularSol_neg hP).equation := by
    refine homRing_hom_ext W (fun r => ?_) (fun i => ?_)
    · refine (congrArg (evalHom W ρ P hP.equation) (evalHom_algebraMap W _ (negCoord W)
        (equation_neg (equation_coord W)) r)).trans ?_
      rw [evalHom_algebraMap, evalHom_algebraMap]
    refine (congrArg (evalHom W ρ P hP.equation) (evalHom_coord W _ (negCoord W)
      (equation_neg (equation_coord W)) i)).trans ?_
    rw [evalHom_coord]
    fin_cases i
    · exact evalHom_coord W ρ P hP.equation 0
    · change evalHom W ρ P hP.equation
        (-coord W 1 - algebraMap R _ W.a₁ * coord W 0 - algebraMap R _ W.a₃ * coord W 2) =
        -P 1 - ρ W.a₁ * P 0 - ρ W.a₃ * P 2
      simp only [map_sub, map_neg, map_mul, evalHom_coord, evalHom_algebraMap]
    · exact evalHom_coord W ρ P hP.equation 2
  simp only [this]
  rfl

theorem negMap_toSpec : negMap W ≫ toSpec W = toSpec W := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_negMap_assoc, ptHom_toSpec, ptHom_toSpec]
  · rw [chartZ, pt_eq_ptHom, ptHom_negMap_assoc, ptHom_toSpec, ptHom_toSpec]

theorem range_subset_of_forall_field {T Y : Scheme.{0}} (f : T ⟶ Y) (U : Y.Opens)
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) :
    Set.range f ⊆ Set.range U.ι := by
  rintro _ ⟨t, rfl⟩
  have := h (T.residueField t) (T.fromSpecResidueField t)
    (Set.mem_univ (IsLocalRing.closedPoint (T.residueField t)))
  rw [Scheme.Opens.range_ι]
  have e : (T.fromSpecResidueField t ≫ f) (IsLocalRing.closedPoint (T.residueField t)) = f t :=
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg f (Scheme.fromSpecResidueField_apply t _))
  rw [← e]
  exact this

end SmoothNeg

open SmoothNeg in

theorem exists_neg_origin_smoothLocus :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → ∃ (neg : (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (o : 𝟙_ _ ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), o.left ≫ U.ι = GlobalTheory.WeierstrassCurve.zero W ∧ ∀ (k : Type) [Field k] (ρ : R →+* k) (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P), (x ≫ neg).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h := by
  intro R _ _ _ W U hU
  have hneg : Set.range (U.ι ≫ negMap W) ⊆ Set.range U.ι := by
    refine range_subset_of_forall_field _ U fun k _ x => ?_
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (x ≫ U.ι ≫ toSpec W)
    obtain ⟨P, hP, e⟩ := exists_eq_ptHom W ρ.hom (x ≫ U.ι) (by simpa using hρ.symm)
    have hns : (W.map ρ.hom).toProjective.Nonsingular P := by
      rw [← hU k ρ.hom P hP, ← e]
      intro y _
      simp
    rw [← Category.assoc, e, ptHom_negMap, hU]
    exact WeierstrassCurve.Projective.nonsingular_neg hns
  have hzero : Set.range (zero W) ⊆ Set.range U.ι := by
    refine range_subset_of_forall_field _ U fun k _ x => ?_
    obtain ⟨ρ, rfl⟩ := Spec.map_surjective x
    have := SpecMap_zero W ρ.hom
    rw [CommRingCat.ofHom_hom] at this
    rw [this, hU]
    exact WeierstrassCurve.Projective.nonsingular_zero
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg) ?_,
    Over.homMk (IsOpenImmersion.lift U.ι (zero W) hzero) ?_, ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg ≫ U.ι ≫ toSpec W = U.ι ≫ toSpec W
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, negMap_toSpec]
  · change IsOpenImmersion.lift U.ι (zero W) hzero ≫ U.ι ≫ toSpec W = 𝟙 _
    rw [IsOpenImmersion.lift_fac_assoc, zero_toSpec]
  · exact IsOpenImmersion.lift_fac _ _ _
  · intro k _ ρ x P hP e
    refine ⟨isUnimodularSol_neg hP, ?_⟩
    change (x.left ≫ IsOpenImmersion.lift U.ι (U.ι ≫ negMap W) hneg) ≫ U.ι = _
    rw [Category.assoc, IsOpenImmersion.lift_fac, ← ptHom_negMap W ρ P hP, ← e]
    exact (Category.assoc _ _ _).symm

end WeierstrassCurve

end GlobalTheory
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace WeierstrassCurve

theorem exists_point_equiv_smoothLocus {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    (k : Type) [Field k] [Algebra R k] :
    ∃ c : (W.baseChange k).toProjective.Point ≃ (specOver R k ⟶ Over.mk (U.ι ≫ toSpec W)),
      ∀ p, (c p).left ≫ U.ι = (ofProjectivePoint W k p).left := by
  have hr : ∀ p, Set.range (ofProjectivePoint W k p).left ⊆ Set.range U.ι := by
    rintro @⟨⟨P⟩, hP⟩ _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hU k (algebraMap R k) P (.of_nonsingular hP)).mpr hP (Set.mem_univ z)
  let c : (W.baseChange k).toProjective.Point → (specOver R k ⟶ Over.mk (U.ι ≫ toSpec W)) :=
    fun p => Over.homMk (IsOpenImmersion.lift U.ι _ (hr p))
      ((IsOpenImmersion.lift_fac_assoc U.ι _ (hr p) _).trans (Over.w (ofProjectivePoint W k p)))
  have hc : ∀ p, (c p).left ≫ U.ι = (ofProjectivePoint W k p).left := fun p =>
    IsOpenImmersion.lift_fac U.ι _ (hr p)
  refine ⟨Equiv.ofBijective c ⟨fun p q e => ?_, fun x => ?_⟩, hc⟩
  · refine ofProjectivePoint_injective W k (Over.OverMorphism.ext ?_)
    rw [← hc, ← hc, e]
  · obtain ⟨P, hP, e⟩ := exists_eq_ptHom W (algebraMap R k) (x.left ≫ U.ι)
      ((Category.assoc _ _ _).trans (Over.w x))
    have hns : (W.baseChange k).toProjective.Nonsingular P := (hU k _ P hP).mp (by
      rw [← e]
      intro y _
      exact (x.left y).2)
    refine ⟨⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr hns⟩,
      Over.OverMorphism.ext ?_⟩
    exact (cancel_mono U.ι).mp ((hc _).trans e.symm)

end WeierstrassCurve

open WeierstrassCurve in

theorem exists_grpObj_smoothLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∃ _ : GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ (η[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.zero W ∧ (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) := by
  intro R _ _ _ W U hU hs hg
  classical
  obtain ⟨m, hm⟩ := exists_add_smoothLocus R W U hU hs hg
  obtain ⟨i, e, he, hi⟩ := exists_neg_origin_smoothLocus R W U hU
  let G : Over (Spec (.of R)) := Over.mk (U.ι ≫ toSpec W)
  have hG : IsIntegral (U : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ toSpec W)
  have hN : IsLocallyNoetherian (U : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ toSpec W)
  have hG₁ : IsIntegral G.left := hG
  have hG₂ : IsIntegral (pullback (U.ι ≫ toSpec W) (U.ι ≫ toSpec W)) := inferInstance
  have hG₂' : IsIntegral (G ⊗ G).left := hG₂
  have hN₂ : IsLocallyNoetherian (G ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (U.ι ≫ toSpec W) (U.ι ≫ toSpec W))
  have hG₃ : IsIntegral ((G ⊗ G) ⊗ G).left := inferInstanceAs (IsIntegral
    (pullback (G ⊗ G).hom (U.ι ≫ toSpec W)))
  have hsep : IsSeparated G.hom := inferInstanceAs (IsSeparated (U.ι ≫ toSpec W))
  have H : ∀ (k : Type) [Field k] [Algebra R k], ∃ (M : Type) (_ : AddCommGroup M)
      (c : M ≃ (specOver R k ⟶ G)), toUnit _ ≫ e = c 0 ∧
        (∀ a b, lift (c a) (c b) ≫ m = c (a + b)) ∧ ∀ a, c a ≫ i = c (-a) := by
    intro k _ _
    obtain ⟨c, hc⟩ := exists_point_equiv_smoothLocus W U hU k
    refine ⟨_, inferInstance, c, ?_, ?_, ?_⟩
    · refine Over.OverMorphism.ext ((cancel_mono U.ι).mp ?_)
      rw [hc, ofProjectivePoint_zero, zeroOver_left]
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) he)
    · rintro @⟨⟨P⟩, hP⟩ @⟨⟨Q⟩, hQ⟩
      obtain ⟨h, e'⟩ := hm k (algebraMap R k) (c ⟨hP⟩) (c ⟨hQ⟩) P Q (.of_nonsingular hP)
        (.of_nonsingular hQ) (hc _) (hc _)
      refine Over.OverMorphism.ext ((cancel_mono U.ι).mp (e'.trans ?_))
      rw [hc]
      rfl
    · rintro @⟨⟨P⟩, hP⟩
      obtain ⟨h, e'⟩ := hi k (algebraMap R k) (c ⟨hP⟩) P (.of_nonsingular hP) (hc _)
      refine Over.OverMorphism.ext ((cancel_mono U.ι).mp (e'.trans ?_))
      rw [hc]
      rfl
  letI : GrpObj G := grpObjOfFieldPoints e m i H
  refine ⟨this, ⟨?_⟩, he, hm⟩
  refine over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => ?_
  obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
  obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _)
  obtain ⟨b, hb⟩ := c.surjective (x ≫ snd _ _)
  obtain rfl : x = lift (c a) (c b) :=
    CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, ha]) (by rw [lift_snd, hb])
  change lift (c a) (c b) ≫ (β_ G G).hom ≫ m = lift (c a) (c b) ≫ m
  rw [lift_braiding_hom_assoc, h₁, h₁, add_comm]

end GlobalTheory
end
