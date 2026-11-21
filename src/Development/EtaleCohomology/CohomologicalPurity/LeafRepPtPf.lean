import Development.EtaleCohomology.CohomologicalPurity.LeafTailRepPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vo (N k : ℕ) : PSh := vecCat N k ⋙ Cat.objects

def voTail (d : ℕ) : Vo (d + 1) 1 ⟶ Vo d 0 where
  app U := TypeCat.ofHom fun v => (Vec.tail d U.unop).obj v
  naturality _ _ _ := rfl

def nerve0 (N k : ℕ) : (Pj N k).obj (op (SimplexCategory.mk 0)) ≅ Vo N k :=
  NatIso.ofComponents (fun U =>
    { hom := TypeCat.ofHom fun (F : ComposableArrows (Vec N k U.unop) 0) => F.obj 0
      inv := TypeCat.ofHom fun v => ComposableArrows.mk₀ (C := Vec N k U.unop) v
      hom_inv_id := by
        ext F
        exact ComposableArrows.ext₀ rfl
      inv_hom_id := rfl })
    (fun _ => rfl)

def LeafRepVec : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : Vo (d + 1) 1 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : Vo d 0 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off A I).toScheme),
      prod.map (voTail d) (𝟙 _) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep0_of_vec (hV : LeafRepVec) : LeafTailRep0 := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w⟩ := hV d R
  let E := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk 0))
  let sq : E.obj (sp R) ≅ yoneda.obj (Spec (CommRingCat.of R)) := Iso.refl _
  refine ⟨A, inferInstance, I, φ, hI, h,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 (d + 1) 1) sq ≪≫ f₁,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 d 0) sq ≪≫ f₂, ?_⟩
  simp only [Iso.trans_hom, PreservesLimitPair.iso_hom, prod.mapIso_hom, Category.assoc]
  change E.map (prod.map _ _) ≫ _ = _
  rw [prodComparison_natural_assoc, prod.map_map_assoc, ← w, prod.map_map_assoc]
  rfl

def LeafRepPt : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (E₁ : ∀ U : Scheme.{0}, Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
        (U ⟶ (off (Polynomial A) (I.map Polynomial.C)).toScheme))
      (E₂ : ∀ U : Scheme.{0}, Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃ (U ⟶ (off A I).toScheme)),
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₁ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₁ U (v, g)) ∧
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₂ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₂ U (v, g)) ∧
      ∀ (U : Scheme.{0}) v g, E₂ U ((Vec.tail d U).obj v, g) =
        E₁ U (v, g) ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h

def isoOfPt {F G : PSh} {X : Scheme.{0}} (E : ∀ U : Scheme.{0}, F.obj (op U) × G.obj (op U) ≃ (U ⟶ X))
    (hE : ∀ {V U : Scheme.{0}} (f : V ⟶ U) a b, E V (F.map f.op a, G.map f.op b) = f ≫ E U (a, b)) :
    F ⨯ G ≅ yoneda.obj X :=
  FunctorToTypes.binaryProductIso F G ≪≫
    NatIso.ofComponents (fun U => (E U.unop).toIso) (fun f => by
      ext ⟨a, b⟩
      exact hE f.unop a b)

theorem LeafRepVec_of (hP : LeafRepPt) : LeafRepVec := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, E₁, E₂, n₁, n₂, sq⟩ := hP d R
  refine ⟨A, inferInstance, I, φ, hI, h, isoOfPt (F := Vo (d + 1) 1) E₁ (fun f a b => n₁ f a b),
    isoOfPt (F := Vo d 0) E₂ (fun f a b => n₂ f a b), ?_⟩
  have key : prod.map (voTail d) (𝟙 (yoneda.obj (Spec (CommRingCat.of R)))) ≫
      (FunctorToTypes.binaryProductIso _ _).hom = (FunctorToTypes.binaryProductIso _ _).hom ≫
      FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ voTail d) FunctorToTypes.prod.snd := by
    apply (cancel_mono (FunctorToTypes.binaryProductIso _ _).inv).1
    apply Limits.prod.hom_ext <;> simp <;> rw [← Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_fst]
  simp only [isoOfPt, Iso.trans_hom]
  rw [reassoc_of% key, Category.assoc]
  congr 1
  ext U ⟨v, g⟩
  exact sq U.unop v g

theorem LeafTailRep0_of (hP : LeafRepPt) : LeafTailRep0 := LeafTailRep0_of_vec (LeafRepVec_of hP)

end LateralTheory.CohomologicalPurity.Thom
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Thom
namespace RepPt

def specEq (U : Scheme.{0}) (B : Type) [CommRing B] : (CommRingCat.of B ⟶ Γ(U, ⊤)) ≃ (U ⟶ Spec (CommRingCat.of B)) where
  toFun φ := ΓSpec.adjunction.homEquiv U (op (CommRingCat.of B)) φ.op
  invFun f := (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop
  left_inv φ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  right_inv f := by
    refine ext_to_Spec ?_
    simp only [Scheme.Γ_map, Quiver.Hom.unop_op]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

theorem specEq_symm_apply (U : Scheme.{0}) (B : Type) [CommRing B] (f : U ⟶ Spec (CommRingCat.of B)) :
    (specEq U B).symm f = (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop := rfl

theorem appTop_specEq (U : Scheme.{0}) (B : Type) [CommRing B] (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specEq U B φ).appTop = φ :=
  (specEq U B).left_inv φ

theorem symm_comp {V U : Scheme.{0}} (B : Type) [CommRing B] (f : V ⟶ U) (g : U ⟶ Spec (CommRingCat.of B)) :
    (specEq V B).symm (f ≫ g) = (specEq U B).symm g ≫ f.appTop := by
  simp only [specEq_symm_apply, Scheme.Hom.comp_appTop, Category.assoc]

theorem comp_specEq {V U : Scheme.{0}} (B : Type) [CommRing B] (f : V ⟶ U) (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) :
    f ≫ specEq U B φ = specEq V B (φ ≫ f.appTop) := by
  apply (specEq V B).symm.injective
  rw [symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem specEq_comp_Spec (U : Scheme.{0}) {B C : Type} [CommRing B] [CommRing C]
    (ψ : CommRingCat.of B ⟶ CommRingCat.of C) (φ : CommRingCat.of C ⟶ Γ(U, ⊤)) :
    specEq U C φ ≫ Spec.map ψ = specEq U B (ψ ≫ φ) := by
  apply (specEq U B).symm.injective
  rw [Equiv.symm_apply_apply, specEq_symm_apply, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, appTop_specEq]

theorem mem_basicOpen_specEq (U : Scheme.{0}) (B : Type) [CommRing B] (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) (b : B)
    (x : U) : (specEq U B φ x : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen b ↔ x ∈ U.basicOpen (φ b) := by
  have h := Scheme.preimage_basicOpen_top (specEq U B φ) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  rw [basicOpen_eq_of_affine] at h
  have h2 : (specEq U B φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) = φ b := by
    calc _ = ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specEq U B φ).appTop) b := rfl
      _ = φ b := by rw [appTop_specEq]
  rw [h2] at h
  rw [← h]
  rfl

theorem mem_off_iff {B : Type} [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B) (hJ : J = Ideal.span (Set.range S))
    (x : PrimeSpectrum B) : x ∈ off B J ↔ ∃ i, x ∈ PrimeSpectrum.basicOpen (S i) := by
  subst hJ
  change x ∉ PrimeSpectrum.zeroLocus _ ↔ _
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.range_subset_iff,
    PrimeSpectrum.mem_basicOpen, SetLike.mem_coe, not_forall]

theorem range_sub (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S))
    (φ : {φ : CommRingCat.of B ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (S i))}) :
    Set.range (specEq U B φ.1) ⊆ Set.range (off B J).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  obtain ⟨i, hi⟩ := φ.2 p
  exact (mem_off_iff S J hJ _).2 ⟨i, (mem_basicOpen_specEq U B φ.1 _ p).2 hi⟩

def offEq (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) :
    (U ⟶ (off B J).toScheme) ≃ {φ : CommRingCat.of B ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (S i))} where
  toFun h := ⟨(specEq U B).symm (h ≫ (off B J).ι), fun p => by
    have hp' : (h ≫ (off B J).ι) p ∈ Set.range (off B J).ι := ⟨h p, rfl⟩
    have hp : (h ≫ (off B J).ι) p ∈ off B J := by rwa [Scheme.Opens.range_ι] at hp'
    obtain ⟨i, hi⟩ := (mem_off_iff S J hJ _).1 hp
    refine ⟨i, ?_⟩
    rw [← mem_basicOpen_specEq, Equiv.apply_symm_apply]
    exact hi⟩
  invFun φ := IsOpenImmersion.lift (off B J).ι (specEq U B φ.1) (range_sub U B S J hJ φ)
  left_inv h := by
    apply (cancel_mono (off B J).ι).1
    dsimp only
    rw [IsOpenImmersion.lift_fac, Equiv.apply_symm_apply]
  right_inv φ := Subtype.ext (by
    dsimp only
    rw [IsOpenImmersion.lift_fac (off B J).ι (specEq U B φ.1) (range_sub U B S J hJ φ), Equiv.symm_apply_apply])

theorem offEq_symm_ι (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) φ :
    (offEq U B S J hJ).symm φ ≫ (off B J).ι = specEq U B φ.1 := IsOpenImmersion.lift_fac _ _ _

theorem comp_offEq_symm {V U : Scheme.{0}} (f : V ⟶ U) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) φ ψ (h : ψ.1 = φ.1 ≫ f.appTop) :
    f ≫ (offEq U B S J hJ).symm φ = (offEq V B S J hJ).symm ψ := by
  rw [← cancel_mono (off B J).ι, Category.assoc, offEq_symm_ι, offEq_symm_ι, comp_specEq, h]

open MvPolynomial in

def e₂ (d : ℕ) (R : Type) [CommRing R] (U : Scheme.{0}) : Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃
    {φ : CommRingCat.of (MvPolynomial (Fin d) R) ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (X i))} where
  toFun vg := ⟨CommRingCat.ofHom (eval₂Hom ((specEq U R).symm vg.2).hom vg.1.1), fun p => by
    obtain ⟨i, -, hi⟩ := vg.1.2 p
    exact ⟨i, by simpa using hi⟩⟩
  invFun φ := (⟨fun i => φ.1 (X i), fun p => (φ.2 p).imp fun _ h => ⟨Nat.zero_le _, h⟩⟩,
    specEq U R (CommRingCat.ofHom C ≫ φ.1))
  left_inv vg := by
    obtain ⟨v, g⟩ := vg
    refine Prod.ext (Subtype.ext (funext fun i => by simp)) ?_
    dsimp only
    conv_rhs => rw [← (specEq U R).apply_symm_apply g]
    congr 1
    ext r
    simp
  right_inv φ := by
    apply Subtype.ext
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp

open MvPolynomial in

def e₁ (d : ℕ) (R : Type) [CommRing R] (U : Scheme.{0}) : Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
    {φ : CommRingCat.of (Polynomial (MvPolynomial (Fin d) R)) ⟶ Γ(U, ⊤) //
      ∀ p : U, ∃ j, p ∈ U.basicOpen (φ (Polynomial.C (X j)))} where
  toFun vg := ⟨CommRingCat.ofHom (Polynomial.eval₂RingHom
      (eval₂Hom ((specEq U R).symm vg.2).hom (fun j => vg.1.1 j.succ)) (vg.1.1 0)), fun p => by
    obtain ⟨i, hi, hp⟩ := vg.1.2 p
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (show i ≠ 0 by rintro rfl; simp at hi)
    exact ⟨j, by simpa using hp⟩⟩
  invFun φ := (⟨(Fin.cons (φ.1 Polynomial.X) (fun j => φ.1 (Polynomial.C (X j))) : Fin (d + 1) → Γ(U, ⊤)),
      fun p => by
        obtain ⟨j, hj⟩ := φ.2 p
        exact ⟨j.succ, by simp, by simpa using hj⟩⟩,
    specEq U R (CommRingCat.ofHom (Polynomial.C.comp C) ≫ φ.1))
  left_inv vg := by
    obtain ⟨v, g⟩ := vg
    refine Prod.ext (Subtype.ext (funext fun i => Fin.cases (by simp) (fun j => by simp) i)) ?_
    dsimp only
    conv_rhs => rw [← (specEq U R).apply_symm_apply g]
    congr 1
    ext r
    simp
  right_inv φ := by
    apply Subtype.ext
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp
    · simp

theorem hJ (d : ℕ) (R : Type) [CommRing R] :
    (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map Polynomial.C =
      Ideal.span (Set.range fun j => (Polynomial.C (MvPolynomial.X j) : Polynomial (MvPolynomial (Fin d) R))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

end RepPt

open RepPt in

theorem LeafRepPt_of : LeafRepPt := by
  intro d R _
  refine ⟨MvPolynomial (Fin d) R, inferInstance, Ideal.span (Set.range MvPolynomial.X), MvPolynomial.C,
    Submodule.fg_span (Set.finite_range _), off_le_C _ _,
    fun U => (e₁ d R U).trans (offEq U _ _ _ (hJ d R)).symm,
    fun U => (e₂ d R U).trans (offEq U _ _ _ rfl).symm, ?_, ?_, ?_⟩
  · intro V U f v g
    refine (comp_offEq_symm f _ _ _ (hJ d R) _ _ ?_).symm
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [e₁, symm_comp]
      · intro i; simp [e₁, Vec.map]
    · simp [e₁, Vec.map]
  · intro V U f v g
    refine (comp_offEq_symm f _ _ _ rfl _ _ ?_).symm
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e₂, symm_comp]
    · intro i; simp [e₂, Vec.map]
  · intro U v g
    rw [← cancel_mono (off _ _).ι, Category.assoc, Scheme.Hom.resLE_comp_ι]
    simp only [Equiv.trans_apply]
    rw [offEq_symm_ι, ← Category.assoc, offEq_symm_ι, specEq_comp_Spec]
    congr 1
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e₁, e₂]
    · intro i; simp [e₁, e₂, Vec.tail]

end LateralTheory.CohomologicalPurity.Thom
end
end
