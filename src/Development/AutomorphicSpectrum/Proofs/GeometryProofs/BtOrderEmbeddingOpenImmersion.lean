import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingBaseChangeCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherian
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExists

section
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.EmbSub

section alg

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

open Classical in

noncomputable def ind (H : Subgroup T) : T → R := fun x => if x ∈ H then 1 else 0

open Classical in

noncomputable def extZero (H : Subgroup T) (a : H → R) : T → R := fun x => if h : x ∈ H then a ⟨x, h⟩ else 0

theorem ind_translate_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A) (c : T) :
    (fun x => ind (R := R) H (c * x)) ∈ B := by
  refine (hB _).2 fun t => ?_
  by_cases h : c * t ∈ H
  · have : (fun x : H => ind (R := R) H (c * (t * x))) = 1 := by
      funext x
      have : c * (t * x) ∈ H := by
        rw [← _root_.mul_assoc]
        exact H.mul_mem h x.2
      simp [ind, this]
    rw [this]
    exact A.one_mem
  · have : (fun x : H => ind (R := R) H (c * (t * x))) = 0 := by
      funext x
      have : c * (t * x) ∉ H := by
        rw [← _root_.mul_assoc]
        exact fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))
      simp [ind, this]
    rw [this]
    exact A.zero_mem

theorem extZero_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A)
    (hA : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A) {a : H → R} (ha : a ∈ A) : extZero H a ∈ B := by
  refine (hB _).2 fun t => ?_
  by_cases h : t ∈ H
  · have : (fun x : H => extZero H a (t * x)) = fun x => a (⟨t, h⟩ * x) := by
      funext x
      have h' : t * x ∈ H := H.mul_mem h x.2
      simp only [extZero, dif_pos h']
      rfl
    rw [this]
    exact hA a ha _
  · have : (fun x : H => extZero H a (t * x)) = 0 := by
      funext x
      have h' : t * x ∉ H := fun h' => h (by simpa using H.mul_mem h' (H.inv_mem x.2))
      simp [extZero, h']
    rw [this]
    exact A.zero_mem

theorem translate_mem {H : Subgroup T} {A : Subalgebra R (H → R)} {B : Subalgebra R (T → R)}
    (hB : ∀ f : T → R, f ∈ B ↔ ∀ t, (fun h : H => f (t * h)) ∈ A) {f : T → R} (hf : f ∈ B) (c : T) :
    (fun x => f (c * x)) ∈ B := by
  refine (hB _).2 fun t => ?_
  simpa only [_root_.mul_assoc] using (hB f).1 hf (c * t)

def transl {B : Subalgebra R (T → R)} (hB : ∀ f ∈ B, ∀ c : T, (fun x => f (c * x)) ∈ B) (c : T) : B →+* B where
  toFun f := ⟨fun x => (f : T → R) (c * x), hB _ f.2 c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_translate_notMem [Finite T] {H : Subgroup T} {B : Subalgebra R (T → R)}
    (he : ∀ c : T, (fun x => ind (R := R) H (c * x)) ∈ B) (P : Ideal B) [P.IsPrime] :
    ∃ t : T, (⟨_, he t⁻¹⟩ : B) ∉ P := by
  classical
  have := Fintype.ofFinite T
  have h0 : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) = 0 := by
    apply Subtype.ext
    funext x
    have hx : ((∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B)) : B) : T → R) x
        = ∏ t : T, (1 - ind (R := R) H (t⁻¹ * x)) := by
      rw [← Subalgebra.coe_val, map_prod, Finset.prod_apply]
      rfl
    rw [hx]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [ind, H.one_mem])
  have hP : (∏ t : T, (1 - (⟨_, he t⁻¹⟩ : B))) ∈ P := h0 ▸ P.zero_mem
  obtain ⟨t, -, ht⟩ := (Ideal.IsPrime.prod_mem_iff (p := P)).1 hP
  refine ⟨t, fun h => ?_⟩
  have : (1 : B) ∈ P := by
    have := P.add_mem ht h
    simpa using this
  exact (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›) this

end alg

section geom

theorem isAffineOpen_of_fin {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
    {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U) : IsAffineOpen U := by
  have := hF.finite
  have : IsAffineHom (U.ι ≫ Γ.G.hom) := inferInstance
  exact isAffine_of_isAffineHom (U.ι ≫ Γ.G.hom)

noncomputable def valRing {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valRing_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valRing x U h s = valAt x U h s := rfl

theorem spec_valRing_fromSpec {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (valRing x U h)) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : CommRingCat.ofHom (valRing x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom := rfl
  rw [this, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp]
  simp

theorem fromSpec_mem' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (z) : hU.fromSpec z ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨z, rfl⟩

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem val_pullback (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hU : IsAffineOpen U) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (ψ : CommRingCat.of A ⟶ Γ(Γ.G.left, U))
    (hψ : Spec.map ψ = hU.fromSpec ≫ j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (f : A) :
    valAt (Γ.pt t).left U h (ψ.hom f) = algebraMap R (FractionRing R) ((f : T → R) t) := by
  have e1 := spec_valRing_fromSpec (Γ.pt t).left hU h
  have e2 := hj.pt t
  rw [← e1, Category.assoc, ← hψ, ← Spec.map_comp] at e2
  have := congrArg (fun g => g.hom f) (Spec.map_injective e2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem val_mem_range [IsIntegrallyClosed R] (Γ : QFGroup R T) {U : Γ.G.left.Opens} (hF : Γ.IsFinOpenSub U)
    (hU : IsAffineOpen U) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (ψ : CommRingCat.of A ⟶ Γ(Γ.G.left, U))
    (hψ : Spec.map ψ = hU.fromSpec ≫ j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) (s : Γ(Γ.G.left, U)) :
    ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left U h s := by
  let ρ : R →+* Γ(Γ.G.left, U) := ψ.hom.comp (algebraMap R A)
  letI : Algebra R Γ(Γ.G.left, U) := ρ.toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) := by
    have e : CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U)) = CommRingCat.ofHom (algebraMap R A) ≫ ψ := rfl
    rw [e, Spec.map_comp, hψ, Category.assoc, hj.isOver]
  have := hF.finite
  have hfin : IsFinite (hU.fromSpec ≫ Γ.G.hom) := by
    rw [← hU.isoSpec_inv_ι, Category.assoc]
    infer_instance
  rw [hρ] at hfin
  have hfin' : Module.Finite R Γ(Γ.G.left, U) := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 hfin)
  have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
  have h2 : (algebraMap R (FractionRing R)).comp (RingHom.id R) =
      (valRing (Γ.pt t).left U h).comp (algebraMap R Γ(Γ.G.left, U)) := by
    ext r
    have := val_pullback Γ hU hj ψ hψ t h (algebraMap R A r)
    exact this.symm
  have h3 : IsIntegral R (valRing (Γ.pt t).left U h s) := h1.map_of_comp_eq _ _ h2
  exact IsIntegrallyClosed.isIntegral_iff.1 h3

end geom

end GlobalTheory.CompanionTheory.Ar.BT.EmbSub

namespace GlobalTheory.CompanionTheory.Ar.BT.EmbSub

theorem openImmersion_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion (U.ι ≫ j) ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j U := by
  intro R _ _ _ T _ _ Γ U hF j hj
  obtain ⟨H, A, hH, hA, hAs⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hF
  have hU := isAffineOpen_of_fin Γ hF
  have hTr : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := GlobalTheory.T.hopf_order_translation_invariant R H A hA
  have hB : ∀ f : T → R, f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h : H => f (t * h)) ∈ A := by
    intro f
    rw [← GlobalTheory.T.btOrder_eq_btOrder_top R T Γ U hF, GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)
      exact (hAs _).2 ⟨s, fun x h => hs x h⟩
    · intro hf t
      obtain ⟨s, hs⟩ := (hAs _).1 (hf t)
      exact (GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ⟨s, fun x h => hs ⟨x, (hH x).2 h⟩ h⟩
  let ψ : CommRingCat.of (Γ.btOrder ⊤) ⟶ Γ(Γ.G.left, U) := Spec.preimage (hU.fromSpec ≫ j)
  have hψ : Spec.map ψ = hU.fromSpec ≫ j := Spec.map_preimage _
  have hv := val_pullback Γ hU hj ψ hψ
  have hi := val_mem_range Γ hF hU hj ψ hψ
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hsurj : Function.Surjective ψ.hom := by
    intro s
    choose a ha using fun t : H => hi t ((hH t).1 t.2) s
    have haA : a ∈ A := (hAs a).2 ⟨s, fun t h => (ha t).symm⟩
    refine ⟨⟨extZero H a, extZero_mem hB hTr haA⟩, ?_⟩
    rw [← sub_eq_zero]
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_
    have ht : t ∈ H := (hH t).2 h
    rw [← valRing_apply, map_sub, valRing_apply, valRing_apply, hv t h, ← ha ⟨t, ht⟩]
    simp [extZero, ht]
  have hz : ∀ f : Γ.btOrder ⊤, ψ.hom f = 0 ↔ ∀ t ∈ H, (f : T → R) t = 0 := by
    intro f
    constructor
    · intro hf t ht
      have := hv t ((hH t).1 ht) f
      rw [hf, ← valRing_apply, map_zero] at this
      exact inj (by rw [← this, map_zero])
    · intro hf
      refine GlobalTheory.T.section_eq_zero_of_values R T Γ U _ fun t h => ?_
      rw [hv t h, hf t ((hH t).2 h), map_zero]
  let e : Γ.btOrder ⊤ := ⟨_, ind_translate_mem hB 1⟩
  have he1 : ∀ x ∈ H, (e : T → R) x = 1 := fun x hx => by simp [e, ind, hx]
  have he0 : ∀ x, x ∉ H → (e : T → R) x = 0 := fun x hx => by simp [e, ind, hx]
  have hidem : IsIdempotentElem e := by
    apply Subtype.ext
    funext x
    change (e : T → R) x * (e : T → R) x = (e : T → R) x
    by_cases hx : x ∈ H
    · simp [he1 x hx]
    · simp [he0 x hx]
  have hker : RingHom.ker ψ.hom = Ideal.span {1 - e} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton', hz]
    constructor
    · intro hf
      refine ⟨f, Subtype.ext (funext fun x => ?_)⟩
      change (f : T → R) x * (1 - (e : T → R) x) = (f : T → R) x
      by_cases hx : x ∈ H
      · simp [hf x hx]
      · simp [he0 x hx]
    · rintro ⟨b, rfl⟩ t ht
      change (b : T → R) t * (1 - (e : T → R) t) = 0
      simp [he1 t ht]
  have hoi : IsOpenImmersion (Spec.map ψ) :=
    (isOpenImmersion_SpecMap_iff_of_surjective ψ hsurj).2 ⟨1 - e, hidem.one_sub, hker⟩
  refine ⟨?_, ?_⟩
  · have : U.ι ≫ j = hU.isoSpec.hom ≫ Spec.map ψ := by
      rw [hψ, ← hU.isoSpec_inv_ι]
      simp
    rw [this]
    infer_instance
  · intro P
    have hBt : ∀ f ∈ Γ.btOrder ⊤, ∀ c : T, (fun x => f (c * x)) ∈ Γ.btOrder ⊤ :=
      fun f hf c => translate_mem hB hf c
    obtain ⟨t, ht⟩ := exists_translate_notMem (B := Γ.btOrder ⊤) (H := H) (ind_translate_mem hB) P.asIdeal
    let Q : Ideal (Γ.btOrder ⊤) := P.asIdeal.comap (transl hBt t⁻¹)
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have heQ : e ∉ Q := by
      intro h
      apply ht
      have : transl hBt t⁻¹ e = ⟨_, ind_translate_mem hB t⁻¹⟩ :=
        Subtype.ext (funext fun x => by simp [transl, e])
      rw [← this]
      exact h
    have h1e : 1 - e ∈ Q := by
      have h0 : e * (1 - e) ∈ Q := by
        rw [mul_sub, _root_.mul_one, hidem.eq, sub_self]
        exact Q.zero_mem
      exact (hQ.mem_or_mem h0).resolve_left heQ
    have hk : RingHom.ker ψ.hom ≤ Q := by
      rw [hker, Ideal.span_singleton_le_iff_mem]
      exact h1e
    obtain ⟨Q', hQ'⟩ : (⟨Q, hQ⟩ : PrimeSpectrum (Γ.btOrder ⊤)) ∈ Set.range (PrimeSpectrum.comap ψ.hom) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact hk
    refine ⟨t, hU.fromSpec Q', fromSpec_mem' hU _, fun f f' hff => ?_⟩
    have hjg : (j (hU.fromSpec Q')).asIdeal = Q := by
      have h1 : j (hU.fromSpec Q') = (Spec.map ψ) Q' := by
        rw [hψ]
        rfl
      rw [h1]
      exact congrArg PrimeSpectrum.asIdeal hQ'
    rw [hjg]
    have h2 : transl hBt t⁻¹ f' = f :=
      Subtype.ext (funext fun x => by
        change (f' : T → R) (t⁻¹ * x) = (f : T → R) x
        rw [hff, mul_inv_cancel_left])
    change f ∈ P.asIdeal ↔ transl hBt t⁻¹ f' ∈ P.asIdeal
    rw [h2]

end GlobalTheory.CompanionTheory.Ar.BT.EmbSub
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_embedding_open_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion (U.ι ≫ j) ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.EmbSub.openImmersion_translatesCover
end

section
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btEmb_localData (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (R' : Type) [CommRing R'] [IsDomain R'] [HenselianLocalRing R'] [Algebra R R']
    [IsIntegrallyClosed R'] (hflat : Module.Flat R R') :
    ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of (Γ'.btOrder ⊤)))
      (ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤) (U : Γ'.G.left.Opens),
      (∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) ∧
      IsOpenImmersion (U.ι ≫ j') ∧ Γ'.TranslatesCover (Γ'.btOrder ⊤) j' U ∧
      ∀ x : Γ'.G.left, Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) (j' x) =
        IsLocalRing.closedPoint R' → x ∈ U := by
  have hA := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  have hinj : Function.Injective (algebraMap R R') := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hreg : IsSMulRegular R' r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R') (mem_nonZeroDivisors_of_ne_zero hr0)
    have : r • (1 : R') = r • (0 : R') := by
      simp [Algebra.smul_def, hr]
    exact one_ne_zero (hreg this)
  obtain ⟨Γ', F, hbc⟩ := GlobalTheory.T.exists_base_change_group R T Γ R' (algebraMap R R') hinj
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := GlobalTheory.T.henselian_quasi_finite_finite_part R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := GlobalTheory.T.isFinOpenSub_of_finite R' T Γ' U hUfin hUcl
  obtain ⟨j', hj'⟩ := (GlobalTheory.T.existsUnique_btOrder_embedding R' T Γ').exists
  have hbt := GlobalTheory.T.btOrder_flat_base_change R T Γ R' Γ' F hbc hflat
  have hfull : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
    obtain ⟨d, hd, hf⟩ := hA.full
    exact ⟨d, fun h => hd (hinj (by simpa using h)), hf⟩
  have hext := (GlobalTheory.T.hopf_order_scalar_extension R T R' (Γ.btOrder ⊤) hA hfull).2
  have hext' : ∃ e : R' ⊗[R] (Γ.btOrder ⊤) ≃ₐ[R'] Γ'.btOrder ⊤,
      ∀ (a : Γ.btOrder ⊤) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
    rw [hbt]; exact hext
  obtain ⟨e, he⟩ := hext'
  let iL : R' →+* R' ⊗[R] (Γ.btOrder ⊤) := Algebra.TensorProduct.includeLeftRingHom
  let iR : (Γ.btOrder ⊤) →+* R' ⊗[R] (Γ.btOrder ⊤) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Γ.btOrder ⊤)).toRingHom
  let ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤ := (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤).comp iR
  have hψ : ∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t) := fun a t => he a t
  have sq : IsPullback (Spec.map (CommRingCat.ofHom iL)) (Spec.map (CommRingCat.ofHom iR))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (Γ.btOrder ⊤))
  let eH : CommRingCat.of (R' ⊗[R] (Γ.btOrder ⊤)) ⟶ CommRingCat.of (Γ'.btOrder ⊤) :=
    CommRingCat.ofHom (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤)
  haveI : IsIso eH := (e.toRingEquiv.toCommRingCatIso).isIso_hom
  have hb : Spec.map (CommRingCat.ofHom ψ) = Spec.map eH ≫ Spec.map (CommRingCat.ofHom iR) := by
    rw [← Spec.map_comp]; rfl
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) =
      Spec.map eH ≫ Spec.map (CommRingCat.ofHom iL) := by
    rw [← Spec.map_comp]
    congr 2
    ext r t
    exact congrArg (fun y : Γ'.btOrder ⊤ => y.1 t) (e.commutes r).symm
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    refine IsPullback.of_iso sq.flip (asIso (Spec.map eH)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hb]
    · simp [hq]
    · simp
    · simp
  have hw : F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) :=
    GlobalTheory.T.embedding_base_change_compat R T Γ R' Γ' F hbc _ _ ψ hψ j j' hj hj'
  have hsq2 : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hw hsq
    rw [hj'.isOver, hj.isOver]
    exact hbc.cart
  obtain ⟨ho, hTC⟩ := GlobalTheory.T.btOrder_embedding_open_cover R' T Γ' U hU j' hj'
  refine ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, ho, hTC, fun x hx => hUcl x ?_⟩
  rw [← hj'.isOver]
  simpa using hx

theorem btEmb_specMap_asIdeal {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom φ) x).asIdeal = Ideal.comap φ x.asIdeal := rfl

theorem isOpenImmersion_emb_and_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  intro R _ _ _ _ T _ _ Γ j hj
  have hA := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  refine ⟨?_, ?_⟩
  · haveI := hA.finite
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    haveI : LocallyOfFinitePresentation (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [hj.isOver]; exact Γ.finPres
    haveI := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
    refine GlobalTheory.T.flat_local_extension_exists R Γ.G.left _ j (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) ?_
    intro P _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R P
    obtain ⟨Γ', F, j', ψ, U, -, hsq, hsq2, ho, -, hcl⟩ := btEmb_localData R T Γ j hj R' hflat
    exact ⟨R', inferInstance, inferInstance, inferInstance, Γ'.G.left, _, j', _, F, _, U, hflat, hcomap, hsq, hsq2, ho, hcl⟩
  · intro P
    let p : Ideal R := P.asIdeal.comap (algebraMap R (Γ.btOrder ⊤))
    haveI : p.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R p
    obtain ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, -, hTC, -⟩ := btEmb_localData R T Γ j hj R' hflat
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R R'))) P (IsLocalRing.closedPoint R')
      (PrimeSpectrum.ext hcomap.symm)
    let Q := hsq.isoPullback.inv z
    have hQ : Spec.map (CommRingCat.ofHom ψ) Q = P := by
      rw [← hz1]
      change (hsq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom ψ)) z = _
      rw [hsq.isoPullback_inv_fst]
    obtain ⟨t, g', -, H⟩ := hTC Q
    refine ⟨t, F g', trivial, fun f f' hff => ?_⟩
    have h1 := H (ψ f) (ψ f') (fun h => by rw [hψ, hψ, hff])
    have hg : (j (F g')).asIdeal = Ideal.comap ψ (j' g').asIdeal := by
      rw [← btEmb_specMap_asIdeal]
      change ((F ≫ j) g').asIdeal = ((j' ≫ Spec.map (CommRingCat.ofHom ψ)) g').asIdeal
      rw [hsq2.w]
    rw [hg, ← hQ, btEmb_specMap_asIdeal]
    exact h1

end GlobalTheory.CompanionTheory.Ar.BT
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_embedding_open_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover
end
