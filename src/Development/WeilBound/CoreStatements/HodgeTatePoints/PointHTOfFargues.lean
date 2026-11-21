import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedDivisibleGroupExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionTwo
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingBaseChangeCompat
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEvalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFour
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFive
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRing

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Ge.EmbSub
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

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

end PositivityTheory.HtPt.Ge.EmbSub

namespace PositivityTheory.HtPt.Ge.EmbSub
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

theorem openImmersion_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion (U.ι ≫ j) ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j U := by
  intro R _ _ _ T _ _ Γ U hF j hj
  obtain ⟨H, A, hH, hA, hAs⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hF
  have hU := isAffineOpen_of_fin Γ hF
  have hTr : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := GlobalTheory.T.hopf_order_translation_invariant R H A hA
  have hB : ∀ f : T → R, f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h : H => f (t * h)) ∈ A := by
    intro f
    rw [← Htat.bt_sub_eq_top R T Γ U hF, GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
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

end PositivityTheory.HtPt.Ge.EmbSub
end

section
noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)
  {V V' : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']

theorem exists_der (ρ : B →ₐ[R] TrivSqZeroExt R V) (h : ∀ f, (ρ f).fst = ε f) :
    ∃ ψ : (RingHom.ker ε).Cotangent →ₗ[R] V, derRing ε ψ = ρ := by
  have hz : ∀ x ∈ (RingHom.ker ε) ^ 2, (ρ x).snd = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      have h1 : (ρ a).fst = 0 := (h a).trans ha
      have h2 : (ρ b).fst = 0 := (h b).trans hb
      rw [map_mul, TrivSqZeroExt.snd_mul, h1, h2]
      simp
    · intro a b ha hb
      rw [map_add, TrivSqZeroExt.snd_add, ha, hb, add_zero]
  let d : RingHom.ker ε →ₗ[R] V :=
    { toFun := fun f => (ρ f.1).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
  let tC : RingHom.ker ε →ₗ[R] (RingHom.ker ε).Cotangent :=
    { toFun := fun f => (RingHom.ker ε).toCotangent f
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => by
        have : r • a = (algebraMap R B r) • a := (algebraMap_smul B r a).symm
        rw [this, map_smul]
        exact algebraMap_smul B r _ }
  have hs : Function.Surjective tC := Ideal.toCotangent_surjective _
  have hk : LinearMap.ker tC ≤ LinearMap.ker d := by
    intro a ha
    exact hz _ ((Ideal.toCotangent_eq_zero _ _).1 ha)
  let ψ : (RingHom.ker ε).Cotangent →ₗ[R] V :=
    ((LinearMap.ker tC).liftQ d hk) ∘ₗ (tC.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hψ : ∀ a, ψ (tC a) = d a := by
    intro a
    have : (tC.quotKerEquivOfSurjective hs).symm (tC a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨ψ, AlgHom.ext fun f => ?_⟩
  rw [derRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [h]
  · have : ψ ((RingHom.ker ε).toCotangent (augPart ε f)) = d (augPart ε f) := hψ _
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, this]
    change (ρ (f - algebraMap R B (ε f))).snd = _
    rw [map_sub, AlgHom.commutes, TrivSqZeroExt.snd_sub]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem derRing_comp (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (π : V →ₗ[R] V') (f : B) :
    TrivSqZeroExt.map π (derRing ε ψ f) = derRing ε (π ∘ₗ ψ) f := by
  rw [derRing_apply, derRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp
end Alg

end PositivityTheory.HtPt.Ge.Tan

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

theorem one_left_eq {B : Scheme.{0}} {X M : Over B} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

section Rel
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
  {V V' : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  [AddCommGroup V'] [Module R V'] [Module Rᵐᵒᵖ V'] [IsCentralScalar R V']

include Γ in
theorem unit_i (ht : Γ.IsTorsionAlong G x N i) (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let w : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    change ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, ht.isOver, ← Category.assoc, Over.w])
  have h := ht.mul Y 1 1 w w rfl rfl
  rw [_root_.mul_one] at h
  have h1 : w * w = w * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h
  have h2 : w = 1 := mul_left_cancel h1
  exact congrArg CommaMorphism.left h2

theorem unit_i' (ht : Γ.IsTorsionAlong G x N i) : η[Γ.G].left ≫ i = x ≫ η[G].left := by
  have h := unit_i Γ ht (Over.mk (𝟙 _))
  rw [one_left_eq, one_left_eq] at h
  simpa using h

theorem unit_j (hj : Γ.IsEmb (Γ.btOrder ⊤) j) :
    η[Γ.G].left ≫ j = Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
  have h1 : (Γ.pt 1).left = (genPt R).hom ≫ η[Γ.G].left := by
    rw [map_one, one_left_eq]
  have h2 := hj.pt 1
  rw [h1, Category.assoc] at h2
  let ρ := Spec.preimage (η[Γ.G].left ≫ j)
  have hρ : Spec.map ρ = η[Γ.G].left ≫ j := Spec.map_preimage _
  rw [← hρ]
  rw [← hρ] at h2
  change Spec.map _ ≫ Spec.map ρ = _ at h2
  rw [← Spec.map_comp] at h2
  have h3 := Spec.map_injective h2
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  have h4 := congrArg (fun g => g.hom f) h3
  exact IsFractionRing.injective R (FractionRing R) h4

theorem zsec_surj : Function.Surjective (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom R R V).toRingHom)) := by
  intro p
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R (TrivSqZeroExt R V)) p
  refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (TrivSqZeroExt R V) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  set b := algebraMap R (TrivSqZeroExt R V) a.fst with hb
  have h0 : (b - a).fst = 0 := by simp [hb, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : b - a ∈ p.asIdeal := by
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : (b - a) ^ 2 = 0 := by
      rw [pow_two]
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h0]
    rw [this]; exact zero_mem _
  constructor
  · intro h; simpa using p.asIdeal.sub_mem h hm
  · intro h; simpa using p.asIdeal.add_mem hm h

theorem spec_fst_comp (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) =
    Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (congrArg TrivSqZeroExt.fst (derRing_apply (ev1 Γ) ψ f)).trans (by simp)

theorem spec_alg_comp (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (derRing (ev1 Γ) ψ).commutes r

theorem rel_of_torsion (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (v : ob x V ⟶ G) (h1 : zsec x ≫ v = 1) (hN : v ^ N = 1) :
    ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, TanRel Γ i j ψ v := by
  obtain ⟨y', hy'⟩ := (ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).1 hN
  let y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left := y'.left
  have y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := Over.w y'
  have y3 : y ≫ i = v.left := hy'
  let ρ₀ := Spec.preimage (y ≫ j)
  have hρ : Spec.map ρ₀ = y ≫ j := Spec.map_preimage _
  have hc : CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)) ≫ ρ₀ =
      CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, Category.assoc, hj.isOver, y1]
  let ρ : (Γ.btOrder ⊤) →ₐ[R] TrivSqZeroExt R V :=
    { ρ₀.hom with
      commutes' := fun r => congrArg (fun g => g.hom r) hc }
  let a := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have e1 : a ≫ y = η[Γ.G].left := by
    have := ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by
        change (a ≫ y) ≫ Γ.G.hom = 𝟙 _
        rw [Category.assoc, y1, ha])) 1 (by
      rw [one_left_eq]
      simp only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]
      rw [unit_i' Γ ht, y3]
      have := congrArg Over.Hom.left h1
      rw [one_left_eq, Over.comp_left] at this
      exact this)
    have h := congrArg Over.Hom.left this
    rw [one_left_eq] at h
    simpa using h
  have hfst : ∀ f, (ρ f).fst = ev1 Γ f := by
    have h2 : Spec.map (ρ₀ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) =
        Spec.map (CommRingCat.ofHom (ev1 Γ).toRingHom) := by
      rw [Spec.map_comp, hρ, ← Category.assoc, e1, unit_j Γ hj]
    have h3 := Spec.map_injective h2
    intro f
    exact congrArg (fun g => g.hom f) h3
  obtain ⟨ψ, hψ⟩ := exists_der (ev1 Γ) ρ hfst
  refine ⟨ψ, y, y1, ?_, y3⟩
  rw [hψ, ← hρ]
  rfl

theorem rel_unique (ht : Γ.IsTorsionAlong G x N i) {ψ ψ' : omega (Γ.btOrder ⊤) →ₗ[R] V} {v : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ' v) : ψ = ψ' := by
  obtain ⟨y, a, b, c⟩ := h
  obtain ⟨y', a', b', c'⟩ := h'
  have e := ht.inj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) (Over.homMk y a)
    (Over.homMk y' a') (by simpa using c.trans c'.symm)
  have e' : y = y' := congrArg CommaMorphism.left e
  rw [e', b'] at b
  have h3 := Spec.map_injective b
  apply derRing_injective (ev1 Γ)
  apply AlgHom.ext
  intro f
  exact (congrArg (fun g => g.hom f) h3).symm

theorem rel_map {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v : ob x V ⟶ G} (h : TanRel Γ i j ψ v) (π : V →ₗ[R] V') :
    TanRel Γ i j (π ∘ₗ ψ) (hom x π ≫ v) := by
  obtain ⟨y, a, b, c⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map π).toRingHom) ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc, a, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (TrivSqZeroExt.map π).commutes r
  · rw [Category.assoc, b, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact derRing_comp (ev1 Γ) ψ π f
  · rw [Category.assoc, c]
    rfl

end Rel

end PositivityTheory.HtPt.Ge.Tan

noncomputable section
namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

theorem hom_add' {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
    [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  GlobalTheory.T.hom_add_mul_of_unit_section S R x G P V u hu f g

theorem val_of_emb {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)) (hs : Γ.HasValues s (f : T → R))
    {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B)
    (h : y ≫ j = Spec.map (CommRingCat.ofHom ρ)) : valAt y ⊤ le_top s = ρ f :=
  GlobalTheory.T.bt_order_value_eval R T Γ j hj f s hs B y ρ h

theorem dual_eq_smul {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Projective R L] (N : ℕ)
    (d : Module.Dual R L) (h : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) (d e) = 0) :
    ∃ u : Module.Dual R L, d = N • u := by
  let I : Ideal R := Ideal.span {(N : R)}
  have hI : ∀ e, d e ∈ I := fun e => Ideal.Quotient.eq_zero_iff_mem.1 (h e)
  let g : L →ₗ[R] I := d.codRestrict I hI
  let p : R →ₗ[R] I := ((N : R) • (LinearMap.id : R →ₗ[R] R)).codRestrict I (fun r => by
    simpa using Ideal.mul_mem_right r I (Ideal.mem_span_singleton_self _))
  have hp : Function.Surjective p := by
    rintro ⟨a, ha⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨r, Subtype.ext (by simp [p, mul_comm])⟩
  obtain ⟨u, hu⟩ := Module.projective_lifting_property p g hp
  refine ⟨u, ?_⟩
  ext e
  have := congrArg Subtype.val (LinearMap.congr_fun hu e)
  simpa [p, g] using this.symm

end PositivityTheory.HtPt.Ge.Tan

namespace PositivityTheory.HtPt.Ge.Tan
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Core
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
  {P : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

theorem hom_nsmul (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V]
    [IsCentralScalar R V] (φ : P →ₗ[R] V) (n : ℕ) : hom x (n • φ) ≫ u = (hom x φ ≫ u) ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero, hom_zero, Category.assoc, hu, MonObj.comp_one]
  | succ n ih => rw [succ_nsmul, hom_add' x G u hu, ih, pow_succ]

theorem hom_zero_comp (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V]
    [IsCentralScalar R V] : hom x (0 : P →ₗ[R] V) ≫ u = 1 := by
  rw [hom_zero, Category.assoc, hu, MonObj.comp_one]

end Core

end PositivityTheory.HtPt.Ge.Tan
end
end
end
end

section
noncomputable section

namespace PositivityTheory.HtPt.Ge.TwDer
open GlobalTheory.CompanionTheory PositivityTheory.HtPt.Ge.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

section Rel
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (U : Γ.G.left.Opens)
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem fst_comp_eq_unit (ht : Γ.IsTorsionAlong G x N i) {y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left}
    (y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))
    {v : ob x V ⟶ G} (y3 : y ≫ i = v.left) (h1 : zsec x ≫ v = 1) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y = η[Γ.G].left := by
  let a := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom)
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have := ht.inj (Over.mk (𝟙 _)) (Over.homMk (a ≫ y) (by
      change (a ≫ y) ≫ Γ.G.hom = 𝟙 _
      rw [Category.assoc, y1, ha])) 1 (by
    rw [one_left_eq]
    simp only [Over.homMk_left, Over.mk_hom, Category.id_comp, Category.assoc]
    rw [unit_i' Γ ht, y3]
    have := congrArg Over.Hom.left h1
    rw [one_left_eq, Over.comp_left] at this
    exact this)
  have h := congrArg Over.Hom.left this
  rw [one_left_eq] at h
  simpa [a] using h

theorem mem_of_fst_comp {y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left}
    (e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y = η[Γ.G].left)
    (hU : ∀ z, η[Γ.G].left z ∈ U) (z) : y z ∈ U := by
  obtain ⟨z', rfl⟩ := zsec_surj (R := R) (V := V) z
  have e2 : y (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = η[Γ.G].left z' :=
    congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e
  rw [e2]
  exact hU z'

theorem rel_exists_open (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    ∃ v : ob x V ⟶ G, zsec x ≫ v = 1 ∧ v ^ N = 1 ∧ TanRel Γ i j ψ v := by
  set f₀ := Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) with hf₀
  have hr : Set.range f₀ ⊆ Set.range (U.ι ≫ j) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', rfl⟩ := zsec_surj (R := R) (V := V) z
    have e := spec_fst_comp Γ ψ
    rw [← unit_j Γ hj] at e
    have e2 : f₀ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) z') = j (η[Γ.G].left z') := by
      exact congrArg (fun k : Spec (CommRingCat.of R) ⟶ _ => k z') e
    refine ⟨⟨_, hU z'⟩, ?_⟩
    exact e2.symm
  let y' := IsOpenImmersion.lift (U.ι ≫ j) f₀ hr
  have y'j : y' ≫ U.ι ≫ j = f₀ := IsOpenImmersion.lift_fac (U.ι ≫ j) f₀ hr
  let y := y' ≫ U.ι
  have yj : y ≫ j = f₀ := by simpa [y] using y'j
  have y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) := by
    rw [← hj.isOver, ← Category.assoc, yj]
    exact spec_alg_comp Γ ψ
  let v : ob x V ⟶ G := Over.homMk (y ≫ i) (by
    change (y ≫ i) ≫ G.hom = _ ≫ x
    rw [Category.assoc, ht.isOver, ← Category.assoc, y1])
  refine ⟨v, ?_, ?_, y, y1, yj, rfl⟩
  · have rη : Set.range η[Γ.G].left ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hU z
    have hl := IsOpenImmersion.lift_fac U.ι η[Γ.G].left rη
    have e0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y' =
        IsOpenImmersion.lift U.ι η[Γ.G].left rη := by
      rw [← cancel_mono (U.ι ≫ j), Category.assoc, y'j, ← Category.assoc (IsOpenImmersion.lift U.ι η[Γ.G].left rη), hl,
        unit_j Γ hj]
      exact spec_fst_comp Γ ψ
    have e1 : (zsec x : Over.mk x ⟶ ob x V).left ≫ y = η[Γ.G].left := by
      change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y' ≫ U.ι = _
      rw [← Category.assoc, e0, hl]
    apply Over.OverMorphism.ext
    rw [one_left_eq, Over.comp_left]
    change (zsec x : Over.mk x ⟶ ob x V).left ≫ y ≫ i = x ≫ _
    rw [← Category.assoc, e1, unit_i' Γ ht]
  · exact (ht.kernel (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))) v).2
      ⟨Over.homMk y y1, rfl⟩

theorem rel_eq_open (ht : Γ.IsTorsionAlong G x N i) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v v' : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ v') (h1 : zsec x ≫ v = 1) (h1' : zsec x ≫ v' = 1) : v = v' := by
  obtain ⟨y, a, b, c⟩ := h
  obtain ⟨y', a', b', c'⟩ := h'
  have m := mem_of_fst_comp Γ U (fst_comp_eq_unit Γ ht a c h1) hU
  have m' := mem_of_fst_comp Γ U (fst_comp_eq_unit Γ ht a' c' h1') hU
  have r : Set.range y ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact m z
  have r' : Set.range y' ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact m' z
  have hl := IsOpenImmersion.lift_fac U.ι y r
  have hl' := IsOpenImmersion.lift_fac U.ι y' r'
  have e : IsOpenImmersion.lift U.ι y r = IsOpenImmersion.lift U.ι y' r' := by
    rw [← cancel_mono (U.ι ≫ j), ← Category.assoc, ← Category.assoc, hl, hl', b, b']
  apply Over.OverMorphism.ext
  rw [← c, ← c', ← hl, ← hl', e]

end Rel

section Core
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (U : Γ.G.left.Opens)
  {P : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

theorem exists_theta_open (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1)
    (huniv : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G),
      zsec x ≫ v = 1 → ∃! φ : P →ₗ[R] V, hom x φ ≫ u = v) :
    ∃ θ : P →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ N • θ = 0 ∧
      ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (φ : P →ₗ[R] V), N • φ = 0 →
        ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, ψ ∘ₗ θ = φ ∧ TanRel Γ i j ψ (hom x φ ≫ u) := by
  letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤)) := opMod R _
  haveI : IsCentralScalar R (omega (Γ.btOrder ⊤)) := opCentral R _
  obtain ⟨v₀, hv₀, hvN, hrel⟩ := rel_exists_open Γ U ht hj hU (LinearMap.id : omega (Γ.btOrder ⊤) →ₗ[R] omega (Γ.btOrder ⊤))
  obtain ⟨θ, hθ, -⟩ := huniv _ v₀ hv₀
  have nat : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
      (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), TanRel Γ i j ψ (hom x (ψ ∘ₗ θ) ≫ u) := by
    intro V _ _ _ _ ψ
    have := rel_map Γ hrel ψ
    rwa [LinearMap.comp_id, ← hθ, ← Category.assoc, LieEx.hom_comp] at this
  have zero : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
      (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V), ψ ∘ₗ θ = 0 → ψ = 0 := by
    intro V _ _ _ _ ψ h
    have h1 := nat V ψ
    have h2 := nat V 0
    rw [h] at h1
    rw [LinearMap.zero_comp] at h2
    exact rel_unique Γ ht h1 h2
  have hN : N • θ = 0 := by
    have h1 : hom x (N • θ) ≫ u = 1 := by rw [hom_nsmul u hu, hθ, hvN]
    have h2 : hom x (0 : P →ₗ[R] omega (Γ.btOrder ⊤)) ≫ u = 1 := hom_zero_comp u hu
    have hz : zsec x ≫ (1 : ob x (omega (Γ.btOrder ⊤)) ⟶ G) = 1 := MonObj.comp_one _
    exact (huniv _ 1 hz).unique h1 h2
  refine ⟨θ, ?_, hN, ?_⟩
  · letI : Module Rᵐᵒᵖ (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opMod R _
    haveI : IsCentralScalar R (omega (Γ.btOrder ⊤) ⧸ LinearMap.range θ) := opCentral R _
    have := zero _ (LinearMap.range θ).mkQ (by
      ext w
      simp)
    rw [← LinearMap.range_eq_top, ← Submodule.ker_mkQ (LinearMap.range θ), this, LinearMap.ker_zero]
  · intro V _ _ _ _ φ hφ
    have h1 : zsec x ≫ hom x φ ≫ u = 1 := by rw [← Category.assoc, zsec_hom, hu]
    have h2 : (hom x φ ≫ u) ^ N = 1 := by rw [← hom_nsmul u hu, hφ, hom_zero_comp u hu]
    obtain ⟨ψ, hψ⟩ := rel_of_torsion Γ ht hj _ h1 h2
    have h3 := rel_eq_open Γ U ht hU hψ (nat V ψ) h1 (by rw [← Category.assoc, zsec_hom, hu])
    refine ⟨ψ, (huniv V _ h1).unique h3.symm rfl, hψ⟩

end Core

theorem omega_open {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (ht : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L]
    [Module.Projective R L] (M : LieModel G x L) {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (U : Γ.G.left.Opens) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)] :
    ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f.1.1 : T → R) → (θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) → v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))) := by
  obtain ⟨u, hu, hupin, huniv⟩ := GlobalTheory.T.dual_lattice_point_universal S G R x L M
  obtain ⟨θ, hsurj, hNθ, hlift⟩ := exists_theta_open Γ U ht hj hU u hu huniv
  have hθN : ∀ w', θ (N • w') = 0 := fun w' => by
    have := LinearMap.congr_fun hNθ w'
    simpa using this
  have hker : ∀ w, θ w = 0 ↔ ∃ u', w = N • u' := by
    intro w
    constructor
    · intro hw
      let W : Submodule R (Module.Dual R L) := LinearMap.range ((N : R) • (LinearMap.id : Module.Dual R L →ₗ[R] Module.Dual R L))
      have h0 : N • W.mkQ = 0 := by
        ext w'
        simp only [LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.comp_apply]
        exact (map_nsmul W.mkQ N w').symm.trans ((Submodule.Quotient.mk_eq_zero W).2 ⟨w', by simp [Nat.cast_smul_eq_nsmul]⟩)
      obtain ⟨ψ, hψ, -⟩ := hlift _ W.mkQ h0
      have h1 : W.mkQ w = 0 := by
        rw [← hψ, LinearMap.comp_apply, hw, map_zero]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨u', rfl⟩ := h1
      exact ⟨u', by simp [Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨u', rfl⟩
      exact hθN u'
  have hkey : ∀ e : L, ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}),
      (∀ w, ψ (θ w) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)) ∧
      ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
        v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left ∧
        v ≫ j = Spec.map (CommRingCat.ofHom
          ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) := by
    intro e
    let mkL : R →ₗ[R] (R ⧸ Ideal.span {(N : R)}) := (Ideal.Quotient.mkₐ R (Ideal.span {(N : R)})).toLinearMap
    let φ : Module.Dual R L →ₗ[R] (R ⧸ Ideal.span {(N : R)}) := mkL ∘ₗ Module.Dual.eval R L e
    have h0 : N • φ = 0 := by
      ext w'
      simp only [φ, mkL, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.zero_apply]
      rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul R, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨ψ, hψ, y, y1, y2, y3⟩ := hlift _ φ h0
    refine ⟨ψ, fun w => by simpa [φ, mkL] using LinearMap.congr_fun hψ w, Spec.map (CommRingCat.ofHom (kap _).toRingHom) ≫ y, ?_, ?_, ?_⟩
    · rw [Category.assoc, y1, ← Spec.map_comp]
      congr 1
      ext r : 2
      exact kap_algebraMap _ r
    · have e1 : hom x φ ≫ u = hom x mkL ≫ M.pt e := by
        rw [← hupin e, ← Category.assoc, LieEx.hom_comp]
      rw [Category.assoc, y3, e1]
      change _ ≫ Spec.map _ ≫ (M.pt e).left = _
      have e2 : CommRingCat.ofHom (TrivSqZeroExt.map mkL).toRingHom ≫ CommRingCat.ofHom (kap (Ideal.span {(N : R)})).toRingHom =
          CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)}))) := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        exact kap_map _ a
      rw [← Category.assoc, ← Spec.map_comp, e2]
    · rw [Category.assoc, y2, ← Spec.map_comp]
      rfl
  have huniq : ∀ (e : L) (v v' : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left),
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) →
      v' ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) →
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left →
      v' ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left →
      v = v' := by
    intro e v v' h1 h1' h2 h2'
    have := ht.inj (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
          (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _)))))
      (Over.homMk v h1) (Over.homMk v' h1') (by simpa using h2.trans h2'.symm)
    exact congrArg CommaMorphism.left this
  refine ⟨θ, hsurj, hker, ?_⟩
  intro f w s hs
  have hval : ∀ (ψ : omega (Γ.btOrder ⊤) →ₗ[R] (R ⧸ Ideal.span {(N : R)}))
      (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left),
      v ≫ j = Spec.map (CommRingCat.ofHom
          ((kap (Ideal.span {(N : R)})).toRingHom.comp (derRing (ev1 Γ) ψ).toRingHom)) →
      valAt v ⊤ le_top s = TrivSqZeroExt.inr (ψ ((augIdeal (Γ.btOrder ⊤)).toCotangent f)) := by
    intro ψ v hv
    rw [val_of_emb Γ hj f.1 s hs v _ hv]
    change kap _ (derRing (ev1 Γ) ψ f.1) = _
    rw [derRing_of_mem (ev1 Γ) ψ f, kap_inr]
    rfl
  constructor
  · intro hw e v h1 h2
    obtain ⟨ψ, hψ, v', h1', h2', h3'⟩ := hkey e
    rw [huniq e v v' h1 h1' h2 h2', hval ψ v' h3', ← hw, hψ]
  · intro H
    obtain ⟨w₀, hw₀⟩ := hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent f)
    have hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w - w₀) e) = 0 := by
      intro e
      obtain ⟨ψ, hψ, v', h1', h2', h3'⟩ := hkey e
      have a1 := H e v' h1' h2'
      rw [hval ψ v' h3', ← hw₀, hψ] at a1
      have a2 := TrivSqZeroExt.inr_injective a1
      rw [LinearMap.sub_apply, map_sub, a2, sub_self]
    obtain ⟨u', hu'⟩ := dual_eq_smul N (w - w₀) hd
    have : θ (w - w₀) = 0 := (hker _).2 ⟨u', hu'⟩
    rw [map_sub, sub_eq_zero] at this
    rw [this, hw₀]

end PositivityTheory.HtPt.Ge.TwDer

namespace PositivityTheory.HtPt.Ge.TwDer
open GlobalTheory.CompanionTheory PositivityTheory.HtPt.Ge.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

section Der
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} (N : ℕ) (i : Γ.G.left ⟶ G.left)
  {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L)

abbrev Q (R : Type) [CommRing R] (N : ℕ) : Type := R ⧸ Ideal.span {(N : R)}

def IsTanPt (e : L) (v : Spec (CommRingCat.of (DualNumber (Q R N))) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
    v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left

def Der (f : T → R) (w : Module.Dual R L) : Prop :=
  ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))

theorem valAt_add' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a b : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a + b) = valAt y ⊤ le_top a + valAt y ⊤ le_top b := by
  simp [valAt]

theorem valAt_mul' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a b : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a * b) = valAt y ⊤ le_top a * valAt y ⊤ le_top b := by
  simp [valAt]

def cst (r : R) : Γ(Γ.G.left, ⊤) :=
  Γ.G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

theorem valAt_cst {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (φ : R →+* B)
    (h : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom φ)) (r : R) : valAt y ⊤ le_top (cst Γ r) = φ r :=
  ValEmb.valAt_pull Γ.G.hom y φ h r

theorem hasValues_cst (r : R) : Γ.HasValues (cst Γ r) (fun _ => r) := fun t =>
  valAt_cst Γ (Γ.pt t).left (algebraMap R (FractionRing R)) (Over.w (Γ.pt t)) r

theorem der_const (r : R) (h : ∀ e : L, ∃ v, IsTanPt Γ N i M e v) : Der Γ N i M (fun _ => r) 0 := by
  refine ⟨cst Γ r, hasValues_cst Γ r, fun e => ?_⟩
  obtain ⟨v, h1, h2⟩ := h e
  refine ⟨v, h1, h2, ?_⟩
  rw [valAt_cst Γ v _ h1]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {Γ N i M}

theorem der_add_mul (hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v')
    {f g : T → R} {w w' : Module.Dual R L} (hf : Der Γ N i M f w) (hg : Der Γ N i M g w') :
    Der Γ N i M (f + g) (w + w') ∧ Der Γ N i M (f * g) (f 1 • w' + g 1 • w) := by
  obtain ⟨s, hs, hv⟩ := hf
  obtain ⟨s', hs', hv'⟩ := hg
  constructor
  · refine ⟨s + s', fun t => ?_, fun e => ?_⟩
    · rw [valAt_add', hs t, hs' t]; simp
    · obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      refine ⟨v, a, b, ?_⟩
      rw [valAt_add', c, c']
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  · refine ⟨s * s', fun t => ?_, fun e => ?_⟩
    · rw [valAt_mul', hs t, hs' t]; simp
    · obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      refine ⟨v, a, b, ?_⟩
      rw [valAt_mul', c, c']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp [TrivSqZeroExt.snd_mul, mul_comm, add_comm]

theorem der_unique [Finite T] [Module.Projective R L]
    (hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v')
    {f : T → R} {w w' : Module.Dual R L} (hf : Der Γ N i M f w) :
    Der Γ N i M f w' ↔ ∃ u : Module.Dual R L, w' = w + N • u := by
  obtain ⟨s, hs, hv⟩ := hf
  constructor
  · rintro ⟨s', hs', hv'⟩
    have hss : s' = s := by
      refine sub_eq_zero.mp (GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) ?_)
      intro t h
      rw [ValEmb.valAt_sub]
      exact sub_eq_zero.mpr ((hs' t).trans (hs t).symm)
    subst hss
    have hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w' - w) e) = 0 := by
      intro e
      obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      have h3 := c'.symm.trans c
      have h4 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) =
          Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) := by
        simpa using congrArg TrivSqZeroExt.snd h3
      rw [LinearMap.sub_apply, map_sub, h4, sub_self]
    obtain ⟨u, hu'⟩ := dual_eq_smul N (w' - w) hd
    exact ⟨u, by rw [← hu']; abel⟩
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [c]
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w + N • u) e) =
        Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) := by
      refine Ideal.Quotient.eq.mpr ?_
      rw [Ideal.mem_span_singleton]
      exact ⟨u e, by simp⟩
    rw [h0]

end Der

end PositivityTheory.HtPt.Ge.TwDer

namespace PositivityTheory.HtPt.Ge.TwDer
open GlobalTheory.CompanionTheory PositivityTheory.HtPt.Ge.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem der_all {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (ht : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L]
    [Module.Projective R L] (M : LieModel G x L) {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (U : Γ.G.left.Opens) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)] :
    (∀ f ∈ Γ.btOrder ⊤, ∃ w, Der Γ N i M f w) ∧
    (∀ f w w', Der Γ N i M f w → (Der Γ N i M f w' ↔ ∃ u : Module.Dual R L, w' = w + N • u)) ∧
    (∀ w, ∃ f ∈ Γ.btOrder ⊤, Der Γ N i M f w) ∧
    (∀ f g w w', Der Γ N i M f w → Der Γ N i M g w' →
      Der Γ N i M (f + g) (w + w') ∧ Der Γ N i M (f * g) (f 1 • w' + g 1 • w)) ∧
    (∀ r : R, Der Γ N i M (fun _ => r) 0) ∧
    ∀ f : augIdeal (Γ.btOrder ⊤), Der Γ N i M f.1.1 0 → (f : Γ.btOrder ⊤) ∈ augIdeal (Γ.btOrder ⊤) ^ 2 := by
  have hex : ∀ e : L, ∃ v, IsTanPt Γ N i M e v := fun e =>
    (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v' := fun e _ _ h h' =>
    (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique h h'
  obtain ⟨θ, hsurj, -, hpin⟩ := omega_open Γ ht M hj U hU
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have hpinD : ∀ (g : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent g → Der Γ N i M g.1.1 w := by
    intro g w h
    obtain ⟨s, hs⟩ := hsec g.1
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, a, b⟩ := hex e
    refine ⟨v, a, b, ?_⟩
    have h0 : (g.1.1 : T → R) 1 = 0 := g.2
    rw [(hpin g w s hs).1 h e v a b, h0]
    simp
  refine ⟨fun f hf => ?_, fun f w w' h => der_unique hu h, fun w => ?_, fun f g w w' h h' => der_add_mul hu h h',
    fun r => der_const Γ N i M r hex, fun f h => ?_⟩
  · let a : Γ.btOrder ⊤ := ⟨f, hf⟩
    let g : augIdeal (Γ.btOrder ⊤) := ⟨a - algebraMap R _ (f 1), by
      rw [OrderApi.mem_augIdeal]
      simp [a]⟩
    obtain ⟨w, hw⟩ := hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent g)
    have h1 := (der_add_mul hu (hpinD g w hw) (der_const Γ N i M (f 1) hex)).1
    refine ⟨w + 0, ?_⟩
    convert h1 using 1
    ext t
    simp [g, a]
  · obtain ⟨g, hg⟩ := Ideal.toCotangent_surjective _ (θ w)
    exact ⟨g.1.1, g.1.2, hpinD g w hg.symm⟩
  · obtain ⟨s, hs, hv⟩ := h
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    have h1 := (hpin f 0 s hs).2 (fun e v a b => by
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp)
    rw [map_zero] at h1
    exact (Ideal.toCotangent_eq_zero _ _).1 h1.symm

theorem finite_levGrp' {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (pow_pos hp.pos n).ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

theorem valuationRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [IsDomain O]
    [Algebra O C] (hv : v.Integers O) : ValuationRing O := by
  haveI : PreValuationRing O := by
    refine ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_of_le h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_of_le h
      exact ⟨c, Or.inl hc.symm⟩
  exact {}

theorem der_main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ), (∀ f ∈ (X.Γ n).btOrder ⊤, ∃ w, X.IsDer M n f w) ∧ (∀ f w w', X.IsDer M n f w → (X.IsDer M n f w' ↔ ∃ u : Module.Dual O L, w' = w + (p ^ n) • u)) ∧ (∀ w, ∃ f ∈ (X.Γ n).btOrder ⊤, X.IsDer M n f w) ∧ (∀ f g w w', X.IsDer M n f w → X.IsDer M n g w' → X.IsDer M n (f + g) (w + w') ∧ X.IsDer M n (f * g) (f 1 • w' + g 1 • w)) ∧ (∀ r : O, X.IsDer M n (fun _ => r) 0) ∧ ∀ f : augIdeal ((X.Γ n).btOrder ⊤), X.IsDer M n f.1.1 0 → (f : (X.Γ n).btOrder ⊤) ∈ augIdeal ((X.Γ n).btOrder ⊤) ^ 2 := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO S _ G _ _ hG y La _ _ _ X L _ _ M n
  haveI : ValuationRing O := valuationRing_of_integers v hv
  haveI : IsLocalRing O := inferInstance
  haveI : IsIntegrallyClosed O := inferInstance
  haveI : Smooth G.hom := hG.smooth
  haveI : Finite (LevGrp La p n) := finite_levGrp' (Fact.out) n
  haveI : Module.Projective O L := (GlobalTheory.T.lie_model_finite_base_change S G O y L M).2.1
  obtain ⟨U, H, hfin, -⟩ := GlobalTheory.T.semiabelian_adic_torsion_one p C v O hv hp hO S G hG y La X
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.existsUnique_btOrder_embedding O _ (X.Γ n)
  haveI := (EmbSub.openImmersion_translatesCover O _ (X.Γ n) (U n) (hfin n) j hj).1
  exact der_all (X.Γ n) (X.tors n) M hj (U n) (hfin n).one

end PositivityTheory.HtPt.Ge.TwDer
end
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Ge.Fargues
open GlobalTheory.CompanionTheory

theorem lie_free_finite (S : Scheme.{0}) (G : Over S) [GrpObj G] (hG : Smooth G.hom) (R : Type) [CommRing R]
    [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : Module.Free R E ∧ Module.Finite R E := by
  obtain ⟨n, ⟨b⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring S G hG R x E M
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

def ordTower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1)
    (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L]
    (M : LieModel G y L) : OrdTower p O La L :=
  haveI : IsLocalRing O := (GlobalTheory.T.complete_integers_properties p C v O hv hp hO).2.1.toIsLocalRing
  have h3 := GlobalTheory.T.semiabelian_adic_torsion_one p C v O hv hp hO S G hG y La X
  have h4 := GlobalTheory.T.semiabelian_adic_torsion_two p C v O hv hp hO S G hG y La X
  have h5 := TwDer.der_main p C v O hv hp hO S G hG y La X L M
  have h6 := (GlobalTheory.T.semiabelian_adic_torsion_four p C v O hv hp hO S G hG y La X L M).1
  { A := fun n => (X.Γ n).btOrder ⊤
    hopf := by
      obtain ⟨U, H, -, -, -, h, -⟩ := h3
      exact h
    res_iff := fun n => (h4 n).1
    ker_res := fun n => (h4 n).2
    der := X.IsDer M
    der_ex := fun n => (h5 n).1
    der_unique := fun n => (h5 n).2.1
    der_onto := fun n => (h5 n).2.2.1
    der_add := fun n f g w w' hf hg => ((h5 n).2.2.2.1 f g w w' hf hg).1
    der_mul := fun n f g w w' hf hg => ((h5 n).2.2.2.1 f g w w' hf hg).2
    der_const := fun n => (h5 n).2.2.2.2.1
    der_zero := fun n => (h5 n).2.2.2.2.2
    der_res := h6 }

theorem pointHT (hF : FarguesHodgeTate) : PointHT := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c hc S _ G _ _ hG y La _ _ EF N u hu X L _ _ M act ρL hmon hact hind
    hrank ζ hζ hζp hpair κ hκ
  haveI : Module.Free ℤ La := hu.free
  haveI : Module.Finite ℤ La := hu.finite
  haveI : IsLocalRing O := (GlobalTheory.T.complete_integers_properties p C v O hv hp hO).2.1.toIsLocalRing
  obtain ⟨hLf, hLfin⟩ := lie_free_finite S G hG.smooth O y L M
  let T := ordTower p C v O hv hp hO S G hG y La X L M
  have hacts : ∀ a : 𝓞 E, T.Acts (DistribMulAction.toAddMonoidHom La a) (ρL a) := by
    intro a n f g hfg
    haveI := hmon a
    exact (GlobalTheory.T.semiabelian_adic_torsion_four p C v O hv hp hO S G hG y La X L M).2 (act a) _ (ρL a) (hind a) (hact a) n f g hfg
  have hpe : T.PairingExtends EF ζ := fun n =>
    GlobalTheory.T.exists_prodSpan_torsion_pairing_eq_zeta_pow p C v O hv hp hO S G hG y La X EF ζ (fun n => (hζ n).pow_eq_one) hpair n
  exact GlobalTheory.T.polarised_divisible_group_exists hF p C v O hv hp hO E c hc La EF N u hu L T ρL ζ κ hacts hrank hζ hζp hpe hκ

end PositivityTheory.HtPt.Ge.Fargues

theorem PositivityTheory.HtPt.Ge.pointHT_of_fargues : FarguesHodgeTate → PointHT := PositivityTheory.HtPt.Ge.Fargues.pointHT
end
end
