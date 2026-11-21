import Development.EtaleCohomology.EtaleSheaves.LeafExcRingPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
namespace LateralTheory.E.LeafExcRingPf2
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

theorem schPb {X Y : Scheme.{0}} (g : Y ⟶ X) (U : X.Opens) :
    IsPullback (sch.map (g ∣_ U)) (sch.map (g ⁻¹ᵁ U).ι) (sch.map U.ι) (sch.map g) := by
  haveI : PreservesLimit (cospan U.ι g) (yoneda ⋙ SimplicialObject.const PSh) := inferInstance
  exact (isPullback_morphismRestrict g U).map (yoneda ⋙ SimplicialObject.const PSh)

theorem conn_iso (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {P Q E : Spc} (e : P ≅ Q) (p : P ⟶ E) (q : Q ⟶ E)
    (h : e.hom ≫ q = p) : Conn R F c p ↔ Conn R F c q := by
  have hb : ∀ n, Function.Bijective (pull R e.hom F n) := fun n => by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hp : ∀ n x, pull R p F n x = pull R e.hom F n (pull R q F n x) := fun n x => by rw [← h, pull_comp]
  unfold Conn ConnK
  refine forall_congr' fun n => and_congr (imp_congr_right fun _ => ?_) (imp_congr_right fun _ => ?_)
  · change Function.Bijective (pull R p F n) ↔ Function.Bijective (pull R q F n)
    rw [show (pull R p F n : _ → _) = pull R e.hom F n ∘ pull R q F n from funext (hp n)]
    exact ⟨fun hh => (Function.Bijective.of_comp_iff' (hb n) _).1 hh, fun hh => (hb n).comp hh⟩
  · change Function.Injective (pull R p F n) ↔ Function.Injective (pull R q F n)
    rw [show (pull R p F n : _ → _) = pull R e.hom F n ∘ pull R q F n from funext (hp n)]
    exact ⟨fun hh => (Function.Injective.of_comp_iff (hb n).1 _).1 hh, fun hh => (hb n).1.comp hh⟩

theorem leafPb : LeafPb := by
  intro R _ F c X Y g U
  exact (conn_iso R F c (schPb g U).isoPullback _ _ (schPb g U).isoPullback_hom_snd).symm

theorem LeafExcRing_of' (hE : LeafExc) (hC1 : LeafCov1) (hC2 : LeafCov2) : LeafExcRing :=
  LeafExcRing_of hE hC1 hC2 leafPb
end LateralTheory.E.LeafExcRingPf2
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafCov1Pf
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

theorem exists_lift {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B)
    (hQ : QIso α I) (p : Ideal B) [hp : p.IsPrime] (hI : I ≤ p) :
    ∃ q : Ideal W, q.IsPrime ∧ q.comap α = p := by
  let e := RingEquiv.ofBijective _ hQ
  let f : W →+* B ⧸ I := (e.symm : W ⧸ I.map α →+* B ⧸ I).comp (Ideal.Quotient.mk (I.map α))
  have hf : f.comp α = Ideal.Quotient.mk I := by
    ext b
    simp only [f, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingEquiv.symm_apply_eq]
    rfl
  have hpb : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)
  refine ⟨(p.map (Ideal.Quotient.mk I)).comap f, Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.comap_comap, hf, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.2 hI

theorem LeafCov1_of (_hE : LeafExc) : LeafCov1 := by
  intro B W _ _ α I hα hQ U hU T y
  have : Etale (Spec.map (CommRingCat.ofHom α)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 hα
  let A : Bool → Scheme.{0} := fun b => Bool.rec (pullback y (Spec.map (CommRingCat.ofHom α)))
    ((y ⁻¹ᵁ U : T.Opens) : Scheme.{0}) b
  let m : (b : Bool) → A b ⟶ T := fun b => Bool.rec (motive := fun b => A b ⟶ T)
    (pullback.fst y (Spec.map (CommRingCat.ofHom α))) (y ⁻¹ᵁ U).ι b
  have hcov : ∀ t, ∃ (b : Bool) (z : A b), (m b).base z = t := by
    intro t
    by_cases ht : y t ∈ U
    · exact ⟨true, ⟨t, ht⟩, rfl⟩
    · rw [hU] at ht
      push Not at ht
      obtain ⟨q, hq, hqp⟩ := exists_lift α I hQ _ ht
      let w : Spec (CommRingCat.of W) := (⟨q, hq⟩ : PrimeSpectrum W)
      have hw : Spec.map (CommRingCat.ofHom α) w = y t := PrimeSpectrum.ext hqp
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback t w hw.symm
      exact ⟨false, z, hz⟩
  have hprop : ∀ b, Etale (m b) := by
    intro b; cases b <;> dsimp [m] <;> infer_instance
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Bool A m hcov hprop
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V k hk
  obtain ⟨b, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  change Bool at b
  cases b
  · right
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    show (h ≫ pullback.snd y _) ≫ _ = h ≫ pullback.fst y (Spec.map (CommRingCat.ofHom α)) ≫ y
    exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) pullback.condition).symm
  · left
    refine ⟨h ≫ (y ∣_ U), ?_⟩
    show (h ≫ (y ∣_ U)) ≫ U.ι = h ≫ (y ⁻¹ᵁ U).ι ≫ y
    exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) (morphismRestrict_ι y U))

end LateralTheory.E.LeafCov1Pf
end
end
