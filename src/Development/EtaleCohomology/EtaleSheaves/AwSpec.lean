import Development.EtaleCohomology.EtaleSheaves.TwPairExists
import Development.EtaleCohomology.EtaleSheaves.EtaleFirstChernClassRepresentedByChernCocycle
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
import Development.EtaleCohomology.EtaleSheaves.LeafSupport
import Development.EtaleCohomology.EtaleSheaves.LeafActSheafPf
import Development.EtaleCohomology.EtaleSheaves.LeafChernPf
import Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
import Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
import Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf
import Development.EtaleCohomology.EtaleSheaves.LeafGeomPfLoc
import Development.EtaleCohomology.EtaleSheaves.WeightBoundsExistence
import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono
import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
import Development.EtaleCohomology.EtaleSheaves.LeafLinePf
import Development.EtaleCohomology.EtaleSheaves.LeafMapWPf
import Development.EtaleCohomology.EtaleSheaves.LeafNatPf
import Development.EtaleCohomology.EtaleSheaves.LeafNewtonPf
import Development.EtaleCohomology.EtaleSheaves.LeafOneLocPf
import Development.EtaleCohomology.EtaleSheaves.LeafPreTensLocInjPf
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
import Development.EtaleCohomology.EtaleSheaves.LeafTensFactorPf
import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
import Development.EtaleCohomology.EtaleSheaves.PairExtensionOfTensorUniversal
import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocGenOf
import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocSplitOf
import Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExistsPf
import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf
import Development.EtaleCohomology.EtaleSheaves.LeafWhitneyPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat

section
namespace LateralTheory.E.LeafA6ringCut

theorem goal_of (h5 : LateralTheory.E.CupProductRingLaws.LeafRingUnit) (h6 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc)
    (h7 : LateralTheory.E.CupProductRingLaws.LeafRingComm) : LateralTheory.E.D2.LeafA6ring :=
  fun q _ E => ⟨h5 q E, h6 q E, h7 q E⟩

end LateralTheory.E.LeafA6ringCut
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCochainVanishPf

variable {R : Type} [CommRing R]

theorem free_ext_zero (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.hom.app (op U)).hom (freeGen R P U x) = 0) : φ = 0 := by
  have h0 : (0 : (free R).obj P ⟶ G).hom = 0 := rfl
  refine Sheaf.hom_ext ?_
  rw [h0]
  refine sheafify_hom_ext _ _ _ G.property ?_
  ext U : 2
  refine ModuleCat.free_hom_ext (fun x => ?_)
  exact (h U.unop x.down).trans (by erw [Limits.comp_zero]; rfl)

theorem chains_isZero (E : Spc) (p : ℤ) (hp : 0 < p) : Limits.IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => ?_)
  have : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  omega

theorem cochain_zero_of (E : Spc) {U V : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (K : Cx R) (k : ℤ)
    (γ : Cochain ((chains R).obj E) K k)
    (hU : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0)
    (hV : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) :
    γ = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : 0 < p
  · exact (chains_isZero (R := R) E p hp).eq_of_src _ _
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
  have hφ : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q hpq = 0 := by
    have := hc.2.2 (op (SimplexCategory.mk N))
    rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
      ((free R).map (g.app (op (SimplexCategory.mk N))))), Limits.comp_zero]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hU N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
    · rw [biprod.inr_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hV N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
  rw [← Iso.hom_inv_id_assoc (chainsXIso R E N) (γ.v _ _ hpq), hφ, Limits.comp_zero]

end LateralTheory.E.LeafCochainVanishPf

theorem LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := by
  intro R _ U V E f g hc K k γ hU hV
  exact LateralTheory.E.LeafCochainVanishPf.cochain_zero_of E f g hc K k γ hU hV
end
end

section
noncomputable section

namespace LateralTheory.E.BaerFlatZModCriterion

open TensorProduct

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_eq_smul_of_baer (hB : Module.Baer R M) {a b : R}
    (hab : ∀ r, b * r = 0 → ∃ s, r = a * s) {m : M} (hm : a • m = 0) : ∃ m' : M, m = b • m' := by
  let f : R →ₗ[R] R := LinearMap.toSpanSingleton R R b
  have hker : LinearMap.ker f ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    intro x hx
    simp only [LinearMap.mem_ker, f, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx ⊢
    obtain ⟨s, rfl⟩ := hab x (by rw [mul_comm]; exact hx)
    rw [mul_comm, mul_smul, hm, smul_zero]
  let g : LinearMap.range f →ₗ[R] M :=
    (LinearMap.ker f).liftQ (LinearMap.toSpanSingleton R M m) hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g', hg'⟩ := hB (LinearMap.range f) g
  refine ⟨g' 1, ?_⟩
  have h1 : f 1 = b := by simp [f]
  have hmem : b ∈ LinearMap.range f := ⟨1, h1⟩
  have := hg' b hmem
  have hg : g ⟨b, hmem⟩ = m := by
    have e : (⟨b, hmem⟩ : LinearMap.range f) = ⟨f 1, LinearMap.mem_range_self f 1⟩ := Subtype.ext h1.symm
    rw [e]
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hg, ← this, ← map_smul, smul_eq_mul, mul_one]

theorem flat_of_baer [IsPrincipalIdealRing R]
    (hA : ∀ a : R, ∃ b, a * b = 0 ∧ ∀ r, b * r = 0 → ∃ s, r = a * s) (hB : Module.Baer R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have pure : ∀ x : I ⊗[R] M, ∃ m : M, x = (⟨a, haI⟩ : I) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul y n =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by rw [← ha]; exact y.2)
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      exact Subtype.ext hc.symm
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, by rw [tmul_add]⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := pure x
  simp only [lift.tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.lsmul_apply] at hx
  obtain ⟨b, hab, hb⟩ := hA a
  obtain ⟨m', rfl⟩ := exists_eq_smul_of_baer hB hb hx
  rw [← smul_tmul]
  have : b • (⟨a, haI⟩ : I) = 0 := Subtype.ext (by simp [smul_eq_mul, mul_comm, hab])
  rw [this, zero_tmul]

end General

section ZModPart

theorem zmod_ann (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, a * b = 0 ∧ ∀ r : ZMod q, b * r = 0 → ∃ s, r = a * s := by
  obtain ⟨n, hn⟩ : ∃ n, n = a.val := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd n q := ⟨_, rfl⟩
  have hq : 0 < q := NeZero.pos q
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_right _ hq
  have hgq : g ∣ q := hg ▸ Nat.gcd_dvd_right n q
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_left n q
  have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hg0
  have ha : a = (n : ZMod q) := by rw [hn, ZMod.natCast_zmod_val]
  refine ⟨((q / g : ℕ) : ZMod q), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hgn
    rw [ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [hk, mul_comm g k, mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
  · intro r hr
    have hr' : q ∣ (q / g) * r.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hr
    have hdiv : g ∣ r.val := by
      have h2 : (q / g) * g ∣ (q / g) * r.val := by rw [Nat.div_mul_cancel hgq]; exact hr'
      exact Nat.dvd_of_mul_dvd_mul_left hqg h2
    obtain ⟨t, ht⟩ := hdiv
    have hz := Nat.gcd_eq_gcd_ab n q
    have hgz : (g : ZMod q) = a * (Nat.gcdA n q : ZMod q) := by
      have := congrArg (Int.cast : ℤ → ZMod q) hz
      push_cast at this
      rw [ZMod.natCast_self, zero_mul, add_zero, ← hg] at this
      rw [this, ha]
    refine ⟨(Nat.gcdA n q : ZMod q) * (t : ZMod q), ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hgz, mul_assoc]

end ZModPart

end LateralTheory.E.BaerFlatZModCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion LateralTheory.E.BaerFlatZModCriterion in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of : LeafInjFlatZMod := by
  intro q _ M _ _ hinj
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  refine flat_of_baer (fun a => ?_) (Module.Baer.of_injective hinj)
  obtain ⟨b, hab, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext _ _ hab, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext _ _ hs⟩
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.InjectiveSections

abbrev MC (q : ℕ) := ModuleCat.{1} (ULift.{1} (ZMod q))

theorem sigma_const_mono (q : ℕ) {α : Type} {d d' : MC q} (f : d ⟶ d') [Mono f] :
    Mono (Limits.Sigma.map (fun _ : α => f)) := by
  have : Mono (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) :=
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun _ => inferInstanceAs (Mono f))
  have : AB4OfSize.{0} (MC q) := AB4OfSize_shrink.{0, 1} (MC q)
  have : HasExactColimitsOfShape (Discrete α) (MC q) := AB4OfSize.ofShape α
  have : PreservesFiniteLimits (colim : (Discrete α ⥤ MC q) ⥤ MC q) := inferInstance
  exact (Functor.map_mono colim (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) : _)

instance evalLA_mono (q : ℕ) (U : Scheme.{0}) :
    (evaluationLeftAdjoint (MC q) (op U)).PreservesMonomorphisms where
  preserves {d d'} f _ := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun t => ?_)
    change Mono (Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h))
    have h : Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h) = Limits.Sigma.map (fun _ => f) := by
      apply Limits.Sigma.hom_ext; intro j; rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_map]
    rw [h]
    exact sigma_const_mono q f

theorem eval_injective (q : ℕ) (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}) :
    Injective (M.obj.obj (op U)) := by
  have h1 : Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (MC q)).obj M) :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology.{0} (MC q)) M
  have h2 : Injective M.obj := h1
  exact Injective.injective_of_adjoint (evaluationAdjunctionRight (MC q) (op U)) M.obj

end LateralTheory.E.InjectiveSections

open LateralTheory.E.InjectiveSections in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := by
  intro q _ M _ U
  have h := eval_injective q M U
  exact Module.injective_module_of_injective_object (ULift.{1} (ZMod q)) (Sec M U)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.PrimitiveRootLocalization

theorem cyc_cond {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ (p₁ p₂ : A[X]) (n : ℕ), derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = (1 : A[X]) ^ n := by
  obtain ⟨h, e1⟩ := cyclotomic.dvd_X_pow_sub_one q A
  obtain ⟨v, hv⟩ := hq.exists_left_inv
  have e2 := congrArg derivative e1
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at e2
  have e3 : C v * C (q : A) = 1 := by rw [← C_mul, hv, C_1]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have e4 : X * X ^ (q - 1) = (X : A[X]) ^ q := by rw [← pow_succ']; congr 1; omega
  refine ⟨C v * X * h, C v * X * derivative h - h, 0, ?_⟩
  linear_combination (-(C v * X)) * e2 + (C v * C (q : A)) * e4 + X ^ q * e3 + e1

def cycPair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := cyc_cond q hq

section
variable {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A))

theorem cycPair_hasMap_root : (cycPair q hq).HasMap (AdjoinRoot.root (cyclotomic q A)) := by
  refine ⟨?_, ?_⟩
  · simp [cycPair]
  · simp [cycPair]

theorem adjoinRoot_nontrivial [Nontrivial A] : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h1 := (cyclotomic.monic q A).isUnit_iff.mp hu
  have h2 := natDegree_cyclotomic q A
  rw [h1, natDegree_one] at h2
  exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne' h2.symm

theorem comap_surj : Function.Surjective (PrimeSpectrum.comap (algebraMap A (cycPair q hq).Ring)) := by
  by_cases hA : Nontrivial A
  · let ψ : (cycPair q hq).Ring →ₐ[A] AdjoinRoot (cyclotomic q A) := (cycPair q hq).lift _ (cycPair_hasMap_root q hq)
    have := (cyclotomic.monic q A).free_adjoinRoot
    have := adjoinRoot_nontrivial (A := A) q
    have hs := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := AdjoinRoot (cyclotomic q A))
    have e : algebraMap A (AdjoinRoot (cyclotomic q A)) = (ψ : (cycPair q hq).Ring →+* _).comp (algebraMap A (cycPair q hq).Ring) := by
      ext a; simp
    intro x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨PrimeSpectrum.comap (ψ : (cycPair q hq).Ring →+* _) y, ?_⟩
    rw [← hy, e]
    rfl
  · intro x
    rw [not_nontrivial_iff_subsingleton] at hA
    exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

def primRing : Prim q (cycPair q hq).Ring :=
  ⟨(cycPair q hq).X, by simpa using hq.map (algebraMap A (cycPair q hq).Ring), by
    have h := (cycPair q hq).hasMap_X.1
    change aeval (cycPair q hq).X (cyclotomic q A) = 0 at h
    rw [← map_cyclotomic q (algebraMap ℤ A), aeval_map_algebraMap] at h
    exact h⟩

end

theorem LeafPrimLoc_of : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := by
  intro q _ U hq
  let P := cycPair (A := Γ(U, ⊤)) q hq
  let f : Spec (CommRingCat.of P.Ring) ⟶ Spec Γ(U, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) P.Ring))
  have hfe : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hfs : Surjective f := ⟨comap_surj q hq⟩
  have hge : Etale (pullback.fst U.toSpecΓ f) := inferInstance
  have hgs : Surjective (pullback.fst U.toSpecΓ f) := inferInstance
  let S : Sieve U :=
    { arrows := fun V _ => Nonempty (Prim q Γ(V, ⊤))
      downward_closed := fun {V W} g hg h => hg.elim fun ζ => ⟨Prim.map h.appTop.hom ζ⟩ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨hgs.surj, hge⟩))
  rintro V _ ⟨W, h, k, ⟨⟩, rfl⟩
  exact ⟨Prim.map ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv ≫ (h ≫ pullback.snd _ _).appTop).hom (primRing q hq)⟩

end LateralTheory.E.PrimitiveRootLocalization
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRepVanishPf

variable (R : Type) [CommRing R]

theorem free_mono {P Q : PSh} (φ : P ⟶ Q) [Mono φ] : Mono ((free R).map φ) := by
  have : Mono ((freeP R).map φ) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [ModuleCat.mono_iff_injective]
    have hi : Function.Injective (φ.app Y) := (mono_iff_injective _).1 inferInstance
    have hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y)) := by
      intro a b h; exact ULift.ext _ _ (hi (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  unfold free
  simp only [Functor.comp_map]
  infer_instance

theorem chains_f (E E' : Spc) (f : E ⟶ E') (N : ℕ) :
    ((chains R).map f).f (-(N : ℤ)) = (chainsXIso R E N).hom ≫ (free R).map (f.app (op (SimplexCategory.mk N))) ≫ (chainsXIso R E' N).inv := by
  exact (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl

theorem freeGen_nat {P Q : PSh} (φ : P ⟶ Q) (Y : Scheme.{0}) (x : P.obj (op Y)) :
    (((free R).map φ).hom.app (op Y)).hom (freeGen R P Y x) = freeGen R Q Y (φ.app _ x) := by
  have e := congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))
  have e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) =
      ModuleCat.freeMk (ULift.up.{1} (φ.app _ x)) := ModuleCat.free_map_apply _ _
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  refine e.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2

theorem ev_pull {U E : Spc} (f : U ⟶ E) {K : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) K n) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y) :
    ev ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add n)) N w h Y y = ev γ N w h Y ((f.app _).app _ y) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← freeGen_nat]
  rfl

theorem chains_mono {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) : Mono (((chains R).map f).f p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    rw [chains_f]
    have := free_mono R (f.app (op (SimplexCategory.mk N)))
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change -(i : ℤ) = p at hi; omega)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩

theorem LeafRepVanish_of : LateralTheory.E.LeafA6suppPf.LeafRepVanish := by
  intro R _ U E f hf F n a ha
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  have hg := chains_mono R f
  have hinj : ∀ q, Injective ((res R F).X q) := fun q =>
    (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))
  have h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 := ha
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨β', hβ'⟩ := h1
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)
  have hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β' := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [β, Cochain.mk_v]
    exact Injective.comp_factorThru _ _
  let b : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - b, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2
      ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]
  · intro N w h Y y
    rw [← ev_pull]
    have e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0 := by
      rw [Cocycle.coe_sub, Cochain.comp_sub]
      have : (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β' := by
        rw [← hβ]; simp [b]
      rw [this, hβ']
      simp [zcomp]
    rw [e]
    simp [ev]

end LateralTheory.E.LeafRepVanishPf
end
end

section
namespace LateralTheory.E.RingCommutativity

theorem goal_of : LateralTheory.E.CupProductRingLaws.LeafRingComm := LateralTheory.Fix.CupProductTensor.ringComm'

end LateralTheory.E.RingCommutativity
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafSecInjPf

universe u v w

instance evaluationLeftAdjoint_preservesMono {C : Type u} [Category.{0} C] (R' : Type 1) [Ring R'] (c : C) :
    (evaluationLeftAdjoint (ModuleCat.{1} R') c).PreservesMonomorphisms where
  preserves {d₁ d₂} f _ := by
    rw [NatTrans.mono_iff_mono_app']
    intro t
    have e : ((evaluationLeftAdjoint (ModuleCat.{1} R') c).map f).app t =
        Limits.Sigma.map (fun _ : c ⟶ t => f) := by
      apply Limits.Sigma.hom_ext; intro h
      erw [Limits.Sigma.ι_desc]
    rw [e]
    have : HasCoproducts.{0} (ModuleCat.{1} R') := hasCoproducts_shrink.{0, 1}
    have : AB4OfSize.{0} (ModuleCat.{1} R') := AB4OfSize_shrink.{0, 1} _
    have : HasExactColimitsOfShape (Discrete (c ⟶ t)) (ModuleCat.{1} R') := AB4OfSize.ofShape _
    have : (MorphismProperty.monomorphisms (ModuleCat.{1} R')).IsStableUnderCoproductsOfShape (c ⟶ t) :=
      MorphismProperty.isStableUnderColimitsOfShape_monomorphisms _ _
    exact MorphismProperty.colimMap (W := MorphismProperty.monomorphisms (ModuleCat.{1} R'))
      (J := Discrete (c ⟶ t)) _ (fun _ => (inferInstance : Mono f))

theorem secInj (R : Type) [CommRing R] (F : Shv R) (hF : Injective F) (U : Scheme.{0}) :
    Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
      (evaluation _ _).obj (op U)).obj F) :=
  ((evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))).map_injective _ hF

theorem LeafSecInj_of : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := by
  intro R _ F hF U
  have h := secInj R F hF U
  exact (Module.injective_iff_injective_object (ULift.{1} R) (Sec F U)).mpr h

end LateralTheory.E.LeafSecInjPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoGenPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩
  · intro U y
    exact loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)
  · intro U x hx
    have hx0 : x = 0 := hx
    subst hx0
    exact loc_top U _ (fun V g => map_zero _)
  · intro U _
    exact h U

theorem LeafTensQIsoGen_of : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := by
  intro R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι
  exact LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι
    (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)

end LateralTheory.E.LeafTensQIsoGenPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTensUPPf
open LateralTheory.E.LeafTwTensExPf
open Classical

variable {R : Type} [CommRing R] {I J K : Cx R}

theorem lift_lo (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  simp [Pair.lift, lo]

theorem lift_nat (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    ((K.X w).obj.map g.op).hom ∘ₗ μ.lift U w = μ.lift V w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  have e := tres_tmul I J g w ⟨(s, t), h⟩ a b
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (Tens.res g w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [e]
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (lo I J ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
  rw [lift_lo, lift_lo, μ.nat]

theorem lift_d (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    ((K.d w (w + 1)).hom.app (op U)).hom ∘ₗ μ.lift U w = μ.lift U (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  change Sec.map (K.d w (w + 1)) (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) =
    μ.lift U (w + 1) (dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [dT_tmul, map_add, map_zsmul, lift_lo, lift_lo, lift_lo, μ.leibniz, Units.smul_def]

def liftP (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (lift_nat μ g.unop w).symm

theorem tensorPresheafLift_comm (μ : Pair I J K) (w : ℤ) :
    liftP μ w ≫ (K.d w (w + 1)).hom = dTP I J w ≫ liftP μ (w + 1) := by
  ext U : 2
  exact ModuleCat.hom_ext (lift_d μ U.unop w)

theorem etale_tensor_presheaf_lift_is_local_iso {T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (liftP τ w) := by
  have : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {U} y => by
    obtain ⟨S, hS, hP⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨x, hx⟩⟩
  have : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {X} x y hxy => by
    let x' : Tens I J X.unop w := x
    let y' : Tens I J X.unop w := y
    have hxy' : τ.lift X.unop w x' = τ.lift X.unop w y' := hxy
    have h0 : τ.lift X.unop w (x' - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy'
    obtain ⟨S, hS, hP⟩ := hτ.2 X.unop w (x' - y') h0
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    have h1 : Tens.res g w (x' - y') = 0 := hP V g hg
    rw [map_sub, sub_eq_zero] at h1
    exact h1⟩
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

theorem etale_tensor_pairing_universal_property_holds : LateralTheory.E.LeafPairExtPf2.LeafTensUP := by
  intro R _ I J T K τ hτ μ
  have hb : ∀ w, Function.Bijective (fun g : (T.X w).obj ⟶ (K.X w).obj => liftP τ w ≫ g) :=
    fun w => etale_tensor_presheaf_lift_is_local_iso τ hτ w _ (K.X w).property
  choose u0 hu0' using fun w => (hb w).2 (liftP μ w)
  have hu0 : ∀ w, liftP τ w ≫ u0 w = liftP μ w := hu0'
  let u : T ⟶ K :=
    { f := fun w => ⟨u0 w⟩
      comm' := by
        rintro i j rfl
        apply Sheaf.hom_ext
        change u0 i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ u0 (i + 1)
        have key : liftP τ i ≫ (u0 i ≫ (K.d i (i + 1)).hom) = liftP τ i ≫ ((T.d i (i + 1)).hom ≫ u0 (i + 1)) := by
          rw [← Category.assoc, ← Category.assoc, hu0, tensorPresheafLift_comm, tensorPresheafLift_comm, Category.assoc, hu0]
        exact (etale_tensor_presheaf_lift_is_local_iso τ hτ i _ (K.X (i + 1)).property).1 key }
  refine ⟨u, fun U s t w h a b => ?_⟩
  have e := congrArg (fun f => (f.app (op U)).hom (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) (hu0 w)
  simp only at e
  rw [← lift_lo τ, ← lift_lo μ]
  exact e

end LateralTheory.E.LeafTensUPPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPfM

theorem iso_inv_mono' {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Mono e.inv := inferInstance

theorem resι_mono {R : Type} [CommRing R] (F : Shv R) : Mono (resι R F) := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))

theorem sec_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have h1 : Mono ((sheafToPresheaf _ _).map φ) := inferInstance
  have h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 h2

def LeafTw0TwFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • twGen 0 ζ = 0 → c = 0

theorem LeafTw0GenFree_of (h : LeafTw0TwFree) : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := by
  intro q _ V ζ
  rcases h q V ζ with h0 | h1
  · exact Or.inl h0
  · right
    intro c hc
    apply h1 c
    have : Mono (resι (ZMod q) (tw q 0)) := resι_mono _
    apply sec_inj (resι (ZMod q) (tw q 0)) V
    show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0
    rw [show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from
      map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]
    simp [Sec.map]

theorem LeafTw0LocSplit_of (h1 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen) (h2 : LeafTw0TwFree) :
    LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit :=
  LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of h1 (LeafTw0GenFree_of h2)

end LateralTheory.E.LeafTw0LocSplitPfM
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0TwFreePf

def aug (q : ℕ) (A : CommRingCat.{0}) : (twF q 0).obj A →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Submodule.liftQ (twRel q 0 A) (Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q)))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, _, rfl⟩
    simp [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single]
    exact sub_self (1 : ULift.{1} (ZMod q)))

theorem aug_mk (q : ℕ) (A : CommRingCat.{0}) (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  show Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q))) (Finsupp.single ζ 1) = 1
  rw [Finsupp.linearCombination_single, one_smul]

theorem aug_map (q : ℕ) (A B : CommRingCat.{0}) (g : A ⟶ B) (ζ : Prim q A) :
    aug q B (((twF q 0).map g).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))) = 1 := by
  show aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom) (Finsupp.single ζ 1))) = 1
  rw [Finsupp.mapDomain_single]
  exact aug_mk q B _

theorem LeafTw0TwFree_of : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := by
  intro q _ V ζ
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q 0
  let x : P.obj (op V) := (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 0).obj Γ(V, ⊤))
  let φ := ((toSheafify Scheme.etaleTopology P).app (op V)).hom
  by_cases hS : ∃ (c : ULift.{1} (ZMod q)), c • twGen 0 ζ = 0 ∧ c ≠ 0
  · obtain ⟨c, hc, hc0⟩ := hS
    have heq : φ (c • x) = φ 0 := by
      rw [φ.map_smul, φ.map_zero]; exact hc
    have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 heq
    by_cases hne : ∃ (U : Scheme.{0}) (f : U ⟶ V), (Presheaf.equalizerSieve (F := P) (X := op V) (c • x) 0).arrows f
    · exfalso
      obtain ⟨U, f, hf⟩ := hne
      apply hc0
      have h1 : (P.map f.op).hom (c • x) = (P.map f.op).hom 0 := hf
      rw [(P.map f.op).hom.map_smul, (P.map f.op).hom.map_zero] at h1
      let y : (twF q 0).obj Γ(U, ⊤) := ((twF q 0).map (Scheme.Γ.map f.op)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))
      have h3 : aug q Γ(U, ⊤) y = 1 := aug_map q _ _ _ ζ
      have h4 : aug q Γ(U, ⊤) (c • y) = c • aug q Γ(U, ⊤) y := (aug q _).map_smul c y
      have h5 : c • y = 0 := h1
      rw [h5, h3, map_zero, smul_eq_mul, mul_one] at h4
      exact h4.symm
    · left
      push Not at hne
      exact (tw q 0).isSeparated V _ hmem _ _ (fun U f hf => absurd hf (hne U f))
  · right
    intro c hc
    by_contra h0
    exact hS ⟨c, hc, h0⟩

end LateralTheory.E.LeafTw0TwFreePf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwResHtpyPf

theorem res_isKInj (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem htpy_of_qiso {C : Type*} [Category C] [Abelian C] {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] [I.IsKInjective] (u u' : L ⟶ I) (h : f ≫ u = f ≫ u') :
    Nonempty (Homotopy u u') := by
  have hY := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hY
  have hf : (HomotopyCategory.subcategoryAcyclic C).trW
      ((HomotopyCategory.quotient C _).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    assumption
  have hb := (hY _ hf).1
  have : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u' := by
    apply hb
    simp only [← Functor.map_comp, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _ this⟩

theorem sh_ext {R : Type} [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {X : Shv R}
    (φ ψ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj P ⟶ X)
    (h : toSheafify Scheme.etaleTopology.{0} P ≫ φ.hom = toSheafify Scheme.etaleTopology.{0} P ≫ ψ.hom) : φ = ψ := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

theorem tw_hom_ext (q : ℕ) (i : ℤ) {X : Shv (ZMod q)} (φ ψ : tw q i ⟶ X)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) : φ = ψ := by
  apply sh_ext
  ext U : 2
  apply ModuleCat.hom_ext
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
  exact h U.unop ζ

end LateralTheory.E.LeafTwResHtpyPf

open LateralTheory.E.LeafTwResHtpyPf in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := by
  intro q _ k T e hT u u' hu
  obtain ⟨_, ε, hε, he⟩ := hT
  have := res_isKInj (ZMod q) (tw q k)
  refine htpy_of_qiso ε u u' ?_
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0 := by
    apply tw_hom_ext
    intro U ζ
    have := hu U ζ
    rw [← he U ζ] at this
    exact this
  have h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  have h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  exact h1.trans ((congrArg _ key).trans h2.symm)
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitAWPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) (U : Scheme.{0}) :
    Subsingleton (Sec ((res R F).X s) U) := by
  have hz : IsZero ((res R F).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h2 : IsZero (((res R F).X s).obj.obj (op U)) :=
    Functor.map_isZero ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op U)) hz
  exact ModuleCat.isZero_iff_subsingleton.mp h2

theorem sub_zero_self {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i : 3
    simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem main_gen (q : ℕ) [NeZero q] (E : Spc) (i j : ℤ) (hij : i = j)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q j)))
    (hU : ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneLoc α)
    (n k : ℤ) (hnk : n = k) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q j)) k, μ.IsAW (show 0 + n = k by omega) α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast hnk hij (CohomologyClass.mk β : Ht q E n i) := by
  subst hij hnk
  refine ⟨β, ?_, rfl⟩
  intro N w h U x
  have hmz : ∀ (s t w : ℤ) (h : s + t = w) (a : Sec ((res _ (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
      s < 0 → μ.mul U s t w h a b = 0 := by
    intro s t w h a b hs
    have := sec_sub (tw q 0) s hs U
    rw [Subsingleton.elim a 0]
    simp
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · subst h
    show _ = (n * ((0 : ℕ) : ℤ)).negOnePow • μ.mul U (-((0 : ℕ) : ℤ) + 0) (-((N - 0 : ℕ) : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 _ rfl U (x.sub 0 0 (by omega))) (ev β.1 (N - 0) _ rfl U (x.sub 0 (N - 0) (by omega)))
    have h1 : (n * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [h1, one_smul]
    show _ = μ.mul U 0 (-(N : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β.1 N _ rfl U (x.sub 0 N (by omega)))
    rw [sub_zero_self]
    exact (eq_of_heq (hU U _ _ (by omega) _ (ev β.1 N _ rfl U x) (hα U (x.sub 0 0 (by omega))))).symm
  · intro p _
    rw [hmz, smul_zero]
    simp
    omega

theorem LeafUnitAW_of : LeafUnitAW := by
  intro q _ E i μ hU α hα n β
  exact main_gen q E i (0 + i) (by ring) μ hU α hα n (0 + n) (by ring) β

end LateralTheory.E.LeafUnitAWPf
end
end

section
open TensorProduct

namespace LateralTheory.E.LeafZModInjFlatPf

universe v

theorem flat_of_injective_of_ann {R : Type v} [CommRing R] [IsPrincipalIdealRing R]
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ s : R, r = s * a)
    (M : Type v) [AddCommGroup M] [Module R M] (hM : Module.Injective R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, rfl⟩ : ∃ a : R, I = Ideal.span {a} :=
    ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have ha : a ∈ Ideal.span ({a} : Set R) := Ideal.mem_span_singleton_self a
  have key : ∀ x : Ideal.span ({a} : Set R) ⊗[R] M, ∃ m : M, x = (⟨a, ha⟩ : Ideal.span ({a} : Set R)) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul i n =>
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 i.2
      refine ⟨s • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp [smul_eq_mul, hs]
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, (tmul_add _ _ _).symm⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := key x
  simp at hx
  obtain ⟨b, hba, hb⟩ := hP a
  have well : ∀ r r' : R, r * b = r' * b → r • m = r' • m := by
    intro r r' h
    obtain ⟨s, hs⟩ := hb (r - r') (by rw [sub_mul, h, sub_self])
    rw [← sub_eq_zero, ← sub_smul, hs, mul_smul, hx, smul_zero]
  let f : Ideal.span ({b} : Set R) → R := fun x => Classical.choose (Ideal.mem_span_singleton'.1 x.2)
  have hf : ∀ x, f x * b = x := fun x => Classical.choose_spec (Ideal.mem_span_singleton'.1 x.2)
  let g : Ideal.span ({b} : Set R) →ₗ[R] M :=
    { toFun := fun x => f x • m
      map_add' := fun x y => by
        rw [← add_smul]; apply well; rw [hf, add_mul, hf, hf]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_smul]; apply well; rw [hf, mul_assoc, hf]; rfl }
  obtain ⟨g', hg'⟩ := Module.Baer.of_injective hM _ g
  have hm : m = b • g' 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, hg' b (Ideal.mem_span_singleton_self b)]
    show m = f _ • m
    conv_lhs => rw [← one_smul R m]
    apply well; rw [hf, one_mul]
  rw [hm, ← smul_tmul]
  have : b • (⟨a, ha⟩ : Ideal.span ({a} : Set R)) = 0 := by ext; simp [smul_eq_mul, hba]
  rw [this, zero_tmul]

theorem zmod_ann (q : ℕ) [NeZero q] :
    ∀ a : ZMod q, ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ s, r = s * a := by
  intro a
  set d := Nat.gcd a.val q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hda : d ∣ a.val := Nat.gcd_dvd_left _ _
  have hq0 : q ≠ 0 := NeZero.ne q
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq0)
  refine ⟨((q / d : ℕ) : ZMod q), ?_, ?_⟩
  · conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [← Nat.cast_mul]
    obtain ⟨t, ht⟩ := hda
    have : q / d * a.val = q * t := by
      rw [ht, ← mul_assoc, Nat.div_mul_cancel hdq]
    rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  · intro r hr
    rw [← ZMod.natCast_zmod_val r, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdq) hd0
    have h2 : d * (q / d) ∣ r.val * (q / d) := by rwa [Nat.mul_div_cancel' hdq]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_right hqd h2
    refine ⟨a⁻¹ * t, ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hd, ← ZMod.mul_inv_eq_gcd]
    ring

instance pir_zmod (q : ℕ) : IsPrincipalIdealRing (ZMod q) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective

instance pir_ulift (q : ℕ) : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm
    (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm.surjective

theorem ulift_ann (q : ℕ) [NeZero q] :
    ∀ a : ULift.{1} (ZMod q), ∃ b, b * a = 0 ∧ ∀ r, r * b = 0 → ∃ s, r = s * a := by
  intro a
  obtain ⟨b, hba, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext _ _ hba, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext _ _ hs⟩

theorem LeafZModInjFlat_of : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := by
  intro q _ M _ _ hM
  exact flat_of_injective_of_ann (ulift_ann q) M hM

end LateralTheory.E.LeafZModInjFlatPf
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.Fix.EtaleChapterDTwo

theorem awSpec : LateralTheory.E.LeafA6suppPf.LeafAWSpec := by
  intro q _ E n m i j α β
  have hS := LateralTheory.Fix.CupProductTensor.cupSpec (ZMod q) (twPair q i j) E (rfl : n + m = n + m)
  obtain ⟨γ, hγ⟩ := hS.1 α β
  exact ⟨γ, hγ, hS.2 α β γ hγ⟩

theorem s0 : LateralTheory.E.D2.LeafA6nat := @_root_.LateralTheory.E.LeafA6nat_xy7V2Cut.goal_of
theorem s1 : LateralTheory.E.CupProductRingLaws.LeafCupSpec := @_root_.LateralTheory.Fix.CupProductTensor.cupSpec
theorem s2 : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := @_root_.LateralTheory.Fix.CupProductTensor.twPairExists
theorem s3 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of
theorem s4 : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of
theorem s5 : LateralTheory.E.ZModFlatnessFromBaerCriterion.TensTwRes := @_root_.GlobalTheory.EtC.isTwRes_tensor
theorem s6 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of
theorem s7 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of
theorem s8 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of s5 s6 s7
theorem s9 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of
theorem s10 : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := @_root_.LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of s3 s4 s8 s9
theorem s11 : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := @_root_.LateralTheory.E.FreeSheafGeneratorLifts.LeafHtpyAW_proved
theorem s12 : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := @_root_.LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of s1 s10 s11
theorem s13 : LateralTheory.E.LeafOneExistsPf.LeafUnitSec := @_root_.LateralTheory.E.UnitSections.LeafUnitSec_of
theorem s14 : LateralTheory.E.LeafOneSpecPf.LeafOneExists := @_root_.LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit s13
theorem s15 : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := @_root_.LateralTheory.E.LeafPrimCoverPf.leafPrimCover_pf
theorem s16 : LateralTheory.E.CupProductRingLaws.LeafOneSpec := @_root_.LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of s14 s15
theorem s17 : LateralTheory.E.LeafUnitActPf.LeafActSheaf := @_root_.LateralTheory.E.LeafActSheafPf.LeafActSheaf_of
theorem s18 : LateralTheory.E.LeafUnitPairGPf.LeafUnitAct := @_root_.LateralTheory.E.LeafUnitActPf.LeafUnitAct_of s17
theorem s19 : LateralTheory.E.LeafPairExtPf2.LeafTensUP := @_root_.LateralTheory.E.LeafTensUPPf.etale_tensor_pairing_universal_property_holds
theorem s20 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := @_root_.LateralTheory.E.LeafTw0LocGenPf.LeafTw0LocGen_of
theorem s21 : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := @_root_.LateralTheory.E.LeafTw0TwFreePf.LeafTw0TwFree_of
theorem s22 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := @_root_.LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0GenFree_of s21
theorem s23 : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := @_root_.LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of s20 s22
theorem s24 : LateralTheory.E.LeafTensMonoPf.LeafPreTensLocInj := @_root_.LateralTheory.E.LeafPreTensLocInjPf.LeafPreTensLocInj_of s23
theorem s25 : LateralTheory.E.LeafExtTensPf.LeafTensMono := @_root_.LateralTheory.E.LeafTensMonoPf.LeafTensMono_of s24
theorem s26 : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := @_root_.LateralTheory.E.LeafTensQIsoGenPf.LeafTensQIsoGen_of
theorem s27 : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := @_root_.LateralTheory.E.LeafSecInjPf.LeafSecInj_of
theorem s28 : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := @_root_.LateralTheory.E.LeafZModInjFlatPf.LeafZModInjFlat_of
theorem s29 : LateralTheory.E.LeafExtTensPf.LeafTensQIso := @_root_.LateralTheory.E.LeafTensQIsoPf.LeafTensQIso_of s26 s27 s28
theorem s30 : LateralTheory.E.LeafPairExtPf2.LeafExtTens := @_root_.LateralTheory.E.LeafExtTensPf.LeafExtTens_of s25 s29
theorem s31 : LateralTheory.E.LeafPairExtPf.LeafExtAlongAug := @_root_.LateralTheory.E.LeafPairExtPf2.LeafExtAlongAug_of s19 s30
theorem s32 : LateralTheory.E.LeafUnitPairGPf.LeafPairExt := @_root_.LateralTheory.E.LeafPairExtPf.LeafPairExt_of' s31
theorem s33 : LateralTheory.E.LeafUnitPairPf.LeafUnitPairG := @_root_.LateralTheory.E.LeafUnitPairGPf.LeafUnitPairG_of s18 s32
theorem s34 : LateralTheory.E.LeafRingUnitPf.LeafUnitPair := @_root_.LateralTheory.E.LeafUnitPairPf.LeafUnitPair_of s33
theorem s35 : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := @_root_.LateralTheory.E.PrimitiveRootLocalization.LeafPrimLoc_of
theorem s36 : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := @_root_.LateralTheory.E.LeafOneLocPf.LeafOneLoc_of s35
theorem s37 : LateralTheory.E.LeafRingUnitPf.LeafUnitAW := @_root_.LateralTheory.E.LeafUnitAWPf.LeafUnitAW_of
theorem s38 : LateralTheory.E.CupProductRingLaws.LeafRingUnit := @_root_.LateralTheory.E.LeafRingUnitPf.LeafRingUnit_of s1 s2 s12 s16 s34 s36 s37
theorem s39 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := @_root_.LateralTheory.Fix.CupProductTensor.ringAssoc
theorem s40 : LateralTheory.E.CupProductRingLaws.LeafRingComm := @_root_.LateralTheory.E.RingCommutativity.goal_of
theorem s41 : LateralTheory.E.D2.LeafA6ring := @_root_.LateralTheory.E.LeafA6ringCut.goal_of s38 s39 s40
theorem s42 : LateralTheory.E.D2.LeafRing := @_root_.LateralTheory.E.D2.LeafRing_of s0 s41
theorem s43 : LateralTheory.E.D2.LeafChern := @_root_.LateralTheory.E.D2.LeafChern_of
theorem s44 : LateralTheory.E.D2.LeafNat := @_root_.LateralTheory.E.D2.LeafNat_of s0
theorem s45 : LateralTheory.E.LeafGeomPf.LeafHalf1 := @_root_.LateralTheory.E.LeafHalf1Pf.LeafHalf1_of
theorem s46 : LateralTheory.E.HalfDegreeVanishing.LeafMapW := @_root_.LateralTheory.E.LeafMapWPf.LeafMapW_of
theorem s47 : LateralTheory.E.LeafGeomPf.LeafHalf2 := @_root_.LateralTheory.E.HalfDegreeVanishing.LeafHalf2_of s46
theorem s48 : LateralTheory.E.D2.LeafGeom := @_root_.LateralTheory.E.LeafGeomPfLoc.LeafGeom_of s45 s47
theorem s49 : LateralTheory.E.D2.LeafCover2 := @_root_.LateralTheory.E.LeafCover2Pf.LeafCover2_of
theorem s50 : LateralTheory.E.LeafA6suppPf.LeafAWSpec := awSpec
theorem s51 : LateralTheory.E.LeafA6suppPf.LeafRepVanish := @_root_.LateralTheory.E.LeafRepVanishPf.LeafRepVanish_of
theorem s52 : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := @_root_.LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of
theorem s53 : LateralTheory.E.D2.LeafA6supp := @_root_.LateralTheory.E.LeafA6suppPf.LeafA6supp_of s50 s51 s52
theorem s54 : LateralTheory.E.D2.LeafWhitney := @_root_.LateralTheory.E.D2.LeafWhitney_of s48 s49 s53 s0
theorem s55 : LateralTheory.E.D2.LeafLine := @_root_.LateralTheory.E.D2.LeafLine_of s0
theorem s56 : LateralTheory.E.D2.LeafNewton := @_root_.LateralTheory.E.LeafNewtonPf.LeafNewton_of
theorem s57 : LateralTheory.E.EtaleChapterDTwo := @_root_.LateralTheory.E.D2.goal_of s42 s43 s44 s54 s55 s56

theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDTwo := s57

end LateralTheory.Fix.EtaleChapterDTwo
end
end
