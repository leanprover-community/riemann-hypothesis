import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaCoordinateSchemeData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariable
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentInjectsSymmetricAntilinearCommuting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

theorem spMap_surj {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ β : R →+* R', spMap β = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

open MvPolynomial in

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o}

theorem isTM_unique (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] [IsReduced R] (z : Sp R ⟶ S) (sw : Sp R ⟶ Sp o)
    (e : z ≫ s = sw) (w : TObj g (N' ^ 2) J b sw) (φ φ' : w.A.left ⟶ t.A.left) (h : IsTM w t z φ)
    (h' : IsTM w t z φ') : φ = φ' := by
  obtain ⟨β, rfl⟩ := spMap_surj sw
  obtain ⟨w', hw'⟩ := tObj_pull o g _ J b _ _ s _ z t e
  obtain ⟨ψ, hψ⟩ := tMap_iff.1 hw'
  obtain ⟨χ, rfl, hχ⟩ := hψ.cancel (h.congr (Category.id_comp z).symm rfl)
  obtain ⟨χ', rfl, hχ'⟩ := hψ.cancel (h'.congr (Category.id_comp z).symm rfl)
  rw [(GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β w w' hm hd ho ?_).2 χ χ' hχ.1 hχ'.1 hχ.2.1 hχ'.2.1
    fun i => (hχ.2.2.1 i).trans (hχ'.2.2.1 i).symm]
  refine Dense.mono (fun p _ => ?_) dense_univ
  obtain ⟨u, hu⟩ := tObj_pull o g _ J b _ _ _ _ ((Sp R).fromSpecResidueField p) w rfl
  refine ⟨(Sp R).residueField p, inferInstance, (Sp R).fromSpecResidueField p, u, ?_, hu, ?_⟩
  · exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply _ _⟩
  · have := tMap_comp hu (tMap_iff.2 ⟨_, hχ⟩)
    rwa [Category.comp_id] at this

theorem exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) (ho : Odd N') (t : TObj g (N' ^ 2) J b s)
    (K : Type) [Field K] (y : Sp K ⟶ S) : ∃ v, t.HasTh y v := by
  obtain ⟨R, _, x, v, hx, hp, hv⟩ := ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho (y (IsLocalRing.closedPoint K))
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) q (IsLocalRing.closedPoint K)]
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ρ x v hv
  rw [hρ, IsOpenImmersion.lift_fac] at this
  exact ⟨_, this⟩

theorem eval_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    (t : TObj g (N' ^ 2) J b s) {K : Type} [Field K] (y : Sp K ⟶ S) (hy : FromC em C t y) (β : o →+* K)
    (hβ : y ≫ s = spMap β) (v : Ix g (N' ^ 2) → K) (hv : t.HasTh y v) :
    ∀ F ∈ thIdeal em C, MvPolynomial.eval₂ β v F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hj, hi, h1, h2, h3, hC⟩ := hy
  obtain ⟨v₀, hv₀⟩ := exists_hasTh_field hL hL2 ho t₀ K₀ (𝟙 _)
  have a1 : tx.HasTh (𝟙 _) v := (hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K _ v h1).2 (by rwa [Category.id_comp])
  have a2 : tx.HasTh (𝟙 _) (fun a => i (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx _ K _ _ h2).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap i)] at this)
  have a3 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc _ ℂ _ _ h3).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap j)] at this)
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ tx n K _ _ ⊥ hn hd a2 Ideal.isPrime_bot 0
  obtain ⟨u, hu⟩ := hasTh_unique_unit hL hL2 o g N' J b _ _ tx K _ _ _ a2 a1
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit (by simpa using hc)))
  obtain rfl : β = i.comp β₀ := spMap_inj (hβ.symm.trans (hi.trans (spMap_comp_eq _ _)))
  obtain rfl : v = fun a => (u : K) * i (v₀ a) := funext hu
  intro F hF
  rw [← F.sum_homogeneousComponent, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hG := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF e
  have h0 : MvPolynomial.eval₂ em (fun a => j (v₀ a)) (MvPolynomial.homogeneousComponent e F) = 0 := by
    simp only [thIdeal, Ideal.mem_iInf] at hG
    exact hG tc _ ⟨hC, a3⟩
  have h4 : MvPolynomial.eval₂ β₀ v₀ (MvPolynomial.homogeneousComponent e F) = 0 := by
    apply j.injective
    rw [MvPolynomial.eval₂_comp_left, hj, map_zero]
    exact h0
  rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous e F)]
  have h5 := congrArg i h4
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h5
  exact mul_eq_zero_of_right _ h5

theorem dense_affine {k : ℕ} {b : TBase o k} {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {t : TObj g k J b s}
    (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] (x : Sp R ⟶ S) [IsOpenImmersion x] :
    Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (ψ : R →+* K), p ∈ Set.range (spMap ψ) ∧ FromC em C t (spMap ψ ≫ x)} := by
  refine Dense.mono (fun p hp => ?_) (hD.preimage x.isOpenEmbedding.isOpenMap)
  obtain ⟨K, _, y, ⟨q, hq⟩, hy⟩ := hp
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q', rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) q' q, hq]
    exact ⟨p, rfl⟩
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have e : spMap ρ ≫ x = y := by rw [hρ, IsOpenImmersion.lift_fac]
  refine ⟨K, inferInstance, ρ, ⟨q, x.isOpenEmbedding.injective ?_⟩, by rwa [e]⟩
  rw [← Scheme.Hom.comp_apply, e, hq]

theorem inMM_of_dense (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (β : o →+* R) (hβ : x ≫ s = spMap β) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v) :
    InMM n N' (thIdeal em C) β v := by
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q hn hd hv hq⟩
  by_contra hne
  have hb : PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) ≠ ⊥ := fun h =>
    hne ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 h).eq_zero
  obtain ⟨p, ⟨K, _, ψ, ⟨q, rfl⟩, hy⟩, hp⟩ := (dense_affine hD x).exists_mem_open
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F)).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb)
  have h0 := eval_eq_zero_of_fromC hL hL2 hn hd ho hem t _ hy (ψ.comp β)
    (by rw [Category.assoc, hβ, spMap_comp_eq]) _ (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ψ x v hv) F hF
  refine hp (show ψ (MvPolynomial.eval₂ β v F) ∈ (show PrimeSpectrum K from q).asIdeal from ?_)
  rw [MvPolynomial.eval₂_comp_left]
  exact (show MvPolynomial.eval₂ (ψ.comp β) (ψ ∘ v) F = 0 from h0) ▸ Ideal.zero_mem _

theorem tMap_affine (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (w₀ : J) (hC : ∀ t, C t → t.Shape Mat κ) {M : Scheme.{0}} {sM : M ⟶ Sp o} (u : TObj g (N' ^ 2) J b sM)
    (hu : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M) (t' : TObj g (N' ^ 2) J b (x ≫ sM)) v,
      t'.Shape Mat κ → t'.HasTh (𝟙 _) v → u.HasTh x v → TMap t' u x)
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (y : Sp R ⟶ M) (hxy : y ≫ sM = x ≫ s) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v)
    (hv' : u.HasTh y v) (w : TObj g (N' ^ 2) J b (x ≫ s)) (hw : TMap w t x) : TMap w u y := by
  obtain ⟨β, hβ⟩ := spMap_surj (x ≫ s)
  obtain ⟨tx, htx⟩ := tObj_pull o g _ J b _ _ s _ x t hβ.symm
  obtain ⟨ux, hux⟩ := tObj_pull o g _ J b _ _ sM _ y u (hxy.trans hβ.symm)
  have key : TMap tx ux (𝟙 _) := by
    refine (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β tx ux hm hd ho (Dense.mono (fun p hp => ?_) (dense_affine hD x))).1
    obtain ⟨K, _, ψ, ⟨q, rfl⟩, K₀, _, β₀, i, j, t₀, tK, tc, -, -, h1, h2, h3, hc⟩ := hp
    let a := algebraMap K (AlgebraicClosure K)
    have ez : spMap a ≫ spMap ψ = spMap (a.comp ψ) := spMap_comp_eq _ _
    obtain ⟨t', ht'⟩ := tObj_pull o g _ J b _ _ _ ((spMap (a.comp ψ) ≫ y) ≫ sM) (spMap (a.comp ψ)) tx
      (by rw [Category.assoc, hxy, hβ])
    obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ _ _ (spMap (a.comp ψ)) tx rfl
    have s0 : t₀.Shape Mat κ := ((GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tc h3).2.2 K₀ rfl
      inferInstance inferInstance).1 (hC tc hc)
    have s1 : tK.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tK h2).1 s0
    have m1 : TMap t' t (spMap (a.comp ψ) ≫ x) := tMap_comp ht' htx
    have m2 : TMap t' tK (spMap a) := tMap_cancel h1 (by rwa [← Category.assoc, ez])
    have s2 : t'.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ tK t' m2).1 s1
    have m3 : TMap t' u (spMap (a.comp ψ) ≫ y) := hu _ _ t' _ s2
      ((hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' _ _ _ _ m1).2 (by
        rw [Category.id_comp]; exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R _ (a.comp ψ) x v hv))
      (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b M sM u R _ (a.comp ψ) y v hv')
    have m4 : TMap u' t' (𝟙 _) := tMap_cancel ht' (by rwa [Category.id_comp])
    have m5 := tMap_comp m4 m3
    rw [Category.id_comp] at m5
    refine ⟨AlgebraicClosure K, inferInstance, spMap (a.comp ψ), u', ⟨IsLocalRing.closedPoint _, ?_⟩, hu',
      tMap_cancel hux m5⟩
    rw [← ez]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) _ _))
  have m : TMap w tx (𝟙 _) := tMap_cancel htx (by rwa [Category.id_comp])
  have := tMap_comp (tMap_comp m key) hux
  rwa [Category.id_comp, Category.id_comp] at this

theorem family_universal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  refine ⟨2, fun j hj o _ b em C d hem hC Y u hu hq S s' t hS hD => ?_⟩
  have ho : Odd (n ^ j) := hodd.pow
  have hd : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have hd1 : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hred : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ S), IsOpenImmersion x → _root_.IsReduced R := fun R _ x _ =>
    (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)
  have uniq : ∀ (R : Type) [CommRing R] (y y' : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), y ≫ Y.s = y' ≫ Y.s →
      u.HasTh y v → u.HasTh y' v → y = y' := by
    intro R _ y y' v e h h'
    obtain ⟨β, hβ⟩ := spMap_surj (y ≫ Y.s)
    exact (Y.pts R β v (Y.loc R β y v hβ.symm ((hu R y v).1 h))).unique ⟨hβ.symm, (hu R y v).1 h⟩
      ⟨e.symm.trans hβ.symm, (hu R y' v).1 h'⟩
  choose R cR x v hx hp hv using ThetaLocal.exists_hasTh hL hL2 o g _ J b S s' t ho
  have loc : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = x p ≫ s' ∧ u.HasTh y (v p) := fun p => by
    have := hx p
    have := hred _ _ (hx p)
    obtain ⟨β, hβ⟩ := spMap_surj (x p ≫ s')
    obtain ⟨y, ⟨h1, h2⟩, -⟩ := Y.pts _ β _ (inMM_of_dense hL hL2 hn.two_le hd1 ho hem.2.2 hD (x p) β hβ.symm _ (hv p))
    exact ⟨y, h1.trans hβ, (hu _ _ _).2 h2⟩
  choose y hy hy' using loc
  choose tx htx using fun p => tObj_pull o g _ J b _ _ s' _ (x p) t rfl
  have hty : ∀ p, TMap (tx p) u (y p) := fun p =>
    haveI := hx p
    haveI := hred _ _ (hx p)
    tMap_affine hL hL2 hn.two_le hd ho w (fun t ht => (hC.shape t ht).1) u
      (fun K _ _ x t' v h1 h2 h3 => hq K x t' v h1 h2 ((hu _ _ _).1 h3)) hD (x p) (y p) (hy p) (v p) (hv p) (hy' p)
      (tx p) (htx p)
  have tr : ∀ p (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R p)) (c : Ix g ((n ^ j) ^ 2) → T),
      t.HasTh (a ≫ x p) c → u.HasTh (a ≫ y p) c := fun p T _ a c h =>
    (hasTh_iff_of_tmap o g _ J b _ _ u _ _ (tx p) _ T a c (hty p)).1
      ((hasTh_iff_of_tmap o g _ J b _ _ t _ _ (tx p) _ T a c (htx p)).2 h)
  obtain ⟨f, hf⟩ := exists_glue _ x y hx (fun p => ⟨p, hp p⟩) fun i i' q hq => by
    have := hx i
    have := hx i'
    obtain ⟨T, z, hz, ⟨r, hr⟩, hs⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := x i q) ⟨⟨q, rfl⟩, hq⟩
    obtain ⟨a, e1⟩ : ∃ a : Sp T ⟶ Sp (R i), a ≫ x i = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i) z (fun p hp => (hs hp).1)⟩
    obtain ⟨a', e2⟩ : ∃ a' : Sp T ⟶ Sp (R i'), a' ≫ x i' = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i') z (fun p hp => (hs hp).2)⟩
    have : IsOpenImmersion (a ≫ x i) := by rw [e1]; exact hz
    refine ⟨_, a, a', IsOpenImmersion.of_comp a (x i), ⟨r, (x i).isOpenEmbedding.injective ?_⟩, e1.trans e2.symm, ?_⟩
    · rw [← Scheme.Hom.comp_apply, e1, hr]
    · obtain ⟨ρ, hρ⟩ := spMap_surj (R' := T) a
      have h := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g _ J b S s' t _ T ρ (x i) (v i) (hv i)
      rw [hρ] at h
      refine uniq T _ _ _ ?_ (tr i T a _ h) (tr i' T a' _ (by rw [e2, ← e1]; exact h))
      rw [Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ s') (e1.trans e2.symm)
  have hfs : f ≫ Y.s = s' := hom_ext_loc fun p => ⟨_, x p, hx p, hp p, by rw [← Category.assoc, hf, hy]⟩
  refine ⟨f, ⟨hfs, ?_⟩, fun f' hf' => hom_ext_loc fun p => ⟨_, x p, hx p, hp p, ?_⟩⟩
  · obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ Y.s s' f u hfs
    have := tMap_comp (tMap_of_loc hL.globalFns t u'
      (fun p => ⟨_, x p, tx p, hx p, hp p, htx p, tMap_cancel hu' (by rw [hf]; exact hty p)⟩)
      (fun t T _ z => tObj_pull o g _ J b _ _ s' _ z t rfl)
      (fun t T _ z w φ φ' hz h h' => haveI := hred T z hz
        isTM_unique hL hL2 hn.two_le hd ho t T z _ rfl w φ φ' h h')) hu'
    rwa [Category.id_comp] at this
  · rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf'.1, hy])
      ((hasTh_iff_of_tmap o g _ J b _ _ u _ _ t f' _ (x p) (v p) hf'.2).1 (hv p)) (hy' p)

end GlobalTheory.FamRep
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIdealFamily_universal_property : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  first | exact @GlobalTheory.FamRep.family_universal | exact GlobalTheory.FamRep.family_universal | (intros; apply GlobalTheory.FamRep.family_universal <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem tangent_eq_constPt_of_tMap : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  intro hL hL2 o _ g n N' J b I Y u hN hu K _ x t hs h1 h2
  have hsub : Subsingleton (PrimeSpectrum (DualNumber K)) := by
    have key : ∀ p : PrimeSpectrum (DualNumber K),
        p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom := by
      intro p
      have hp := p.isPrime
      have hle : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom ≤ p.asIdeal := by
        intro a ha
        have ha' : a.fst = 0 := ha
        apply hp.mem_of_pow_mem 2
        have : a ^ 2 = 0 := by
          rw [sq]; ext <;> simp [ha']
        rw [this]; exact p.asIdeal.zero_mem
      have hmax : (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨TrivSqZeroExt.inl c, rfl⟩)
      exact (hmax.eq_of_le hp.ne_top hle).symm
    exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩
  have hsub' : Subsingleton (Sp (DualNumber K)) := hsub
  obtain ⟨p⟩ : Nonempty (Sp (DualNumber K)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber K)))
  obtain ⟨R, _, j, v, hj, ⟨q, _⟩, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base hL hL2 o g N' J b _ _ t hN p
  have hsurj : Function.Surjective j := fun y => ⟨q, Subsingleton.elim _ _⟩
  have hiso : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext y
    simpa using hsurj y
  have c1 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t x R j v h1).1 hv)
  have c2 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t (constPt x) R j v h2).1 hv)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (R := CommRingCat.of o) (S := CommRingCat.of R) (j ≫ x ≫ Y.s)
  have e1 : (j ≫ x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc]; exact hβ.symm
  have e2 : (j ≫ constPt x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc, ← hs]; exact hβ.symm
  have h := (Y.pts R β.hom v (Y.loc R β.hom _ v e1 c1)).unique ⟨e1, c1⟩ ⟨e2, c2⟩
  exact (cancel_epi j).1 h

end GlobalTheory.ZM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_zero_of_object_constant_along : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  atlas_forward_decl GlobalTheory.ZM.tangent_eq_constPt_of_tMap
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ThetaFamily

theorem exists_coord_of_isLocalRing {X : Scheme.{0}} {M : LB X} {σ : Type} (th : σ → M.Sec) (hM : M.IsLB)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) : ∃ v, SecCoord M th x v := by
  obtain ⟨k, hk⟩ : ∃ k, x (IsLocalRing.closedPoint R) ∈ M.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge trivial)
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  exact ((IsLocalRing.specializes_closedPoint y).map x.continuous).mem_open (M.U k).isOpen hk

theorem nonempty_thetaFam : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  intro h₁ h₂ hcrit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, hglue⟩ := GlobalTheory.T.exists_thetaFamily_over_thetaPointScheme h₁ h₂ hcrit g J Mat κ n w w' hn hodd
  obtain ⟨j₂, hrep⟩ := GlobalTheory.T.thetaIdealFamily_universal_property h₁ h₂ g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d hb hC => ?_⟩
  have := hb.1
  obtain ⟨i₁, i₂, i₃⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C hb.2.2
  obtain ⟨Y⟩ := GlobalTheory.ZM.nonempty_MMPre o g n (n ^ j) (thIdeal em C) (pow_pos hn.pos j) i₁ i₂ i₃
  obtain ⟨t, hd, -, hth, hfib⟩ := hglue j (le_of_max_le_left hj) o b em C d hb hC Y
  refine ⟨{ MM := Y.MM
            s := Y.s
            qproj := Y.qproj
            flat := Y.flat
            reduced := Y.reduced
            univ := t
            dense := hd
            loc := fun R _ _ β x hx => ?_
            pts := fun R _ β v hv => ?_
            rep := hrep j (le_of_max_le_right hj) o b em C d hb hC Y t hth hfib
            unram := GlobalTheory.T.tangentVector_zero_of_object_constant_along h₁ h₂ o g n (n ^ j) J b _ Y t hodd.pow hth }⟩
  · obtain ⟨v, hv⟩ := exists_coord_of_isLocalRing Y.th Y.isLB x
    exact ⟨v, (hth R x v).2 hv, Y.loc R β x v hx hv⟩
  · simpa only [hth] using Y.pts R β v hv

end GlobalTheory.ZM.ThetaFamily
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaObject_family_open_closure : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  atlas_forward_decl GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericTrdeg

theorem exists_hom_of_ker_eq {R K K' : Type} [CommRing R] [Field K] [Field K'] (φ : R →+* K) (θ : R →+* K')
    (hk : RingHom.ker θ = RingHom.ker φ) (hs : ∀ z : K, ∃ a b, z = φ a / φ b) :
    ∃ j : K →+* K', j.comp φ = θ := by
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : IsFractionRing (R ⧸ RingHom.ker φ) K := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, h⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  let g : (R ⧸ RingHom.ker φ) →+* K' := Ideal.Quotient.lift _ θ (fun a ha => by rw [← hk] at ha; exact ha)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hk]
    exact ha
  refine ⟨IsFractionRing.lift hg, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (K := K) hg (Ideal.Quotient.mk _ a)

theorem exists_local_domain {A K : Type} [CommRing A] [Field K] (e : A →+* K) (P : Ideal A) [P.IsPrime]
    (hP : P ≤ RingHom.ker e) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (ρ : A →+* R') (ψ : R' →+* K),
      RingHom.ker ρ = P ∧ ψ.comp ρ = e ∧ ∀ r, ψ r ≠ 0 → IsUnit r := by
  let e' : A ⧸ P →+* K := Ideal.Quotient.lift P e (fun a ha => hP ha)
  haveI : (RingHom.ker e').IsPrime := RingHom.ker_isPrime e'
  let R' := Localization.AtPrime (RingHom.ker e')
  have hu : ∀ y : (RingHom.ker e').primeCompl, IsUnit (e' y) := fun y =>
    isUnit_iff_ne_zero.2 y.2
  have hinj : Function.Injective (algebraMap (A ⧸ P) R') :=
    IsLocalization.injective R' (RingHom.ker e').primeCompl_le_nonZeroDivisors
  refine ⟨R', inferInstance, inferInstance, (algebraMap (A ⧸ P) R').comp (Ideal.Quotient.mk P),
    IsLocalization.lift hu, ?_, ?_, ?_⟩
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  · intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e').primeCompl r
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R' (RingHom.ker e')]
    intro ha
    apply hr
    rw [IsLocalization.lift_mk']
    rw [show e' a = 0 from ha, zero_mul]

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_factor {X : Scheme.{0}} {R R' K : Type} [CommRing R] [CommRing R'] [Field K] (x : Sp R ⟶ X)
    [IsOpenImmersion x] (x' : Sp R' ⟶ X) (φ : R →+* K) (ψ : R' →+* K) (hψ : ∀ r, ψ r ≠ 0 → IsUnit r)
    (h : spMap ψ ≫ x' = spMap φ ≫ x) : ∃ χ : R →+* R', spMap χ ≫ x = x' ∧ ψ.comp χ = φ := by
  have hr : Set.range x' ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    let pt : Sp K := (⊥ : PrimeSpectrum K)
    have hsp : q ⤳ spMap ψ pt := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro r hr
      change ψ r ∈ (⊥ : Ideal K)
      by_contra hne
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hr (hψ r hne))
    have hmem : x' (spMap ψ pt) ∈ Set.range x := by
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (hsp.map x'.continuous).mem_open x.isOpenEmbedding.isOpen_range hmem
  have hχ : spMap (Spec.preimage (IsOpenImmersion.lift x x' hr)).hom ≫ x = x' := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  refine ⟨_, hχ, spMap_inj ?_⟩
  rw [← cancel_mono x, ← spMap_comp, Category.assoc, hχ, h]

theorem exists_algebraicIndependent : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  intro hL hL2 n g N' J Mat κ w w' o _ b em C d F hA hG R _ _ x hx hxs K _ _ φ hmin hsurj
  have hη : (spMap φ.toRingHom ≫ x) ≫ F.s = spMap (algebraMap o K) := by
    rw [Category.assoc, hxs, spMap_comp]
    congr 1
    exact φ.comp_algebraMap
  obtain ⟨v, hv, hvI⟩ := F.loc K (algebraMap o K) _ hη
  let e : MvPolynomial (Ix g (N' ^ 2)) o →+* K := MvPolynomial.eval₂Hom (algebraMap o K) v
  have hN : N' ≠ 0 := by
    rintro rfl
    have := b.unit.map (algebraMap o K)
    simp at this
  obtain ⟨c₁, hc₁⟩ := hvI.2 ⊥ Ideal.isPrime_bot 0
  set a₁ := 0 + (N' / n) • c₁ with ha₁
  have hva₁ : v a₁ ≠ 0 := hc₁
  obtain ⟨P, a₀, a, hP, hIP, hPp, -, hind⟩ := GlobalTheory.ThetaPrime.exists_prime_independent_ratios hL hL2 g N' J Mat κ w w' o b em C d hA hG
    (RingHom.ker e) a₁ hN (RingHom.ker_isPrime e) (fun G hG => hvI.1 G hG)
    (by simpa [e, RingHom.mem_ker] using hva₁)
  obtain ⟨R', _, _, ρ, ψ, hρ, hψρ, hψ⟩ := exists_local_domain e P hPp
  let β' : o →+* R' := ρ.comp MvPolynomial.C
  let v' : Ix g (N' ^ 2) → R' := fun i => ρ (MvPolynomial.X i)
  have hev : MvPolynomial.eval₂Hom β' v' = ρ := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [β', v']
  have hψv : (fun i => ψ (v' i)) = v := by
    funext i
    have := RingHom.congr_fun hψρ (MvPolynomial.X i)
    simpa [e] using this
  have hψβ : ψ.comp β' = algebraMap o K := by
    ext i
    have := RingHom.congr_fun hψρ (MvPolynomial.C i)
    simpa [e, β'] using this
  have hI' : InMM n N' (thIdeal em C) β' v' := by
    refine ⟨fun G hG => ?_, fun q hq i => ?_⟩
    · have : ρ G = 0 := by rw [← RingHom.mem_ker, hρ]; exact hIP hG
      rw [← hev] at this
      exact this
    · obtain ⟨c, hc⟩ := hvI.2 ⊥ Ideal.isPrime_bot i
      refine ⟨c, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
      rw [congrFun hψv]
      exact hc
  obtain ⟨x', ⟨hx's, hx'v⟩, -⟩ := F.pts R' β' v' hI'
  have hcl : spMap ψ ≫ x' = spMap φ.toRingHom ≫ x := by
    refine (F.pts K (algebraMap o K) v hvI).unique ⟨?_, ?_⟩ ⟨hη, hv⟩
    · rw [Category.assoc, hx's, spMap_comp, hψβ]
    · have := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K ψ x' v' hx'v
      rwa [hψv] at this
  obtain ⟨χ, hχx, hψχ⟩ := exists_factor x x' φ.toRingHom ψ hψ hcl
  let K' := FractionRing R'
  let lam : R' →+* K' := algebraMap R' K'
  have hlam : Function.Injective lam := IsFractionRing.injective R' K'
  have hker : RingHom.ker (lam.comp χ) = RingHom.ker φ.toRingHom := by
    have hle : RingHom.ker (lam.comp χ) ≤ RingHom.ker φ.toRingHom := by
      intro r hr
      rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam] at hr
      rw [RingHom.mem_ker, ← hψχ, RingHom.comp_apply, hr, map_zero]
    exact le_antisymm hle (hmin.2 ⟨RingHom.ker_isPrime _, bot_le⟩ hle)
  obtain ⟨j, hj⟩ := exists_hom_of_ker_eq φ.toRingHom (lam.comp χ) hker hsurj
  have hpt : spMap j ≫ spMap φ.toRingHom ≫ x = spMap lam ≫ x' := by
    rw [← Category.assoc, spMap_comp, hj, ← spMap_comp, Category.assoc, hχx]
  have h1 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ K K' j _ v hv
  have h2 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K' lam _ v' hx'v
  rw [hpt] at h1
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ F.univ K' _ _ _ h1 h2
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a₁, rfl⟩)
      (isUnit_iff_ne_zero.2 ((map_ne_zero j).2 hva₁)))
  have hjβ : j.comp (algebraMap o K) = lam.comp β' := by
    apply spMap_inj
    rw [← spMap_comp, ← hη, ← Category.assoc, hpt, Category.assoc, hx's, spMap_comp]
  have hkP : RingHom.ker (MvPolynomial.eval₂Hom (lam.comp β') (fun i => lam (v' i))) = P := by
    rw [← MvPolynomial.comp_eval₂Hom, hev, ← hρ]
    ext G
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam, RingHom.mem_ker]
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K' _ _ hkP G ?_⟩
  have h3 := congrArg j hG
  rw [MvPolynomial.aeval_def, MvPolynomial.hom_eval₂, hjβ, map_zero] at h3
  rw [← h3]
  congr 1
  funext i
  rw [hu, hu, mul_div_mul_left _ _ u.ne_zero, map_div₀]

end GlobalTheory.ZM.GenericTrdeg
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaClosure_component_trdeg_ge : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  atlas_forward_decl GlobalTheory.ZM.GenericTrdeg.exists_algebraicIndependent
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.GenericSmooth

theorem le_ringKrullDim_of_mem_minimalPrimes (o k R S : Type) [CommRing o] [IsDomain o] [Field k]
    [CommRing R] [CommRing S] [Algebra o k] [IsFractionRing o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    [IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S]
    [Algebra.FiniteType k S] (d : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R →
      (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  let K := FractionRing (S ⧸ q)
  let ψ : S →ₐ[o] K := (IsScalarTower.toAlgHom o (S ⧸ q) K).comp (Ideal.Quotient.mkₐ o q)
  let φ : R →ₐ[o] K := ψ.comp (IsScalarTower.toAlgHom o R S)
  have hψ : ∀ s, ψ s = 0 ↔ s ∈ q := fun s ↦ by
    change algebraMap (S ⧸ q) K (Ideal.Quotient.mk q s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker φ = q.under R := by
    ext r
    exact hψ (algebraMap R S r)
  have hmin : RingHom.ker φ ∈ minimalPrimes R := by
    have h' := IsLocalization.minimalPrimes_map
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S ⊥
    rw [Ideal.map_bot] at h'
    rw [hker]
    exact h'.le hq
  have hs : ∀ s : S, ∃ a b, φ b ≠ 0 ∧ ψ s = φ a / φ b := fun s ↦ by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) s
    have hb : φ b ≠ 0 := ((IsLocalization.map_units S b).map ψ).ne_zero
    refine ⟨a, b, hb, ?_⟩
    rw [eq_div_iff hb]
    have := congrArg ψ hab
    rw [map_mul] at this
    exact this
  have hsurj : ∀ z : K, ∃ a b, z = φ a / φ b := fun z ↦ by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ q) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, b, hb, h₁⟩ := hs x
    obtain ⟨a', b', hb', h₂⟩ := hs y
    refine ⟨a * b', b * a', ?_⟩
    change ψ x / ψ y = _
    rw [h₁, h₂, map_mul, map_mul, div_div_div_eq]
  obtain ⟨y, hy⟩ := h K φ hmin hsurj
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (S ⧸ q)
  have hk : AlgebraicIndependent k y := by
    have : Algebra.IsAlgebraic o k := IsLocalization.isAlgebraic k (nonZeroDivisors o)
    exact hy.extendScalars k
  have h₃ := hk.cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic (S ⧸ q) K := IsLocalization.isAlgebraic K (nonZeroDivisors (S ⧸ q))
  have : FaithfulSMul k (S ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (S ⧸ q)).injective
  rw [← trdeg_add_eq k (S ⧸ q) (A := K), trdeg_eq_zero (R := S ⧸ q) (A := K), add_zero, h₂,
    Cardinal.mk_fin] at h₃
  rw [h₁]
  exact_mod_cast h₃

theorem finrank_derivation_le (o k R S C : Type) [CommRing o] [CommRing k]
    [CommRing R] [CommRing S] [Field C] [Algebra o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    (M : Submonoid R) [IsLocalization M S] [Algebra.FiniteType o R]
    [Algebra k C] [Algebra S C] [IsScalarTower k S C] [Algebra o C] [Algebra R C]
    [IsScalarTower o R C] [IsScalarTower R S C] [IsScalarTower o S C] [IsScalarTower o k C] :
    Module.finrank C (Derivation k S C) ≤ Module.finrank C (Derivation o R C) := by
  have : Module.Finite C (Derivation o R C) :=
    Module.Finite.equiv (GlobalTheory.SmoothTangent.derivationEquivDual o R C).symm
  let f : Derivation k S C →ₗ[C] Derivation o R C :=
    { toFun := fun D ↦ (D.restrictScalars o).compAlgebraMap R
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [injective_iff_map_eq_zero]
  intro D hD
  have h0 : ∀ r, D (algebraMap R S r) = 0 := fun r ↦ congr($hD r)
  ext s
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M s
  have := congrArg D hab
  rw [D.leibniz, h0, h0, smul_zero, zero_add, Algebra.smul_def] at this
  exact (mul_eq_zero.mp this).resolve_left
    ((IsLocalization.map_units S b).map (algebraMap S C)).ne_zero

end GlobalTheory.GenericSmooth

namespace GlobalTheory

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le :
    ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  intro o _ _ em R _ _ d hem hft hind htan
  let e : FractionRing o →+* ℂ := IsFractionRing.lift hem
  have : CharZero (FractionRing o) := e.charZero
  have := IsLocalization.tensorRight (S := R) (FractionRing o) (nonZeroDivisors o)
  refine smoothOfRelativeDimension_of_dim_of_finrank_derivation_le (FractionRing o) e _ d
    inferInstance
    (GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes o (FractionRing o) R _ d hind) ?_
  intro _ _ _ he
  let : Algebra o ℂ := em.toAlgebra
  let : Algebra R ℂ :=
    ((algebraMap (FractionRing o ⊗[o] R) ℂ).comp (algebraMap R _)).toAlgebra
  have h₁ : IsScalarTower o (FractionRing o) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [he]
    exact (IsFractionRing.lift_algebraMap hem x).symm
  have h₂ : IsScalarTower o (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply o (FractionRing o) ℂ,
      IsScalarTower.algebraMap_apply (FractionRing o) (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o (FractionRing o) (FractionRing o ⊗[o] R)]
  have h₃ : IsScalarTower R (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun _ ↦ rfl
  have h₄ : IsScalarTower o R ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o R (FractionRing o ⊗[o] R),
      ← IsScalarTower.algebraMap_apply o (FractionRing o ⊗[o] R) ℂ]
  exact (GenericSmooth.finrank_derivation_le o (FractionRing o) R _ ℂ
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))).trans (htan rfl)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.smooth_genericFibre_of_independent_and_tangent_bound : ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  atlas_forward_decl GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.smooth_genericFibre_of_affine_opens : ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | exact GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | (intros; apply GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem finiteType_of_isQProjOver_affineOpen {o : Type} [CommRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (hs : IsQProjOver s) (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (hx : x ≫ s = spMap (algebraMap o R)) : Algebra.FiniteType o R := by
  obtain ⟨N, i, hi, -, rfl⟩ := hs
  have := isProper_str o N
  have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
    rw [← hx]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  exact RingHom.finiteType_algebraMap.mp h

theorem ThetaFam.smooth_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → (∀ (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hb hC ht
  have : IsDedekindDomain o := hb.1
  refine GlobalTheory.T.smooth_genericFibre_of_affine_opens o F.MM F.s d fun R _ _ x hx hxs => ?_
  exact GlobalTheory.T.smooth_genericFibre_of_independent_and_tangent_bound o em R d hb.2.2 (finiteType_of_isQProjOver_affineOpen F.qproj R x hxs)
    (GlobalTheory.T.thetaClosure_component_trdeg_ge h1 h2 n g N' J Mat κ w w' o b em C d F hb hC R x hx hxs)
    (fun he => ht R x hx hxs he)

end GlobalTheory.ZM
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.thetaFam_isPEL : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (n N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ F : ThetaFam n em (PELClass (b := b) D a bas ρ em), ∃ τ : SAB H F.MM, IsPEL D a bas ρ F.univ τ := by
  intro h1 h2 h3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl n N' o _ b em ρ hρ hem F
  obtain ⟨hded, -, hinj⟩ := hem
  have := F.reduced
  have : LocallyOfFiniteType F.s := by
    obtain ⟨N, i, hi, -, hs⟩ := F.qproj
    have := isProper_str o N
    rw [← hs]
    infer_instance
  have : IsLocallyNoetherian F.MM := LocallyOfFiniteType.isLocallyNoetherian F.s
  exact GlobalTheory.T.exists_isPELTriple_of_dense_fibres h1 h2 h3 E H D g J a bas w w' hpq hbas hw hw' hcl (N' ^ 2) o b em ρ F.MM F.s F.univ hρ hinj F.dense
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem eq_zero_of_line_subset_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (v : Fin g → ℂ) (hv : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  by_contra h
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hinj : Function.Injective (fun t : ℂ => (⟨t • v, hv t⟩ : Λ)) := by
    intro s t hst
    exact smul_left_injective ℂ h (congrArg Subtype.val hst)
  have : Countable ℂ := hinj.countable
  have : Countable ℝ := Complex.ofReal_injective.countable
  exact not_countable this

theorem linear_eq_of_ex_eq {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' := by
  have hd := u.discrete
  have hm : ∀ z, F z - F' z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (F z - F' z) (F' z)
    rw [sub_add_cancel, h z] at h1
    exact (mul_eq_right.mp h1.symm)
  refine LinearMap.ext fun z => sub_eq_zero.mp (eq_zero_of_line_subset_discrete u.Λ _ fun t => ?_)
  have := hm (t • z)
  rwa [map_smul, map_smul, ← smul_sub] at this

theorem exists_linear_lift_action : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (∀ (f : P₀.A ⟶ P₀.A) (F F' : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f) → F = F') ∧ ∀ (O : Type) [CommRing O] (act : OAct O P₀.A), ∃ F : O →+* Module.End ℂ (Fin P₀.g → ℂ), ∀ a z, u.ex (F a z) = u.ex z ≫ act.act a := by
  intro P₀ u Hm χ hu
  refine ⟨fun f F F' h h' => linear_eq_of_ex_eq u F F' fun z => (h z).trans (h' z).symm, ?_⟩
  intro O _ act
  choose F hF using fun a => hu.endo (act.act a) (act.hom a)
  have hone : F 1 = (1 : Module.End ℂ (Fin P₀.g → ℂ)) :=
    linear_eq_of_ex_eq u _ _ fun z => by rw [hF, act.one, Category.comp_id]; rfl
  have hmul : ∀ a b, F (a * b) = (F a : Module.End ℂ (Fin P₀.g → ℂ)) * F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, mul_comm a b, act.mul, Module.End.mul_apply, hF, hF, Category.assoc]
  have hadd : ∀ a b, F (a + b) = F a + F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, act.add, LinearMap.add_apply, u.ex_add, hF, hF, MonObj.comp_mul]
  exact ⟨RingHom.mk' ⟨⟨F, hone⟩, hmul⟩ hadd, hF⟩

end GlobalTheory.KS
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.DimPEL

theorem exists_sum_eigen {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : 𝓞 E →+* Module.End ℂ V) (v : V) :
    ∃ w : (E →+* ℂ) → V, (∀ τ (a : 𝓞 E), F a (w τ) = τ (a : E) • w τ) ∧ v = ∑ τ, w τ := by
  classical
  let B := canonicalEmbedding.latticeBasis E
  let Φ : ((E →+* ℂ) → ℂ) →ₗ[ℂ] Module.End ℂ V := B.constr ℂ (fun i => F (RingOfIntegers.basis E i))
  have hB : ∀ i, B i = canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    simp [B, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  have h1 : ∀ a : 𝓞 E, Φ (canonicalEmbedding E (a : E)) = F a := by
    intro a
    let L₁ : 𝓞 E →ₗ[ℤ] Module.End ℂ V :=
      (Φ.toAddMonoidHom.comp (((canonicalEmbedding E).comp (algebraMap (𝓞 E) E)).toAddMonoidHom)).toIntLinearMap
    let L₂ : 𝓞 E →ₗ[ℤ] Module.End ℂ V := F.toAddMonoidHom.toIntLinearMap
    have : L₁ = L₂ := by
      apply (RingOfIntegers.basis E).ext
      intro i
      change Φ (canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E)) = F _
      rw [← hB]
      simp [Φ]
    exact LinearMap.congr_fun this a
  have h2 : ∀ (a : 𝓞 E) (x : (E →+* ℂ) → ℂ), Φ (canonicalEmbedding E (a : E) * x) = F a * Φ x := by
    intro a x
    have : Φ ∘ₗ LinearMap.mulLeft ℂ (canonicalEmbedding E (a : E)) = LinearMap.mulLeft ℂ (F a) ∘ₗ Φ := by
      apply B.ext
      intro i
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hB, h1, ← map_mul F, ← h1, ← map_mul (canonicalEmbedding E)]
      rfl
    exact LinearMap.congr_fun this x
  refine ⟨fun τ => Φ (Pi.single τ 1) v, fun τ a => ?_, ?_⟩
  · have : canonicalEmbedding E (a : E) * Pi.single τ 1 = τ (a : E) • (Pi.single τ 1 : (E →+* ℂ) → ℂ) := by
      ext σ
      by_cases h : σ = τ
      · subst h; simp [canonicalEmbedding.apply_at]
      · simp [Pi.single_eq_of_ne h]
    rw [← Module.End.mul_apply, ← h2, this, map_smul, LinearMap.smul_apply]
  · rw [← LinearMap.sum_apply, ← map_sum, Finset.univ_sum_single]
    have := h1 1
    have e : Φ 1 = 1 := by simpa using this
    change v = Φ 1 v
    rw [e]
    rfl

theorem conj_eq_neg {z : ℂ} {d : ℕ} (h : z ^ 2 = -(d : ℂ)) (hd : 0 < d) : starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : z.re = 0 := by
    have h3 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [this]

abbrev Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) := ⨅ a : 𝓞 E, Module.End.eigenspace (F a) (τ (a : E))

theorem mem_Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (v : Fin g → ℂ) : v ∈ Eig F τ ↔ ∀ a : 𝓞 E, F a v = τ (a : E) • v := by
  simp [Eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem theta_mem {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (Θ : Matrix (Fin g) (Fin g) ℂ) (hΘ : ∀ a, Comm Θ (F a)) (v : Fin g → ℂ) (hv : v ∈ Eig F τ) :
    Θ.mulVec (star v) ∈ Eig F (ComplexEmbedding.conjugate τ) := by
  rw [mem_Eig] at hv ⊢
  intro a
  rw [hΘ a v, hv, star_smul, Matrix.mulVec_smul, ComplexEmbedding.conjugate_coe_eq]
  rfl

theorem finrank_symm_comm_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ))
    (hρ : ρ₀ ^ 2 = -(H.d : ℂ)) (_hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hdim : ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q)
    (hS : ∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) :
    Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  classical
  have hd : 0 < H.d := H.d_prime.pos
  have hρ0 : ρ₀ ≠ 0 := by
    intro h
    rw [h] at hρ
    have : (H.d : ℂ) = 0 := by simpa using hρ
    exact hd.ne' (by exact_mod_cast this)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    intro τ
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    simpa using this
  have hconj : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ (H.rt : E) = - τ (H.rt : E) := by
    intro τ
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg (hsq τ) hd
  have hne : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) ≠ ρ₀ := by
    intro τ h h'
    rw [hconj, h] at h'
    apply hρ0
    linear_combination (-1/2 : ℂ) * h'
  have heq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) = ρ₀ := by
    intro τ h
    rw [hconj]
    have : τ (H.rt : E) ^ 2 = ρ₀ ^ 2 := by rw [hsq, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]
  have hdim' : ∀ τ : E →+* ℂ, Module.finrank ℂ (Eig F τ) = if τ (H.rt : E) = ρ₀ then p else q :=
    fun τ => hdim (τ.comp (algebraMap (𝓞 E) E))
  let T := {τ : E →+* ℂ // τ (H.rt : E) = ρ₀}
  have hcard : Fintype.card T ≤ Module.finrank ℚ E / 2 := by
    have h1 : Fintype.card T ≤ Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = ρ₀} := by
      refine Fintype.card_le_of_injective
        (fun τ => ⟨ComplexEmbedding.conjugate τ.1, hne τ.1 τ.2⟩) ?_
      intro σ τ h
      have h2 : ComplexEmbedding.conjugate σ.1 = ComplexEmbedding.conjugate τ.1 := congrArg Subtype.val h
      exact Subtype.ext (star_injective h2)
    rw [Fintype.card_subtype_compl, NumberField.Embeddings.card] at h1
    have h3 : Fintype.card T ≤ Fintype.card (E →+* ℂ) := Fintype.card_subtype_le _
    rw [NumberField.Embeddings.card] at h3
    change Fintype.card T ≤ _ - Fintype.card T at h1
    omega
  have hp : ∀ τ : T, Module.finrank ℂ (Eig F τ.1) = p := fun τ => by rw [hdim', if_pos τ.2]
  have hq : ∀ τ : T, Module.finrank ℂ (Eig F (ComplexEmbedding.conjugate τ.1)) = q :=
    fun τ => by rw [hdim', if_neg (hne τ.1 τ.2)]
  let b : ∀ τ : T, Module.Basis (Fin p) ℂ (Eig F τ.1) := fun τ => Module.finBasisOfFinrankEq ℂ _ (hp τ)
  let Ψ : S →ₗ[ℂ] (∀ τ : T, Fin p → Eig F (ComplexEmbedding.conjugate τ.1)) :=
    { toFun := fun Θ τ i => ⟨Θ.1.mulVec (star (b τ i : Fin g → ℂ)), theta_mem F τ.1 Θ.1 (hS Θ.1 Θ.2).2 _ (b τ i).2⟩
      map_add' := fun Θ Θ' => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.add_mulVec]
      map_smul' := fun c Θ => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro Θ hΘ
    obtain ⟨hs, hc⟩ := hS Θ.1 Θ.2
    have k1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ hτ v hv
      have hb : ∀ i, Θ.1.mulVec (star (b ⟨τ, hτ⟩ i : Fin g → ℂ)) = 0 := fun i =>
        congrArg Subtype.val (congrFun (congrFun hΘ ⟨τ, hτ⟩) i)
      have e := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨v, hv⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
      rw [← e, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [star_smul, Matrix.mulVec_smul, hb, smul_zero]
    have k2 : ∀ τ : E →+* ℂ, ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ v hv
      by_cases hτ : τ (H.rt : E) = ρ₀
      · exact k1 τ hτ v hv
      · by_contra h0
        have h1 := hpos _ h0
        rw [hs v, k1 _ (heq τ hτ) _ (theta_mem F τ Θ.1 hc v hv)] at h1
        simp [hermForm] at h1
    have k3 : ∀ v : Fin g → ℂ, Θ.1.mulVec (star v) = 0 := by
      intro v
      obtain ⟨w, hw, rfl⟩ := exists_sum_eigen F v
      rw [star_sum, Matrix.mulVec_sum]
      exact Finset.sum_eq_zero fun τ _ => k2 τ _ ((mem_Eig F τ _).2 (hw τ))
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := k3 (star v)
    rw [star_star] at this
    simpa using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at hle
  simp only [Module.finrank_pi_fintype, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  calc Module.finrank ℂ S ≤ Fintype.card T * (p * q) := hle
    _ ≤ Module.finrank ℚ E / 2 * (p * q) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

end GlobalTheory.KS.DimPEL
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.finrank_symm_antilinear_comm_CM_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ)), ρ₀ ^ 2 = -(H.d : ℂ) → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q) → (∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) → Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  atlas_forward_decl GlobalTheory.KS.DimPEL.finrank_symm_comm_le
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.UnifEigenRank

theorem finrank_of_existsUnique {k V : Type} [Field k] [AddCommGroup V] [Module k V] (E : Submodule k V) {n : ℕ}
    (W : Fin n → V) (hW : ∀ i, W i ∈ E) (h : ∀ z ∈ E, ∃! c : Fin n → k, z = ∑ i, c i • W i) :
    Module.finrank k E = n := by
  let W' : Fin n → E := fun i => ⟨W i, hW i⟩
  have hc : ∀ c : Fin n → k, ((Fintype.linearCombination k W' c : E) : V) = ∑ i, c i • W i := fun c => by
    simp [Fintype.linearCombination_apply, W']
  have hb : Function.Bijective (Fintype.linearCombination k W') := by
    refine (Function.bijective_iff_existsUnique _).2 fun z => ?_
    refine (existsUnique_congr fun c => ?_).1 (h z z.2)
    rw [Subtype.ext_iff, hc, eq_comm]
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]

end GlobalTheory.UnifEigenRank

open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD isTan_iff isLieComb_iff isTan_scale) in

theorem GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  intro P₀ u Hm χ hu O _ act F hF τ n hn
  have := act.hom
  let j : epsPt (𝟙 (Sp ℂ)) ≅ epsR ℂ := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp ℂ)) ⟶ P₀.A) ≃* (epsR ℂ ⟶ P₀.A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl P₀.A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have one : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ P₀.A).left = η[P₀.A].left := Category.id_comp _
  obtain ⟨v, hv, hb⟩ := LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ)
    (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (Q := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl))
    (fun c u v => by rw [he, he]; rfl) n hn
  have key : ∀ (z : Fin P₀.g → ℂ) (w : epsR ℂ ⟶ P₀.A), IsTangent w → u.IsDiff z w →
      ((∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w) ↔
        z ∈ ⨅ a, Module.End.eigenspace (F a) (τ a)) := by
    intro z w hw hd
    rw [Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [Module.End.mem_eigenspace_iff]
    have h1 : u.IsDiff (F a z) (w ≫ act.act a) :=
      isDiff_comp u (act.act a) (LinearMap.toContinuousLinearMap (F a)) (hF a) hw hd
    have h2 := isDiff_smul u ((isTan_iff _).2 hw) hd (τ a)
    have t1 := isTangent_comp (act.act a) hw
    have t2 := (isTan_iff _).1 (isTan_scale (τ a) ((isTan_iff _).2 hw))
    constructor
    · intro h
      exact (hu.tan₁ _ t1).unique h1 (by rw [h]; exact h2)
    · intro h
      rw [h] at h1
      exact (hu.tan₂ _).unique ⟨t1, h1⟩ ⟨t2, h2⟩
  choose W hW using fun i => (hu.tan₁ (v i) (hv i).1).exists
  have ht : ∀ i, Chart.IsTan (R := ℂ) (G := P₀.A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin n → ℂ, IsTangent (prodPts (R := ℂ) (G := P₀.A) c v) ∧
      u.IsDiff (∑ i, c i • W i) (prodPts (R := ℂ) (G := P₀.A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • W i) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hW i) (c i))
    exact ⟨(isTan_iff _).1 a, b⟩
  refine UnifEigenRank.finrank_of_existsUnique _ W (fun i => (key _ _ (hv i).1 (hW i)).1 (hv i).2) fun z hz => ?_
  obtain ⟨w, hw, hd⟩ := (hu.tan₂ z).exists
  refine (existsUnique_congr fun c => ?_).1 (hb w ⟨hw, (key _ _ hw hd).2 hz⟩)
  refine Iff.trans (isLieComb_iff c v w) ⟨fun h => ?_, fun h => ?_⟩
  · exact (hu.tan₁ _ hw).unique hd (by rw [h]; exact (hp c).2)
  · rw [h] at hd
    exact (hu.tan₂ _).unique ⟨hw, hd⟩ (hp c)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  atlas_forward_decl GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTan

theorem finrank_derivation_le : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  intro l1 l2 _ hu E _ _ _ H D g J _ a w w' bas _ _ _ _ _ N' o _ b ρ R _ _ _ _ _ t τ hρ hP _ hun
  obtain ⟨t₀, m, u, Hm, χ, κ, hG, ⟨hm, -⟩, hκ, hD⟩ := GlobalTheory.T.tangent_injects_symmetric_antilinear_commuting l1 l2 hu o g (N' ^ 2) J b R t hun
  have hx : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨act, act₀, hc, hdet⟩ := GlobalTheory.FibreAct.exists_fibre_act E H D g (N' ^ 2) J a bas o b ρ _ _ t τ _
    (algebraMap o ℂ) t₀.A m hP hx hm
  obtain ⟨F, hF⟩ := (GlobalTheory.KS.exists_linear_lift_action t₀.pol u Hm χ hG).2 (𝓞 E) act₀
  have hle := GlobalTheory.T.finrank_symm_antilinear_comm_CM_le E H t₀.pol.g D.p D.q (algebraMap o ℂ ρ) Hm F (LinearMap.range κ)
    (by rw [← map_pow, hρ]; simp) hG.ah.1 hG.ah.2.1
    (fun σ => by
      split_ifs with h
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).1 h)
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).2 h))
    (by
      rintro _ ⟨d, rfl⟩
      exact ⟨(hD d).1, fun c => (hD d).2 (act.act c) (act₀.act c) (F c) (hc c) (hF c)⟩)
  rw [LinearMap.finrank_range_of_inj hκ] at hle
  exact hle

end GlobalTheory.PelTan
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  atlas_forward_decl GlobalTheory.PelTan.finrank_derivation_le
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem ThetaFam.unram_of_mono {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) {S : Scheme.{0}} (x : S ⟶ F.MM) [Mono x]
    {s : S ⟶ Sp o} (hs : x ≫ F.s = s) (t : TObj g (N' ^ 2) J b s) (ht : TMap t F.univ x) (K : Type) [Field K]
    (y : Sp (DualNumber K) ⟶ S) (t' : TObj g (N' ^ 2) J b (y ≫ s)) (hy : y ≫ s = constPt y ≫ s)
    (h₁ : TMap t' t y) (h₂ : TMap t' t (constPt y)) : y = constPt y := by
  subst hs
  have hc : constPt (y ≫ x) = constPt y ≫ x := by simp [constPt]
  rw [← cancel_mono x, ← hc]
  have key : ∀ (s' : Sp (DualNumber K) ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s'), s' = (y ≫ x) ≫ F.s →
      TMap t' F.univ (y ≫ x) → TMap t' F.univ (constPt (y ≫ x)) → y ≫ x = constPt (y ≫ x) := by
    rintro _ t' rfl h h'
    exact F.unram K (y ≫ x) t' (by rw [hc, Category.assoc, Category.assoc, hy]) h h'
  refine key _ t' (Category.assoc _ _ _).symm ?_ ?_
  · exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x y ht).1 h₁
  · rw [hc]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x (constPt y) ht).1 h₂

theorem exists_thetaFam_isPEL_smooth : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 hcrit hgen hU E _ _ _ H D g J _ a w w' bas hD hbas hw hw' ha n hn hodd
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha
  obtain ⟨j₁, hj₁⟩ := hcl n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.nonempty_thetaObject_family_open_closure h1 h2 hcrit g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em ρ hρ hb => ?_⟩
  have hgood := hj₁ j (le_of_max_le_left hj) _ rfl o b em ρ hρ
  obtain ⟨F⟩ := hj₂ j (le_of_max_le_right hj) o b em _ _ hb hgood
  obtain ⟨τ, hτ⟩ := GlobalTheory.thetaFam_isPEL h1 h2 hgen E H D g J a w w' bas hD hbas hw hw' ha n _ o b em ρ hρ hb F
  refine ⟨F, τ, hτ, ThetaFam.smooth_genericFibre h1 h2 g n _ J Mat κ w w' o b em _ _ F hb hgood ?_⟩
  intro R _ _ _ _ _ x hx hs hem
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ F.s _ x F.univ hs
  obtain ⟨τ', hτ'⟩ := GlobalTheory.PELPull.isPEL_pull E H D g _ J a bas o b ρ _ _ F.s _ x F.univ t τ hs ht hτ
  have hρ2 : ρ ^ 2 = -(H.d : o) := hb.2.2 (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hft : Algebra.FiniteType o R := by
    have := ((GlobalTheory.isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB F.s).1 F.qproj).1
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := hs ▸ inferInstance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h)
  exact GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha _ o b ρ R t τ' hρ2 hτ' hft
    (fun y t' hy h₁ h₂ => F.unram_of_mono x hs t ht ℂ y t' hy h₁ h₂)

end GlobalTheory.ZM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  atlas_forward_decl GlobalTheory.ZM.exists_thetaFam_isPEL_smooth
end
