import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
import Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsEigenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointMemClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.GenericCentre

theorem trdegGe_of_le_trdeg {k L M : Type} [Field k] [Field L] [Field M] [Algebra k L] (g : L →+* M) {d : ℕ}
    (hd : (d : Cardinal) ≤ Algebra.trdeg k L) : TrdegGe M d := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hc : Cardinal.mk (Fin d) ≤ Cardinal.mk s := by
    rw [hs.cardinalMk_eq_trdeg]; simpa using hd
  obtain ⟨e⟩ := hc
  have h1 : AlgebraicIndependent k (((↑) : s → L) ∘ e) := hs.1.comp e e.injective
  let _ : Algebra k M := (g.comp (algebraMap k L)).toAlgebra
  have h2 : AlgebraicIndependent k (g ∘ (((↑) : s → L) ∘ e)) :=
    h1.ringHom_of_comp_eq (RingHom.id k) g Function.surjective_id g.injective rfl
  let e' := (algebraMap k M).rangeRestrictFieldEquiv
  let j : (⊥ : Subfield M) →+* k := e'.symm.toRingHom.comp (Subfield.inclusion bot_le)
  refine ⟨_, AlgebraicIndependent.of_ringHom_of_comp_eq j (RingHom.id M) h2 j.injective ?_⟩
  ext z
  exact congrArg Subtype.val (e'.apply_symm_apply (Subfield.inclusion bot_le z))

theorem exists_cdvr_centred_generic (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (A : Type) [CommRing A] [Algebra O A] [Algebra.FiniteType O A] (K : Type) [Field K] [Algebra A K] [Algebra O K]
    [IsScalarTower O A K] (hinj : Function.Injective (algebraMap O K))
    (hfrac : ∀ x : K, ∃ a b : A, algebraMap A K b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a)
    (p : Ideal A) (hp : p.IsPrime) (hker : RingHom.ker (algebraMap A K) ≤ p)
    (hm : (maximalIdeal O).map (algebraMap O A) ≤ p) (d : ℕ) (hd : (d : Cardinal) ≤ Algebra.trdeg O K) :
    ∃ (T : CDVR) (f : A →+* T.V) (ψ : K →+* T.Fr),
      (algebraMap T.V T.Fr).comp f = ψ.comp (algebraMap A K) ∧ IsLocalHom (f.comp (algebraMap O A)) ∧
      TrdegGe ((maximalIdeal T.V).comap f).ResidueField d := by
  let P := RingHom.ker (algebraMap A K)
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let B := A ⧸ P
  let _ : Algebra B K := (RingHom.kerLift (algebraMap A K)).toAlgebra
  have hBK : Function.Injective (algebraMap B K) := RingHom.kerLift_injective _
  have hmk : ∀ a : A, algebraMap B K (Ideal.Quotient.mk P a) = algebraMap A K a := fun _ => rfl
  have : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsScalarTower.algebraMap_apply O A K x).trans (hmk _).symm
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBK
  have hOB : Function.Injective (algebraMap O B) := by
    refine Function.Injective.of_comp (f := algebraMap B K) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hinj
  have : FaithfulSMul O B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hOB
  have : IsFractionRing B K := by
    refine IsFractionRing.of_field B K fun x => ?_
    obtain ⟨a, b, hb, h⟩ := hfrac x
    exact ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P b, by rw [hmk, hmk, ← h, mul_div_cancel_right₀ _ hb]⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  have hp' : (p.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hker)
  have hle : (maximalIdeal O).map (algebraMap O B) ≤ p.map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hm (Ideal.mem_map_of_mem _ hx))
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  have hqp : q.IsPrime := hq.1.1
  have hlo := GlobalTheory.liesOver_maximalIdeal_of_mem_minimalPrimes O hq
  have hq0 : (⊥ : Ideal B) < q := by
    rw [bot_lt_iff_ne_bot]
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field O
    rw [hlo.over]
    exact Ideal.comap_bot_of_injective _ hOB
  obtain ⟨V, _, _, _, hc, φ, hφ0, hφ⟩ := GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal B) q hq0
  have hφi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr hφ0
  have h0 : CharZero V := charZero_of_injective_ringHom (f := φ.comp (algebraMap O B)) (hφi.comp hOB)
  let T : CDVR := @CDVR.mk V _ _ _ hc h0
  let f : A →+* V := φ.comp (Ideal.Quotient.mk P)
  have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V _).comp hφi
  refine ⟨T, f, IsFractionRing.lift (A := B) (K := K) hg, ?_, ?_, ?_⟩
  · ext a
    exact (IsFractionRing.lift_algebraMap (K := K) hg (Ideal.Quotient.mk P a)).symm
  · refine ⟨fun x hx => ?_⟩
    by_contra hn
    have h1 : algebraMap O B x ∈ q := hq.1.2 (Ideal.mem_map_of_mem _ hn)
    rw [← hφ] at h1
    exact h1 hx
  · have := GlobalTheory.isLocalHom_algebraMap_localization_of_liesOver O q
    have h1 := GlobalTheory.trdeg_residueField_eq_of_mem_minimalPrimes O (ResidueField O) residue_surjective q hq
    have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top O B K, ← h1] at hd
    let Q : Ideal A := (maximalIdeal V).comap f
    have hQ : ∀ a, a ∈ Q ↔ Ideal.Quotient.mk P a ∈ q := fun a => by rw [← hφ]; rfl
    let g : B →+* Q.ResidueField := Ideal.Quotient.lift P (algebraMap A _) fun a ha => by
      rw [Ideal.algebraMap_residueField_eq_zero, hQ, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact q.zero_mem
    have hgq : ∀ b, g b = 0 ↔ b ∈ q := fun b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← hQ]
      exact Ideal.algebraMap_residueField_eq_zero
    exact trdegGe_of_le_trdeg (Ideal.ResidueField.lift q g (fun b hb => (hgq b).mpr hb)
      fun b hb => Ne.isUnit fun h => hb ((hgq b).mp h)) hd

end GlobalTheory.GenericCentre
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_prime_dominance : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (A : Type) [CommRing A] [Algebra O A] [Algebra.FiniteType O A] (K : Type) [Field K] [Algebra A K] [Algebra O K] [IsScalarTower O A K], Function.Injective (algebraMap O K) → (∀ x : K, ∃ a b : A, algebraMap A K b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a) → ∀ p : Ideal A, p.IsPrime → RingHom.ker (algebraMap A K) ≤ p → (maximalIdeal O).map (algebraMap O A) ≤ p → ∀ d : ℕ, (d : Cardinal) ≤ Algebra.trdeg O K → ∃ (T : CDVR) (f : A →+* T.V) (ψ : K →+* T.Fr), (algebraMap T.V T.Fr).comp f = ψ.comp (algebraMap A K) ∧ IsLocalHom (f.comp (algebraMap O A)) ∧ TrdegGe ((maximalIdeal T.V).comap f).ResidueField d := by
  atlas_forward_decl GlobalTheory.GenericCentre.exists_cdvr_centred_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem trdegGe_map_of_ringHom {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ} (h : TrdegGe k n) :
    TrdegGe k' n := by
  obtain ⟨t, ht⟩ := h
  have hm : (⊥ : Subfield k).map φ = ⊥ := Subfield.map_bot φ
  let f : (⊥ : Subfield k) →+* (⊥ : Subfield k') :=
    (φ.comp (⊥ : Subfield k).subtype).codRestrict _ fun x => hm ▸ ⟨x.1, x.2, rfl⟩
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx, e⟩ : y.1 ∈ (⊥ : Subfield k).map φ := hm.symm ▸ y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨φ ∘ t, ht.ringHom_of_comp_eq f φ hf φ.injective (by ext; rfl)⟩

theorem exists_specializes_over_closedPoint (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0})
    (s : X ⟶ Sp O) [IsProper s] (x : X) : ∃ ξ : X, x ⤳ ξ ∧ s ξ = closedPoint O := by
  have h1 : s x ⤳ closedPoint O := IsLocalRing.specializes_closedPoint _
  obtain ⟨ξ, h2, h3⟩ := s.isClosedMap.specializingMap h1
  exact ⟨ξ, h2, h3⟩

theorem exists_cdvr_centred_trdegGe (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (X : Scheme.{0}) (s : X ⟶ Sp O) [IsProper s] (K : Type) [Field K] (g : Sp K ⟶ X) [IsPreimmersion g]
    (a : O →+* K) (ha : Function.Injective a) (hg : g ≫ s = spMap a) (d : ℕ)
    (hd : letI := a.toAlgebra; (d : Cardinal) ≤ Algebra.trdeg O K) :
    ∃ (T : CDVR) (yt : Sp T.V ⟶ X) (ψ : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b ∧ yt ≫ s = spMap b ∧
      spMap (algebraMap T.V T.Fr) ≫ yt = spMap ψ ≫ g ∧ TrdegGe (X.residueField (yt (closedPoint T.V))) d := by
  obtain ⟨ξ, hξ, hs⟩ := exists_specializes_over_closedPoint O X s (g (closedPoint K))
  obtain ⟨A, _, j, _, p, rfl⟩ : ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X) (_ : IsOpenImmersion j)
      (p : PrimeSpectrum A), j p = ξ := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
    have hU : IsAffineOpen U := hU
    have : ξ ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    obtain ⟨p, hp⟩ := this
    exact ⟨Γ(X, U), inferInstance, hU.fromSpec, inferInstanceAs (IsOpenImmersion hU.fromSpec), p, hp⟩
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (closedPoint K)]
    exact hξ.mem_open j.isOpenEmbedding.isOpen_range ⟨p, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* K, spMap φ ≫ j = g :=
    ⟨(Spec.preimage (IsOpenImmersion.lift j g hr)).hom, by
      rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨α, hα⟩ : ∃ α : O →+* A, spMap α = j ≫ s :=
    ⟨(Spec.preimage (j ≫ s)).hom, by rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hcomp : φ.comp α = a := by
    have : spMap (φ.comp α) = spMap a := by
      rw [← hg, ← hφ, Category.assoc, ← hα, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  let _ := a.toAlgebra
  let _ := φ.toAlgebra
  let _ := α.toAlgebra
  have : IsScalarTower O A K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hft : Algebra.FiniteType O A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom α)).mp
      (show LocallyOfFiniteType (spMap α) from hα ▸ inferInstance)
  have hpre : IsPreimmersion (spMap φ) := by
    have : IsPreimmersion (spMap φ ≫ j) := hφ ▸ inferInstance
    exact IsPreimmersion.of_comp _ j
  have hst : φ.SurjectiveOnStalks := ((IsPreimmersion.SpecMap_iff (CommRingCat.ofHom φ)).1 hpre).2
  have hfr : ∀ x : K, ∃ u v : A, algebraMap A K v ≠ 0 ∧ x * algebraMap A K v = algebraMap A K u := fun x => by
    obtain ⟨u, v, c, hc, hv, e⟩ := RingHom.surjectiveOnStalks_iff_forall_ideal.1 hst ⊥ bot_ne_top x
    refine ⟨u, v, hv, mul_left_cancel₀ (show c ≠ 0 from hc) ?_⟩
    rw [mul_comm x, ← mul_assoc]
    exact e
  have hker : RingHom.ker (algebraMap A K) ≤ p.asIdeal := by
    have h1 : j (spMap φ (closedPoint K)) ⤳ j p := by
      rw [← hφ] at hξ
      exact hξ
    have h2 := (PrimeSpectrum.le_iff_specializes (PrimeSpectrum.comap φ (closedPoint K)) p).mpr
      (j.isOpenEmbedding.isInducing.specializes_iff.mp h1)
    exact fun x hx => h2 (show φ x ∈ (closedPoint K).asIdeal from (show φ x = 0 from hx) ▸ Ideal.zero_mem _)
  have hmax : (maximalIdeal O).map (algebraMap O A) ≤ p.asIdeal := by
    have h1 : (j ≫ s) p = closedPoint O := hs
    rw [← hα] at h1
    exact Ideal.map_le_iff_le_comap.2 (congrArg PrimeSpectrum.asIdeal h1).ge
  obtain ⟨T, f, ψ, e, hl, ht⟩ := GlobalTheory.T.valuation_ring_prime_dominance O A K ha hfr p.asIdeal p.isPrime hker hmax d hd
  refine ⟨T, spMap f ≫ j, ψ, f.comp α, hl, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hα, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · rw [← hφ, ← Category.assoc, ← Category.assoc, spMap, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  · let q : Sp A := PrimeSpectrum.comap f (closedPoint T.V)
    exact trdegGe_map_of_ringHom (k := q.asIdeal.ResidueField) (k' := X.residueField (j q))
      ((Scheme.Spec.residueFieldIso (.of A) q).inv ≫ inv (j.residueFieldMap q)).hom ht

end GlobalTheory.FactorDepth
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_point_lifting : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (X : Scheme.{0}) (s : X ⟶ Sp O) [IsProper s] (K : Type) [Field K] (g : Sp K ⟶ X) [IsPreimmersion g] (a : O →+* K), Function.Injective a → g ≫ s = spMap a → ∀ d : ℕ, (letI := a.toAlgebra; (d : Cardinal) ≤ Algebra.trdeg O K) → ∃ (T : CDVR) (yt : Sp T.V ⟶ X) (ψ : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b ∧ yt ≫ s = spMap b ∧ spMap (algebraMap T.V T.Fr) ≫ yt = spMap ψ ≫ g ∧ TrdegGe (X.residueField (yt (closedPoint T.V))) d := by
  atlas_forward_decl GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe
end

section
section
open IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.GaussCountable

theorem isDiscreteValuationRing_localization {R : Type} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (p : Ideal R) [p.IsPrime] (g : R) (hgp : Prime g)
    (hg : p = Ideal.span {g}) : IsDiscreteValuationRing (Localization.AtPrime p) := by
  set O := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors p)
  have h1 : Ideal.map (algebraMap R O) p = Ideal.span {algebraMap R O g} := by
    rw [congrArg (Ideal.map (algebraMap R O)) hg, Ideal.map_span, Set.image_singleton]
  have hspan : Ideal.span {algebraMap R O g} = IsLocalRing.maximalIdeal O :=
    h1.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p O)
  have hϖ0 : algebraMap R O g ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hgp.ne_zero
  have hϖ : Prime (algebraMap R O g) :=
    (Ideal.span_singleton_prime hϖ0).mp (by rw [hspan]; infer_instance)
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, hϖ.irreducible, ?_⟩
  intro x hx
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.mk'_surjective p.primeCompl x
  simp only at hxs
  subst hxs
  have ha : a ≠ 0 := by rintro rfl; exact hx (by simp)
  obtain ⟨n, a', hnd, rfl⟩ := WfDvdMonoid.max_power_factor ha hgp.irreducible
  have ha' : a' ∈ p.primeCompl := by
    show a' ∉ p
    rw [hg, Ideal.mem_span_singleton]; exact hnd
  refine ⟨n, ((IsLocalization.AtPrime.isUnit_mk'_iff O p a' s).mpr ha').unit, ?_⟩
  rw [IsUnit.unit_spec, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul]

theorem exists_gaussExtension : ∀ T : CDVR, ∃ (T' : CDVR) (φ : T.V →+* T'.V) (_ : IsLocalHom φ),
    Function.Injective φ ∧ ∃ t : ℕ → ResidueField T'.V,
      (letI := (ResidueField.map φ).toAlgebra; AlgebraicIndependent (ResidueField T.V) t) := by
  intro T
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  let A := MvPolynomial ℕ T.V
  have hp : Prime (MvPolynomial.C ϖ : A) := (MvPolynomial.prime_C_iff _).2 hϖ.prime
  let P : Ideal A := Ideal.span {MvPolynomial.C ϖ}
  haveI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    isDiscreteValuationRing_localization P _ hp rfl
  obtain ⟨O, _, _, _, _, ψ, hψ, _⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating
    (Localization.AtPrime P) (IsDiscreteValuationRing.not_isField _)
  let g : A →+* O := ψ.comp (algebraMap A (Localization.AtPrime P))
  have hg : Function.Injective g :=
    hψ.comp (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P))
  have hmem : ∀ a : A, residue O (g a) = 0 ↔ MvPolynomial.map (residue T.V) a = 0 := by
    intro a
    rw [residue_eq_zero_iff, ← RingHom.mem_ker, MvPolynomial.ker_map, ker_residue,
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (ψ (algebraMap A (Localization.AtPrime P) a)) ↔ a ∈ P
    rw [isUnit_map_iff, IsLocalization.AtPrime.isUnit_to_map_iff _ P]
    exact not_not
  let φ : T.V →+* O := g.comp MvPolynomial.C
  have hφ : Function.Injective φ := hg.comp (MvPolynomial.C_injective _ _)
  haveI : CharZero O := charZero_of_injective_ringHom hφ
  haveI hl : IsLocalHom φ := ⟨fun a ha => by
    by_contra hn
    have h1 : residue T.V a = 0 := (residue_eq_zero_iff _).2 hn
    have h2 := (hmem (MvPolynomial.C a)).2 (by rw [MvPolynomial.map_C, h1, map_zero])
    exact ((residue_eq_zero_iff _).1 h2) ha⟩
  refine ⟨⟨O⟩, φ, hl, hφ, fun i => residue O (g (MvPolynomial.X i)), ?_⟩
  letI := (ResidueField.map φ).toAlgebra
  change AlgebraicIndependent (ResidueField T.V) (fun i => residue O (g (MvPolynomial.X i)))
  rw [algebraicIndependent_iff]
  intro q hq
  obtain ⟨a, rfl⟩ := MvPolynomial.map_surjective (σ := ℕ) (residue T.V) residue_surjective q
  rw [← hmem, ← hq]
  have : (residue O).comp g = ((MvPolynomial.aeval (R := ResidueField T.V)
      (fun i => residue O (g (MvPolynomial.X i)))).toRingHom).comp
      (MvPolynomial.map (residue T.V)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
      rfl
    · intro i
      simp
  exact congr($this a)

end GlobalTheory.GaussCountable
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_residue_transcendence : ∀ T : CDVR, ∃ (T' : CDVR) (φ : T.V →+* T'.V) (_ : IsLocalHom φ), Function.Injective φ ∧ ∃ t : ℕ → ResidueField T'.V, (letI := (ResidueField.map φ).toAlgebra; AlgebraicIndependent (ResidueField T.V) t) := by
  atlas_forward_decl GlobalTheory.GaussCountable.exists_gaussExtension
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.PlaceLocalRing

section

variable {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {O : Type} [CommRing O] {β : O →+* K}

theorem exists_unit (hinj : Function.Injective β) (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {x : K} (hx : la.valuation K x = 1) : ∃ u : Oˣ, β u = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨a, ha⟩ := (hr x).2 hx.le
  obtain ⟨c, hc⟩ := (hr x⁻¹).2 (by rw [map_inv₀, hx, inv_one])
  have : IsUnit a := IsUnit.of_mul_eq_one c (hinj (by rw [map_mul, ha, hc, mul_inv_cancel₀ hx0, map_one]))
  exact ⟨this.unit, ha⟩

theorem exists_unit_mul_zpow (hinj : Function.Injective β) (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {p : K} (hp : la.valuation K p = WithZero.exp (-1 : ℤ)) {x : K} (hx : x ≠ 0) :
    ∃ u : Oˣ, x = β u * p ^ vLa la x := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hv : la.valuation K x ≠ 0 := by simpa using hx
  obtain ⟨u, hu⟩ := exists_unit hinj hr (x := x * p ^ (-vLa la x)) (by
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul, ← WithZero.exp_log hv, ← WithZero.exp_add]
    simp [vLa])
  refine ⟨u, ?_⟩
  rw [hu, mul_assoc, ← zpow_add₀ hp0]
  simp

theorem vLa_nonneg (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) {a : O} (ha : β a ≠ 0) :
    0 ≤ vLa la (β a) := by
  have hv : la.valuation K (β a) ≠ 0 := by simpa using ha
  have h := (hr _).1 ⟨a, rfl⟩
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  simp only [vLa]
  omega

theorem irreducible_of_valuation (hinj : Function.Injective β)
    (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {π : O} (hp : la.valuation K (β π) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hle : ∀ a : O, la.valuation K (β a) ≤ 1 := fun a => (hr _).1 ⟨a, rfl⟩
  have hun : ∀ a : O, la.valuation K (β a) = 1 → IsUnit a := fun a ha => by
    obtain ⟨u, hu⟩ := exists_unit hinj hr ha
    exact hinj hu ▸ u.isUnit
  refine ⟨fun h => ?_, fun a c h => ?_⟩
  · obtain ⟨c, hc⟩ := h.exists_right_inv
    have h1 : la.valuation K (β π) * la.valuation K (β c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
      calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
        _ ≤ la.valuation K (β π) * 1 := by gcongr; exact hle c
        _ = _ := by rw [mul_one, hp]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    omega
  · rw [h, map_mul, map_mul] at hp
    have h0 := mul_ne_zero_iff.1 (hp.trans_ne WithZero.exp_ne_zero)
    have ha := hle a
    have hc := hle c
    rw [← WithZero.exp_log h0.1, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [← WithZero.exp_log h0.2, ← WithZero.exp_zero, WithZero.exp_le_exp] at hc
    rw [← WithZero.exp_log h0.1, ← WithZero.exp_log h0.2, ← WithZero.exp_add, WithZero.exp_inj] at hp
    by_cases h1 : WithZero.log (la.valuation K (β a)) = 0
    · exact Or.inl (hun a (by rw [← WithZero.exp_log h0.1, h1, WithZero.exp_zero]))
    · exact Or.inr (hun c (by
        rw [← WithZero.exp_log h0.2, show WithZero.log (la.valuation K (β c)) = 0 by omega, WithZero.exp_zero]))

end

theorem dvr_and_overLa : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (O : Type) [CommRing O] (β : O →+* K), Function.Injective β → (∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) → ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), (letI := β.toAlgebra; IsFractionRing O K) ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b → (algebraMap T.V T.Fr).comp b = io.comp β → ∃ e : ℕ, OverLa la T.V io e := by
  intro K _ _ la O _ β hinj hr
  obtain ⟨p, hp⟩ := la.valuation_exists_uniformizer K
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨π, rfl⟩ := (hr p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hπ := irreducible_of_valuation hinj hr hp
  have hdom : IsDomain O := hinj.isDomain β
  have hdvr : IsDiscreteValuationRing O :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hπ, fun {x} hx => by
      have hx' : β x ≠ 0 := (map_ne_zero_iff β hinj).2 hx
      obtain ⟨u, hu⟩ := exists_unit_mul_zpow hinj hr hp hx'
      have h0 := vLa_nonneg hr hx'
      refine ⟨(vLa la (β x)).toNat, u, hinj ?_⟩
      rw [map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg h0, mul_comm, ← hu]⟩
  refine ⟨hdom, hdvr, ?_, ?_⟩
  · letI := β.toAlgebra
    haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).2 hinj
    refine IsFractionRing.of_field O K fun x => ?_
    rcases le_total (la.valuation K x) 1 with h | h
    · obtain ⟨a, ha⟩ := (hr x).2 h
      exact ⟨a, 1, by rw [map_one, div_one]; exact ha.symm⟩
    · obtain ⟨a, ha⟩ := (hr x⁻¹).2 (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h)
      exact ⟨1, a, by rw [map_one, one_div]; change x = (β a)⁻¹; rw [ha, inv_inv]⟩
  · intro T io b hb hc
    have hc' : ∀ a, io (β a) = algebraMap T.V T.Fr (b a) := fun a => (RingHom.congr_fun hc a).symm
    have hlt : valV T.V (io (β π)) < 1 := by
      rw [hc']
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 fun h => hπ.not_isUnit (isUnit_of_map_unit b _ h)
    have hne : valV T.V (io (β π)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hp0)
    have hpos : 0 < vV T.V (io (β π)) := by
      rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      simp only [vV]
      omega
    refine ⟨(vV T.V (io (β π))).toNat, by omega, fun a => ?_⟩
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    obtain ⟨u, hu⟩ := exists_unit_mul_zpow hinj hr hp ha
    have h1 : valV T.V (io (β u)) = 1 := by
      rw [hc']
      refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.mp fun h => ?_)
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h (u.isUnit.map b)
    rw [Int.toNat_of_nonneg hpos.le]
    generalize vLa la a = n at hu
    rw [hu]
    simp only [vV, map_mul, map_zpow₀, h1, one_mul, WithZero.log_zpow]
    simp [mul_comm]

end GlobalTheory.PlaceLocalRing
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_bound_over_dvr : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (O : Type) [CommRing O] (β : O →+* K), Function.Injective β → (∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) → ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), (letI := β.toAlgebra; IsFractionRing O K) ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b → (algebraMap T.V T.Fr).comp b = io.comp β → ∃ e : ℕ, OverLa la T.V io e := by
  atlas_forward_decl GlobalTheory.PlaceLocalRing.dvr_and_overLa
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.GenericCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_residue_factor {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (ξ : X) (q : Sp k) (h : x q = ξ) :
    ∃ ι : X.residueField ξ →+* k, spMap ι ≫ X.fromSpecResidueField ξ = x := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have hp : p = ξ := by
    rw [← h, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  subst hp
  exact ⟨φ.hom, rfl⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in

theorem isCombAtG_map {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (a i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · have h := map_list_prod (Formalism.L2.Pj.preHom (G := t.G) δ) (List.ofFn u)
    rw [List.map_ofFn] at h
    exact congrArg (fun g => g.left) h.symm

attribute [local instance] Over.cartesianMonoidalCategory in

theorem exists_comb {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (a : Fin m → S) :
    ∃ w, IsCombAtG t x v a w ∧ IsTanAtG t x w :=
  ⟨_, (isCombAtG_iff t x (fun j => ovT (hv j)) a _).2 rfl,
    isTanAtG_of _ (combT_tan _ _ (fun j => smT_zero_ovT (hv j)) a)⟩

attribute [local instance] Over.cartesianMonoidalCategory in

theorem comb_unique {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hv j)) a _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hv j)) a _).1 h')

theorem exists_frac_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (h : Function.Injective φ) : ∃ φF : FractionRing A →+* FractionRing B,
      φF.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp φ := by
  have hi : Function.Injective ((algebraMap B (FractionRing B)).comp φ) := (IsFractionRing.injective B _).comp h
  refine ⟨IsFractionRing.lift (K := FractionRing A) hi, RingHom.ext fun r => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_centre (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c β) (hB : PointsOfFlagModel.BaseAt la β) (Z : Comp Xo c) :
    ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
      (ξ : Y.X) (ι : Y.X.residueField ξ →+* ResidueField T.V),
      z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt ∧ z ≫ pullback.snd _ _ = spMap io ∧
      (∀ q, z q ∈ (Z : Set (Xo.XF c))) ∧ spMap ι ≫ Y.X.fromSpecResidueField ξ = spMap (residue T.V) ≫ yt ∧
      TrdegGe (Y.X.residueField ξ) Dw.dim ∧
      ∃ s : ℕ → ResidueField T.V, letI := ι.toAlgebra; AlgebraicIndependent (Y.X.residueField ξ) s := by
  obtain ⟨_, _, hfr, hover⟩ := GlobalTheory.T.ramification_bound_over_dvr c.F la O β hB.1 hB.2
  letI : Algebra O c.F := β.toAlgebra
  have : CharZero O := RingHom.charZero β
  have : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  let g : Sp (kap Z) ⟶ Xo.XF c := genSp Z
  have : IsPreimmersion g := by unfold g genSp; infer_instance
  have hg : g ≫ pullback.snd _ _ = spMap (algebraMap c.F (kap Z)) := (Spec.map_preimage _).symm
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  let a : O →+* kap Z := (algebraMap c.F (kap Z)).comp β
  have htr : letI := a.toAlgebra; ((Dw.dim : ℕ) : Cardinal) ≤ Algebra.trdeg O (kap Z) := by
    letI := a.toAlgebra
    have : IsScalarTower O c.F (kap Z) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rw [← trdeg_add_eq O c.F (A := kap Z), kapTrdeg_pf Xo c Z]
    exact le_add_self
  have hga : (g ≫ Y.j) ≫ Y.s = spMap a := by
    rw [Category.assoc, hjs, ← Category.assoc, hg, spMap_comp' β]
  obtain ⟨T₀, yt₀, ψ, b, hb, hs, hgen, hd⟩ := GlobalTheory.T.complete_dvr_point_lifting O Y.X Y.s (kap Z) (g ≫ Y.j) a
    ((algebraMap c.F (kap Z)).injective.comp hB.1) hga Dw.dim htr
  obtain ⟨T, φ, hφ, hinj, s, hs'⟩ := GlobalTheory.T.complete_dvr_residue_transcendence T₀
  obtain ⟨φF, hφF⟩ := exists_frac_map φ hinj
  have hba : (algebraMap T₀.V T₀.Fr).comp b = ψ.comp a := by
    apply spMap_inj
    rw [← spMap_comp' b, ← hs, ← Category.assoc, hgen, Category.assoc, hga, spMap_comp' a]
  obtain ⟨e, he⟩ := hover T ((φF.comp ψ).comp (algebraMap c.F (kap Z))) (φ.comp b) inferInstance (by
    rw [← RingHom.comp_assoc, ← hφF, RingHom.comp_assoc, hba]; rfl)
  obtain ⟨ι₀, hι₀⟩ := exists_residue_factor (spMap (residue T₀.V) ≫ yt₀) (yt₀ (closedPoint T₀.V))
    (closedPoint (ResidueField T₀.V))
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg yt₀ (comap_closedPoint (residue T₀.V))))
  refine ⟨T, _, e, he, spMap φ ≫ yt₀, spMap (φF.comp ψ) ≫ g, _, (ResidueField.map φ).comp ι₀, ?_, ?_, fun q => ?_, ?_,
    hd, s, ?_⟩
  · rw [← spMap_comp', Category.assoc, Category.assoc, ← hgen, ← Category.assoc, ← Category.assoc, spMap_comp',
      spMap_comp', hφF]
  · rw [Category.assoc, hg, spMap_comp']
  · have h1 : (spMap (φF.comp ψ) ≫ g) q = genPt Z :=
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    rw [h1]
    exact ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  · rw [← spMap_comp', Category.assoc, hι₀, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp',
      ResidueField.map_comp_residue]
  · letI := ι₀.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    letI := ((ResidueField.map φ).comp ι₀).toAlgebra
    have : IsScalarTower (Y.X.residueField (yt₀ (closedPoint T₀.V))) (ResidueField T₀.V) (ResidueField T.V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact AlgebraicIndependent.restrictScalars ι₀.injective hs'

end GlobalTheory.GenericCentre
end
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DepthSum

section Core

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace NumberField
  IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem thetaCore_trait :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (yt : Sp V ⟶ Y.X)
      (z : Sp (FractionRing V) ⟶ Xo.XF c), z ≫ Y.j = spMap (algebraMap V (FractionRing V)) ≫ yt →
      ∀ (G : SAB H (Sp V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp (FractionRing V)))
        (m2 : SABMap t' G (spMap (algebraMap V (FractionRing V)))),
        ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : V, ∀ i, σ.f i = constFn G.G.hom _ a * θ.f i) ∧
          (∃ (g : G.G.left) (i : G.PP.L.ι), G.G.hom g = closedPoint V ∧ g ∈ G.G.left.basicOpen (θ.f i)) ∧
          ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L), IsRigIso m2.cm t'.PP G.PP w2 ∧
            (∀ (j : G.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens) (h₁ : W ≤ m2.φ ⁻¹ᵁ G.PP.L.U j)
              (h₂ : W ≤ (G.PP.L.pull m2.φ).U (fun _ => j) ⊓ t'.PP.L.U k),
              (m2.φ.appLE _ _ h₁).hom (θ.f j) =
                resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k)) ∧
            ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := by
  intro E _ _ _ H D l Xo c O _ β Y V _ _ _ yt z hz G m t' m2
  have := G.semi.smooth
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m2
  have cancel : ∀ (p : Sp (FractionRing V) ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p), Nonempty (SABMap t' Y.oF.t z) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m3⟩ := cancel _ hz.symm n
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre GlobalTheory.allSixLaws.2.1.secTwist amplePt Y.oF m3
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaDvr.thetaNZ_of_polAt GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 E H V G
    (GlobalTheory.GoodTrait.polAt_of_point Y m (jK V) z hz)
  obtain ⟨g, k₀, hg₂, hgb⟩ := hθ (closedPoint V)
  have hk₀ : g ∈ G.PP.L.U k₀ := G.G.left.basicOpen_le _ hgb
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (G.G.left.mem_basicOpen _ _ hk₀).1 hgb
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  have down := sec_pull_down ((isGen_iff w2).1 g2) G.PP.isLB t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant m2.φ := IsSchemeTheoreticallyDominant.of_isPullback m2.cart.1.flip
  have : QuasiCompact m2.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) m2.cart.1.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f σ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f τ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn t'.G.hom _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn G.G.hom _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine m2.φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB y
    refine (gs_pull (𝟙 _) m2.φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) m2.φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ m2.φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ m2.φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk, (sec_eq_iff _ _ _ _).1 h₃ k y hk,
      Category.id_comp, m2.cart.1.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : LB.Sec t'.PP.L} {a a' : FractionRing V}, (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      (∀ k, t.f k = constFn t'.G.hom _ a' * u.f k) → ∀ k, s.f k = constFn t'.G.hom _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : LB.Sec t'.PP.L} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      ∀ k, t.f k = constFn t'.G.hom _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : LB.Sec G.PP.L) (r : V), (∀ j, θ.f j = constFn G.G.hom _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit G.G.hom g hg₂ hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀, -⟩ := hb σ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ σ' σ' 0 hσ' hσ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  have gen : ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := fun s' => by
    obtain ⟨a, ha, hu⟩ := hb s'
    refine ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀), fun a' ha' => ?_⟩
    rw [← hu _ (mulc ha' ha₀), mul_inv_cancel_right₀ h₀]
  refine ⟨θ, fun σ => ?_, ⟨g, k₀, hg₂, (G.G.left.mem_basicOpen _ _ hk₀).2 (by rwa [gs_eq _ _ _ hk₀] at un)⟩, w2, σ', ⟨g2, r2⟩,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, gen⟩
  · obtain ⟨σK, hσK⟩ := down σ
    obtain ⟨a, ha, -⟩ := gen σK
    have ex : ∃ r : V, ∀ i, σ.f i = constFn G.G.hom _ r * θ.f i := by
      by_cases h : IsLocalization.IsInteger V a
      · obtain ⟨r, rfl⟩ := h
        exact ⟨r, inj σ θ σK σ' r hσK hσ' ha⟩
      · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
        obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
        obtain ⟨u, rfl⟩ := unit σ r (inj θ σ σ' σK r hσ' hσK (hr ▸ invc hne ha))
        exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
    obtain ⟨r, hr⟩ := ex
    refine ⟨r, hr, fun r' hr' => ?_⟩
    by_contra hne
    have e : cst G.G.hom g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst G.G.hom g (r' - r) * 0 := by
      rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
    exact un.ne_zero (cst_regular G.G.hom g (sub_ne_zero.2 hne) e)
  · rw [gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy, hσ' _ (𝟙 _) y j k (h₁ hy) (h₂ hy).2, gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg₂ (· * ·) ((gs_res (𝟙 _) y h₂ hy _).trans (gs_unit (𝟙 _) y _ (h₂ hy) _)).symm rfl

end Core

section Frame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

set_option maxHeartbeats 400000 in

theorem thetaFrame_trait :
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp T.Fr))
      (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      letI := io.toAlgebra
      ∀ s₀ : LB.Sec (PPx (z ≫ pullback.fst _ _)),
      (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i, s'.f i = scal (z ≫ pullback.fst _ _) a i * s₀.f i) →
      ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx (z ≫ pullback.fst _ _))),
        (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
          σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
        (∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
          (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
          RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
          ∀ g : t'.G.left ⟶ Gx (z ≫ pullback.fst _ _),
            g ≫ (snd (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = m1.φ →
            g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = t'.G.hom →
            ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx (z ≫ pullback.fst _ _)).U (fun _ => j PUnit.unit)),
              s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
        (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i,
          s'.f i = scal (z ≫ pullback.fst _ _) a i * s.f i) ∧
        ∃ a : T.Frˣ, ∀ i, s.f i = scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i := by
  intro T io O _ β Y yt z hz hzs G m t' m1 m2
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ := thetaCore_trait E H Dw l Xo c O β Y T.V yt z hz G m t' m2
  generalize (z ≫ pullback.fst _ _ : Sp T.Fr ⟶ Xo.X) = x at m1 ⊢
  intro s₀ hs₀
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := thf_secUp hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have uniq : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m1.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  have hg0 : g0 ≫ h = 𝟙 _ := uniq g0 g0s g0f
  have h0g : h ≫ g0 = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show h ≫ g0 ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left
      rw [g0f, hh, Category.id_comp]
    · rw [Category.assoc]
      show h ≫ g0 ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left
      rw [g0s, hφ, Category.id_comp]
  let s : LB.Sec (PPx x) := thfPull1 Xo.univ.t.PP.L h hφ s1
  have hsf : ∀ j : Fin 1 → Xo.univ.t.PP.L.ι, s.f j = (h.appLE _ _ (chart_le_pullback_open _ h hφ j)).hom (s1.f (fun _ => j 0)) :=
    fun j => rfl
  let θ2 := thfPull G.PP.L m2.φ θ
  have hI2 : IsoMaps w2 σ' θ2 := fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => by
    have h₁ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ m2.φ ⁻¹ᵁ G.PP.L.U (i PUnit.unit) :=
      inf_le_left.trans (LB.wchart_le G.PP.L _ i PUnit.unit)
    have h₂ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ (G.PP.L.pull m2.φ).U (fun _ => i PUnit.unit) ⊓ t'.PP.L.U k :=
      le_rfl
    have e := congrArg (gs (𝟙 _) y _) (hcl (i PUnit.unit) k _ h₁ h₂)
    refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      (((gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy _).symm.trans e).trans ((gs_mul _ y _ hy _ _).trans ?_)))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_res _ y h₂ hy _).symm ((gs_res _ y _ hy _).trans (gs_res _ y _ hy _).symm)
  have hI1 : IsoMaps w1 σ' s1 := fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => by
    exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  have hgc : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      ∀ (j : PUnit → Xo.univ.t.PP.L.ι) (hj : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ hj).hom (s.f (fun _ => j PUnit.unit)) := fun g e₁ e₂ j hj => fn_ext fun y hy =>
    Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))
  have hgenS : ∀ s'' : LB.Sec (PPx x), ∃! a : T.Fr, ∀ i, s''.f i = scal x a i * s.f i := by
    intro s''
    have le : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr hy
    let σ : ∀ j, Γ(t'.G.left, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j) := fun j => (g0.appLE _ _ (le j)).hom (s''.f (fun _ => j))
    have gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j, m1.φ (r z) ∈ Xo.univ.t.PP.L.U j →
        gs r z _ (σ j) = gs (r ≫ g0) z _ (s''.f (fun _ => j)) := fun Z r z j hz => gs_appLE g0 _ _ (le j) r z hz _
    obtain ⟨τ, hτ⟩ := sec_down hw1 hL hL' σ fun y j j' h₁ h₂ => by
      have m : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j h₁
      have m' : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j') := le j' h₂
      have gg : gm (𝟙 _ ≫ g0) y _ ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) A).left) (fun _ => 1) (𝟙 _ ≫ g0) y _ _ m m').trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, g0s, Category.id_comp])
      exact (gP _ (𝟙 _) y j h₁).trans ((gs_compat s'' (𝟙 _ ≫ g0) y m m').trans
        (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))
    obtain ⟨a, ha, hu⟩ := hgen τ
    refine ⟨a, fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_, fun a' ha' => hu a' ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
      refine fn_ext fun y hy => ?_
      have mφ : m1.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
          (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m1.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)
      obtain ⟨k, hk⟩ := exists_chart hL' ((𝟙 _ ≫ h) y)
      have e1 : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a * gs (𝟙 _ ≫ h) y _ (σ'.f k)) := by
        have c1 : (𝟙 _ ≫ h) ≫ g0 = 𝟙 _ := by rw [Category.id_comp, h0g]
        refine (congrArg (fun q => gs q y _ (s''.f (fun _ => j))) c1).symm.trans ?_
        refine (gP _ (𝟙 _ ≫ h) y j mφ).symm.trans ((hτ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_))
        rw [ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
      have e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w1 (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (σ'.f k) :=
        (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _) y hy _).trans
          (hs1 _ (𝟙 _ ≫ h) y (fun _ => j) k (chart_le_pullback_open _ h hφ _ hy) hk)
      have e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a := by
        rw [show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]
        exact gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a
      exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hL (m1.φ y)
      have c2 : (𝟙 _ ≫ g0) ≫ h = 𝟙 _ := by rw [Category.id_comp, hg0]
      have mg : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j hj
      have e1 := hτ _ (𝟙 _) y j k hj hy
      have e2 : gs (𝟙 _) y _ (σ j) =
          cst (𝟙 _ ≫ t'.G.hom) y a' * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        refine (gP _ (𝟙 _) y j hj).trans ?_
        rw [ha' (fun _ => j), gs_mul _ y _ mg]
        refine congrArg₂ (· * ·) ?_ ?_
        · exact (gs_constFn (fst (Over.mk x) A).left _ _ y mg a').trans (by rw [Category.assoc, g0f])
        · refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g0) y mg _).trans ?_
          rw [c2]
          exact hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy
      rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
      rw [e1, mul_left_comm] at e2
      exact (Units.mul_right_inj _).1 e2
  obtain ⟨a, ha, -⟩ := hs₀ s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = 0 := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    obtain ⟨b, -, hb⟩ := hgenS s
    exact zero_ne_one ((hb 0 fun i => by rw [z0 i, mul_zero]).trans (hb 1 fun i => by rw [z0 i, mul_zero]).symm)
  exact ⟨θ, s, hθ, ⟨w1, w2, σ', s1, θ2, ⟨g1, r1⟩, ⟨g2, r2⟩, hI1, hI2, fun j hj => rfl, hgc⟩, hgenS,
    Units.mk0 a a0, ha⟩

end Frame

section Points

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth GlobalTheory.GenericCentre
attribute [local instance] Over.cartesianMonoidalCategory

end Points

end GlobalTheory.DepthSum
end
end
