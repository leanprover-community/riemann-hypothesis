import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreMore

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem isLocalization_of_mem_iff {O F : Type*} [CommRing O] [Field F] (φ : O →+* F) (hφ : Function.Injective φ)
    (L : Subring F) [Algebra O L] (hL : ∀ x : O, ((algebraMap O L x : L) : F) = φ x) (m : Ideal O) [m.IsPrime]
    (h : ∀ y : F, y ∈ L ↔ ∃ x s : O, s ∉ m ∧ y * φ s = φ x) :
    IsLocalization.AtPrime L m where
  map_units := by
    rintro ⟨s, hs⟩
    have hs0 : φ s ≠ 0 := fun h0 => hs (by rw [(map_eq_zero_iff φ hφ).1 h0]; exact m.zero_mem)
    refine IsUnit.of_mul_eq_one ⟨(φ s)⁻¹, (h _).2 ⟨1, s, hs, by rw [map_one, inv_mul_cancel₀ hs0]⟩⟩ ?_
    apply Subtype.ext
    simp only [Subring.coe_mul, hL, Subring.coe_one]
    exact mul_inv_cancel₀ hs0
  surj z := by
    obtain ⟨x, s, hs, hxs⟩ := (h z).1 z.2
    exact ⟨⟨x, ⟨s, hs⟩⟩, Subtype.ext (by simp only [Subring.coe_mul, hL]; exact hxs)⟩
  exists_of_eq {x y} hxy := ⟨1, by
    have h1 := congrArg Subtype.val hxy
    rw [hL, hL] at h1
    rw [hφ h1]⟩

theorem card_quot_map_eq_card_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] [IsLocalization.AtPrime S (p.comap (Ideal.Quotient.mk I))] :
    Nat.card (S ⧸ I.map (algebraMap R S)) = Nat.card (Localization.AtPrime p) := by
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) (p.comap (Ideal.Quotient.mk I)).primeCompl = p.primeCompl := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨r', hr', he⟩
      rw [← he]
      exact hr'
    · intro hx
      exact ⟨r, hx, rfl⟩
  have : IsLocalization p.primeCompl (S ⧸ I.map (algebraMap R S)) := hM ▸ inferInstance
  exact Nat.card_congr (IsLocalization.algEquiv p.primeCompl _ (Localization.AtPrime p)).toEquiv

theorem card_quot_span_eq_card_localization {O L : Type*} [CommRing O] [CommRing L] (ψ : O →+* L) (b : O)
    (m : Ideal O) [m.IsPrime] (p : Ideal (O ⧸ Ideal.span {b})) [p.IsPrime]
    (hm : m = p.comap (Ideal.Quotient.mk _)) (h : @IsLocalization O _ m.primeCompl L _ ψ.toAlgebra) :
    Nat.card (L ⧸ Ideal.span {ψ b}) = Nat.card (Localization.AtPrime p) := by
  subst hm
  let _ := ψ.toAlgebra
  rw [← card_quot_map_eq_card_localization (S := L) (Ideal.span {b}) p, Ideal.map_span, Set.image_singleton,
    RingHom.algebraMap_toAlgebra]

theorem log_card_eq_sum_log_card_localization (A : Type*) [CommRing A] [Finite A] [Fintype (PrimeSpectrum A)] :
    Real.log (Nat.card A) = ∑ p : PrimeSpectrum A, Real.log (Nat.card (Localization.AtPrime p.asIdeal)) := by
  have hA : Nat.card A = ∏ p : PrimeSpectrum A, Nat.card (Localization.AtPrime p.asIdeal) := by
    rw [Nat.card_congr (PrimeSpectrum.toPiLocalizationEquiv A).toEquiv, Nat.card_pi]
  have h0 : Nat.card A ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  rw [hA, Finset.prod_ne_zero_iff] at h0
  rw [hA, Nat.cast_prod, Real.log_prod fun p _ => by exact_mod_cast h0 p (Finset.mem_univ _)]

theorem finsum_mem_eq_sum_of_injective {α β : Type*} [Fintype β] (s : Set α) (f : α → ℝ) (g : β → α)
    (hg : Function.Injective g) (hs : ∀ x, g x ∈ s) (hf : ∀ a ∈ s, f a ≠ 0 → a ∈ Set.range g) :
    ∑ᶠ a ∈ s, f a = ∑ x, f (g x) := by
  have hS : s ∩ Function.support f = Set.range g ∩ Function.support f := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hf a h1 h2, h2⟩
    · rintro ⟨⟨x, rfl⟩, h2⟩
      exact ⟨hs x, h2⟩
  rw [← finsum_mem_inter_support, hS, finsum_mem_inter_support, finsum_mem_range hg, finsum_eq_sum_of_fintype]

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option maxHeartbeats 1000000 in

theorem RegularityLocal.proof (hO : RegularityOrder.Statement) (hE : RegularityMaximalSpectrum.Statement) :
    RegularityLocal.Statement := by
  classical
  intro K _ ι _ P b hP hb
  have : P.IsPrime := hP.2.1.1
  obtain ⟨e, he⟩ := hE K ι P hP
  obtain ⟨hfree, hfinite, -⟩ := hO K ι P hP
  let φ : regRing P →+* FractionRing (MRing ι ⧸ P) := (funField P).subtype.comp (regRing P).subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  let ψ : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, regRing P →+* locRing P W.1 :=
    fun W => φ.codRestrict (locRing P W.1) fun x => x.2 W.1 W.2.1 W.2.2
  have hcard : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W},
      locIdeal P W.1 (φ b) = Ideal.span {ψ W b} := fun W => locIdeal_eq_span (b.2 W.1 W.2.1 W.2.2)
  have hloc : ∀ W, @IsLocalization (regRing P) _ (e W).asIdeal.primeCompl (locRing P W.1) _ (ψ W).toAlgebra :=
    fun W => by
      let _ := (ψ W).toAlgebra
      have := (e W).isMaximal
      exact isLocalization_of_mem_iff φ hφ (locRing P W.1) (fun _ => rfl) (e W).asIdeal (he W)

  have hone : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∉ (e W).asIdeal →
      Nat.card (locRing P W.1 ⧸ locIdeal P W.1 (φ b)) = 1 := fun W hbW => by
    let _ := (ψ W).toAlgebra
    have := hloc W
    have hu : IsUnit (ψ W b) :=
      IsLocalization.map_units (M := (e W).asIdeal.primeCompl) (locRing P W.1) ⟨b, hbW⟩
    rw [hcard, Ideal.span_singleton_eq_top.2 hu]
    exact Nat.card_eq_one_iff_unique.2 ⟨Ideal.Quotient.subsingleton_iff.2 rfl, ⟨0⟩⟩

  set I : Ideal (regRing P) := Ideal.span {b} with hI
  have : Finite (regRing P ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I (by rwa [hI, Ne, Ideal.span_singleton_eq_bot])
  have : Fintype (PrimeSpectrum (regRing P ⧸ I)) := Fintype.ofFinite _
  let m : PrimeSpectrum (regRing P ⧸ I) → MaximalSpectrum (regRing P) := fun p =>
    ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := p.asIdeal)⟩
  let g : PrimeSpectrum (regRing P ⧸ I) → {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} := fun p => e.symm (m p)
  have heg : ∀ p, (e (g p)).asIdeal = p.asIdeal.comap (Ideal.Quotient.mk I) := fun p =>
    congrArg MaximalSpectrum.asIdeal (e.apply_symm_apply (m p))
  have hg : Function.Injective g := fun p q hpq => by
    have h1 := congrArg (fun W => (e W).asIdeal) hpq
    simp only [heg] at h1
    exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  clear_value g m

  have hgp : ∀ p : PrimeSpectrum (regRing P ⧸ I),
      Nat.card (locRing P (g p).1 ⧸ locIdeal P (g p).1 (φ b)) = Nat.card (Localization.AtPrime p.asIdeal) :=
    fun p => by
      have := (e (g p)).isMaximal
      rw [hcard]
      exact card_quot_span_eq_card_localization (ψ (g p)) b (e (g p)).asIdeal p.asIdeal (heg p) (hloc (g p))

  have hsupp : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∈ (e W).asIdeal → ∃ p, g p = W :=
    fun W hbW => by
      have := (e W).isMaximal
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ (e W).asIdeal := by
        rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
        exact hbW
      refine ⟨⟨(e W).asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩, ?_⟩
      apply e.injective
      apply MaximalSpectrum.ext
      rw [heg, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left,
        ← RingHom.ker_eq_comap_bot]
      exact hker
  have hfin : {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W (φ b)) ≠ 1} ⊆
      Set.range (fun p => (g p).1) := by
    rintro W ⟨h1, h2, h3⟩
    obtain ⟨p, hp⟩ := hsupp ⟨W, h1, h2⟩ (by_contra fun hn => h3 (hone ⟨W, h1, h2⟩ hn))
    exact ⟨p, congrArg Subtype.val hp⟩
  refine ⟨(Set.finite_range _).subset hfin, ?_⟩

  refine (finsum_mem_eq_sum_of_injective {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
    (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (φ b)))) (fun p => (g p).1)
    (Subtype.val_injective.comp hg) (fun p => (g p).2)
    fun W hW h0 => hfin ⟨hW.1, hW.2, fun h1 => h0 (by rw [h1, Nat.cast_one, Real.log_one])⟩).trans ?_
  rw [log_card_eq_sum_log_card_localization (regRing P ⧸ I)]
  exact Finset.sum_congr rfl fun p _ => congrArg (fun n : ℕ => Real.log n) (hgp p)

end

end GroundTheory.Heights₂.Heights.Inter
end
