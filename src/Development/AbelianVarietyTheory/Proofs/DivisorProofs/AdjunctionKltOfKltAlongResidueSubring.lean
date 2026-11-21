import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueTopFormAlongPrimeDivisorAdjunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisOfKaehlerWedgeFreeGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFreeGenOfFormallyEtale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_topForm_orders_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K), TrBasis c x →
  IsFreeGen K (dForm c x) ∧
  ∀ E : Place c, (∃ ω : Forms E.const n, IsFreeGen E.ring ω) ∧
    (∀ η : Forms c n, η ≠ 0 → E.IsFormOrd η (E.formOrd η)) ∧
    (∀ (η : Forms c n) (f : K), η ≠ 0 → f ≠ 0 → E.formOrd (f • η) = E.ord f + E.formOrd η) ∧
    (∀ (η : Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a → E.formOrd η = a) := by
  first | exact @GlobalTheory.FieldPair.formOrd_api | exact GlobalTheory.FieldPair.formOrd_api | (intros; apply GlobalTheory.FieldPair.formOrd_api <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.LocModelTwo

variable {L : Type} [Field L] {cL : ℂ →+* L}

def primeOf (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : Ideal Q :=
  Ideal.comap ((Q.subtype).codRestrict P.ring fun x => hP x x.2) (IsLocalRing.maximalIdeal P.ring)

instance (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : (primeOf P Q hP).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_primeOf {P : Place cL} {Q : Subring L} {hP : P.Contains Q} {x : Q} :
    x ∈ primeOf P Q hP ↔ ¬ IsUnit (⟨x, hP x x.2⟩ : P.ring) := Iff.rfl

theorem isUnit_of_ord_eq_zero (P : Place cL) {y : P.ring} (hy : (y : L) ≠ 0) (h : P.ord y = 0) :
    IsUnit y := by
  have hi : (y : L)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hy)).1 (by rw [P.ord_inv, h]; rfl)
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩

theorem ord_zero (P : Place cL) : P.ord 0 = 0 := by simp [Place.ord]

theorem pos_ord_iff {P : Place cL} {Q : Subring L} (hP : P.Contains Q) {x : Q} (hx : (x : L) ≠ 0) :
    0 < P.ord x ↔ x ∈ primeOf P Q hP := by
  rw [mem_primeOf]
  constructor
  · intro h hu
    have := P.ord_eq_zero hu
    simp only at this
    omega
  · intro h
    have h0 : 0 ≤ P.ord x := (P.ord_nonneg_iff hx).2 (hP x x.2)
    refine lt_of_le_of_ne h0 fun e => h ?_
    exact isUnit_of_ord_eq_zero P (y := ⟨x, hP x x.2⟩) hx e.symm

theorem ring_le {P P' : Place cL} {Q : Subring L} (hP : P.IsPrimeOf Q) (hP' : P'.Contains Q)
    (h : primeOf P' Q hP' ≤ primeOf P Q hP.1) : P.ring ≤ P'.ring := by
  intro f hf
  obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
  have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
    rw [mem_primeOf, not_not]
    exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
  have hbP' : (⟨b, hb⟩ : Q) ∉ primeOf P' Q hP' := fun h' => hbP (h h')
  rw [mem_primeOf, not_not] at hbP'
  obtain ⟨v, hv⟩ := hbP'.exists_right_inv
  have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
  have : f = a * v := by
    calc f = f * (b * v) := by rw [hv', mul_one]
      _ = a * v := by rw [← mul_assoc, e]
  rw [this]
  exact mul_mem (hP' a ha) v.2

theorem ringKrullDim_eq_one {P : Place cL} {Q : Subring L} [IsLocalRing Q] (hP : P.IsPrimeOf Q)
    (h : IsLocalRing.maximalIdeal Q ≤ primeOf P Q hP.1) : ringKrullDim Q = 1 := by
  have hle : P.ring.toSubring ≤ Q := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
    have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
      rw [mem_primeOf, not_not]
      exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
    have hbQ : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact hbP (h ((IsLocalRing.mem_maximalIdeal _).2 hn))
    obtain ⟨v, hv⟩ := hbQ.exists_right_inv
    have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
    have : f = a * v := by
      calc f = f * (b * v) := by rw [hv', mul_one]
        _ = a * v := by rw [← mul_assoc, e]
    rw [this]
    exact Q.mul_mem ha v.2
  have hQ : Q = P.ring.toSubring := le_antisymm (fun x hx => hP.1 x hx) hle
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.subringCongr hQ)).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one P.ring)

theorem eq_span_of_mem_of_not_mem {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t u : R} (hm : Ideal.span {t, u} = IsLocalRing.maximalIdeal R) (p : Ideal R) [p.IsPrime]
    (ht : t ∈ p) (hu : u ∉ p) : p = Ideal.span {t} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).2 ht)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
    (IsNoetherian.noetherian p) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  intro y hy
  have hym : y ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hy
  rw [← hm, Ideal.mem_span_pair] at hym
  obtain ⟨c, d, e⟩ := hym
  have hdu : d * u ∈ p := by
    have : d * u = y - c * t := by rw [← e]; ring
    rw [this]
    exact p.sub_mem hy (p.mul_mem_left c ht)
  have hd : d ∈ p := ((Ideal.IsPrime.mem_or_mem ‹_› hdu).resolve_right hu)
  rw [← e]
  refine Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self t)) ?_
  have huM : u ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have := Submodule.smul_mem_smul huM hd
  rw [mul_comm]
  exact this

end GlobalTheory.FieldPair.LocModelTwo

namespace GlobalTheory.FieldPair.LocModelTwo

theorem ring_eq_and_ord_eq_zero : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  intro L _ cL Q hQ t u hm hd
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  have hA : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q,
      ¬ (t ∈ primeOf P Q hP.1 ∧ u ∈ primeOf P Q hP.1) := by
    rintro P hP ⟨ht, hu⟩
    have h1 := ringKrullDim_eq_one hP (by
      rw [← hm]
      exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨ht, Set.singleton_subset_iff.2 hu⟩))
    rw [hd] at h1
    exact absurd h1 (by decide)
  have hB : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q, 0 < P.ord (t : L) →
      primeOf P Q hP.1 = Ideal.span {t} := by
    intro P hP hpos
    have ht0 : (t : L) ≠ 0 := fun e => by rw [e, ord_zero] at hpos; exact lt_irrefl _ hpos
    have ht : t ∈ primeOf P Q hP.1 := (pos_ord_iff hP.1 ht0).1 hpos
    exact eq_span_of_mem_of_not_mem hm _ ht fun hu => hA P hP ⟨ht, hu⟩
  refine ⟨fun P P' hP hP' hPt hP't => ?_, fun P hP => ?_⟩
  · have e := (hB P hP hPt).trans (hB P' hP' hP't).symm
    exact le_antisymm (ring_le hP hP'.1 e.ge) (ring_le hP' hP.1 e.le)
  · by_contra h
    push_neg at h
    have hpos : ∀ x : Q, P.ord (x : L) ≠ 0 → x ∈ primeOf P Q hP.1 := by
      intro x hx
      have hx0 : (x : L) ≠ 0 := fun e => hx (by rw [e, ord_zero])
      exact (pos_ord_iff hP.1 hx0).1
        (lt_of_le_of_ne ((P.ord_nonneg_iff hx0).2 (hP.1 x x.2)) (Ne.symm hx))
    exact hA P hP ⟨hpos t h.1, hpos u h.2⟩

end GlobalTheory.FieldPair.LocModelTwo
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  atlas_forward_decl GlobalTheory.FieldPair.LocModelTwo.ring_eq_and_ord_eq_zero
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing KaehlerDifferential Module

theorem mem_maximalIdeal_of_mul_add_mul_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {t u : R} (h : Ideal.span {t, u} = maximalIdeal R)
    (hd : ringKrullDim R = 2) {a b : R} (hab : a * t + b * u ∈ maximalIdeal R ^ 2) :
    a ∈ maximalIdeal R := by
  by_contra ha
  have hau : IsUnit a := by simpa [mem_maximalIdeal, mem_nonunits_iff] using ha
  have hu : u ∈ maximalIdeal R := h ▸ Ideal.subset_span (by simp)
  have hle : maximalIdeal R ≤ Ideal.span {u} ⊔ maximalIdeal R ^ 2 := by
    conv_lhs => rw [← h]
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, hc⟩ := hau.exists_left_inv
      have e : x = c * (a * x + b * u) + (-(c * b)) * u := by
        linear_combination (-x) * hc
      rw [e]
      exact add_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hab))
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)))
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h1 := spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (Set.finite_singleton u)
    ((Ideal.span_singleton_le_iff_mem _).2 hu) hle
  rw [Set.ncard_singleton] at h1
  have h2 := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at h2
  have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  have := h2.trans h3
  norm_num at this

theorem isFreeGen_dForm_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
    ringKrullDim Q = 2 →
    ∃ (m : ℕ) (z : Fin m → Q),
      (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
      IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem)
        (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  intro L _ cL Q hQ t u hspan hdim
  letI := hQ.isLocalRing
  letI : Algebra ℂ Q := (cL.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  haveI : IsRegularLocalRing Q := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_
    rw [hdim, ← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Q) (Set.toFinite ({t, u} : Set Q))
    have h2 : ({t, u} : Set Q).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    exact_mod_cast h1.trans h2
  haveI : Algebra.FormallySmooth ℂ Q := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ Q
  have hs : Function.Surjective (algebraMap Q (ResidueField Q)) := residue_surjective
  haveI : Algebra.EssFiniteType ℂ (ResidueField Q) := .comp ℂ Q _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := ℂ) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap Q (ResidueField Q)) = maximalIdeal Q := ker_residue
  have htm : t ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have hum : u ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have ht0 : algebraMap Q (ResidueField Q) t = 0 := (residue_eq_zero_iff t).mpr htm
  have hu0 : algebraMap Q (ResidueField Q) u = 0 := (residue_eq_zero_iff u).mpr hum

  obtain ⟨s, hsb⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  haveI := hsb.isAlgebraic_field
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin ℂ (Set.range ((↑) : s → ResidueField Q))) (ResidueField Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨bκ, hbκ⟩ := exists_basis_kaehler_of_algebraicIndependent hsb.1
  haveI : Finite s := Module.Finite.finite_basis bκ
  let e : Fin (Nat.card s) ≃ s := (Finite.equivFin s).symm
  let b' := bκ.reindex e.symm
  have hb' : ∀ i, b' i = D ℂ (ResidueField Q) (e i) := fun i => by
    rw [Basis.reindex_apply, Equiv.symm_symm, hbκ]
  let z : Fin (Nat.card s) → Q := fun i => Function.surjInv hs (e i : ResidueField Q)
  have hz : ∀ i, algebraMap Q (ResidueField Q) (z i) = e i := fun i => Function.surjInv_eq hs _
  refine ⟨Nat.card s, z, fun P hP => ?_, ?_⟩
  · have e1 : algebraMap Q (ResidueField Q) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)
        = MvPolynomial.aeval (fun i => (e i : ResidueField Q)) P := by
      rw [show (fun i => (e i : ResidueField Q)) = algebraMap Q (ResidueField Q) ∘ z from
        funext fun i => (hz i).symm, MvPolynomial.aeval_algebraMap_apply]
      rfl
    refine (residue_ne_zero_iff_isUnit _).mp ?_
    change algebraMap Q (ResidueField Q) _ ≠ 0
    rw [e1]
    exact fun h0 => hP ((algebraicIndependent_iff.1 (hsb.1.comp e e.injective)) P h0)
  · let v : Fin (Nat.card s + 2) → Q := Fin.cons t (Fin.cons u z : Fin (Nat.card s + 1) → Q)
    let w : Fin (Nat.card s + 2) → (ResidueField Q) ⊗[Q] Ω[Q⁄ℂ] := TensorProduct.mk Q (ResidueField Q) Ω[Q⁄ℂ] 1 ∘ fun i => D ℂ Q (v i)
    have hw0 : w 0 = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q t := rfl
    have hw1 : w (Fin.succ 0) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q u := rfl
    have hwz : ∀ i : Fin (Nat.card s), w i.succ.succ = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (z i) := fun i => rfl
    have hmb : ∀ x : Q, mapBaseChange ℂ Q (ResidueField Q) ((1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x) = D ℂ (ResidueField Q) (algebraMap Q (ResidueField Q) x) :=
      fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
    have hpair : ∀ a b : Q, (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) =
        algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0) := fun a b => by
      rw [hw0, hw1]
      simp only [map_add, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul]
      rw [← algebraMap_smul (ResidueField Q) t, ← algebraMap_smul (ResidueField Q) u, ht0, hu0]
      simp only [zero_smul, add_zero, algebraMap_smul]
    have hkc : ∀ x (hx : x ∈ RingHom.ker (algebraMap Q (ResidueField Q))),
        kerCotangentToTensor ℂ Q (ResidueField Q) ((RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨x, hx⟩) =
          (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x := fun x hx => kerCotangentToTensor_toCotangent _ _ _ _

    have hsp : Submodule.span (ResidueField Q) (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      let c := b'.repr (mapBaseChange ℂ Q (ResidueField Q) y)
      have hy0 : mapBaseChange ℂ Q (ResidueField Q) (y - ∑ i, c i • w i.succ.succ) = 0 := by
        rw [map_sub, map_sum, sub_eq_zero]
        conv_lhs => rw [← b'.sum_repr (mapBaseChange ℂ Q (ResidueField Q) y)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hwz, hmb, hz, hb']
      obtain ⟨c', hc'⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ Q (ResidueField Q) hs _).mp hy0
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c'
      have hx' := hx
      rw [hker, ← hspan, Ideal.mem_span_pair] at hx'
      obtain ⟨a, b, rfl⟩ := hx'
      rw [hkc, hpair] at hc'
      have hy : y = (algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)) + ∑ i, c i • w i.succ.succ := by
        rw [hc', sub_add_cancel]
      rw [hy]
      refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ 0, rfl⟩)))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

    have hli : LinearIndependent (ResidueField Q) w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hg
      have hφ := congrArg (mapBaseChange ℂ Q (ResidueField Q)) hg
      simp only [map_add, map_sum, map_smul, map_zero] at hφ
      rw [hw0, hmb, ht0, Derivation.map_zero, smul_zero, zero_add] at hφ
      rw [hw1, hmb, hu0, Derivation.map_zero, smul_zero, zero_add] at hφ
      simp only [hwz, hmb, hz, ← hb'] at hφ
      have hrest : ∀ i : Fin (Nat.card s), g i.succ.succ = 0 :=
        Fintype.linearIndependent_iff.mp b'.linearIndependent (fun i => g i.succ.succ) hφ
      simp only [hrest, zero_smul, Finset.sum_const_zero, add_zero] at hg
      obtain ⟨a, ha⟩ := hs (g 0)
      obtain ⟨b, hb⟩ := hs (g (Fin.succ 0))
      have hg' : (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = 0 := by
        rw [hpair, ha, hb]
        exact hg
      have hmem : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) := by
        rw [hker]
        exact add_mem (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hum)
      have hsq : a * t + b * u ∈ maximalIdeal Q ^ 2 := by
        have h1 : (RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨_, hmem⟩ = 0 :=
          hinj (by rw [hkc, map_zero]; exact hg')
        have h2 : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) ^ 2 :=
          (Ideal.toCotangent_eq_zero _ _).mp h1
        rwa [hker] at h2
      have ham : a ∈ maximalIdeal Q := mem_maximalIdeal_of_mul_add_mul_mem_sq hspan hdim hsq
      have hbm : b ∈ maximalIdeal Q := by
        refine mem_maximalIdeal_of_mul_add_mul_mem_sq (t := u) (u := t) (a := b) (b := a)
          (by rw [Set.pair_comm]; exact hspan) hdim ?_
        rw [add_comm]; exact hsq
      have h0 : g 0 = 0 := by rw [← ha]; exact (residue_eq_zero_iff a).mpr ham
      have h1 : g (Fin.succ 0) = 0 := by rw [← hb]; exact (residue_eq_zero_iff b).mpr hbm
      intro i
      refine Fin.cases h0 (fun j => Fin.cases h1 (fun k => hrest k) j) i
    haveI : Module.FinitePresentation Q Ω[Q⁄ℂ] := Module.finitePresentation_of_finite Q _
    obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := Q) (fun i => D ℂ Q (v i)) hli hsp
      (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal Q).subtype
        Subtype.val_injective)
    exact isFreeGen_dForm v b hb

end GlobalTheory.FieldPair
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∃ (m : ℕ) (z : Fin m → Q),
    (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  atlas_forward_decl GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd (dForm cL (fun i => (x i : L))) = 0 := by
  intro L _ cL Q hQ D x hx P hP
  let α : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  let ρ : Q →+* P.ring := RingHom.codRestrict Q.subtype P.ring (fun q => hP.1 q q.2)
  have hρ : ρ.comp α = P.const := RingHom.ext fun _ => Subtype.ext rfl
  have e : dForm cL (fun i => (x i : L)) = P.toRat D (dForm P.const fun i => ρ (x i)) := by
    have h := TopForm.formMap_dForm (D := D) (α := P.const) (β := cL) P.ring.subtype rfl (fun i => ρ (x i))
    refine Eq.trans ?_ h.symm
    congr 1
  let S : Submonoid Q :=
    { carrier := {b | (b : L) ≠ 0 ∧ P.ord b = 0}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · change (a : L) * b ≠ 0
          exact mul_ne_zero ha.1 hb.1
        · change P.ord ((a : L) * b) = 0
          rw [P.ord_mul ha.1 hb.1, ha.2, hb.2, add_zero]
      one_mem' := ⟨one_ne_zero, P.ord_one⟩ }
  letI := α.toAlgebra
  letI := P.const.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower ℂ Q P.ring := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization S P.ring :=
    { map_units := fun ⟨b, hb⟩ => by
        have hinv : (b : L)⁻¹ ∈ P.ring := by
          rw [← P.ord_nonneg_iff (inv_ne_zero hb.1), P.ord_inv, hb.2, neg_zero]
        exact IsUnit.of_mul_eq_one (⟨(b : L)⁻¹, hinv⟩ : P.ring)
          (Subtype.ext (mul_inv_cancel₀ hb.1))
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb0, hbo⟩), Subtype.ext e⟩
      exists_of_eq := fun {a b} e => by
        have h : (a : L) = b := congrArg (fun z : P.ring => (z : L)) e
        exact ⟨1, by rw [Subtype.ext h]⟩ }
  haveI : Algebra.FormallyEtale Q P.ring := .of_isLocalization S
  have hG : IsFreeGen P.ring (TopForm.formMap D ρ hρ (dForm α x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q P.ring) D)
  rw [TopForm.formMap_dForm] at hG
  rw [e]
  exact P.formOrd_toRat hG

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd (dForm cL (fun i => (x i : L))) = 0 := by
  atlas_forward_decl GlobalTheory.formOrd_dForm_of_isPrimeOf
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_of_kaehlerWedge_freeGenerator : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  first | exact @GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm | exact GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm | (intros; apply GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem residuePlace_of_locModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  intro L K _ _ cL cK Q hQ t u hm hdim S ψ hS ht hψ hc
  letI := hQ.isLocalRing
  have hSQ : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let φ₀ : Q →+* S.ring := Q.subtype.codRestrict S.ring hSQ
  let φ : Q →+* K := ψ.comp φ₀
  have hker : ∀ s : S.ring, ψ s = 0 ↔ ¬ IsUnit s := by
    intro s
    have hmax := RingHom.ker_isMaximal_of_surjective ψ hψ
    have h := IsLocalRing.eq_maximalIdeal hmax
    rw [← RingHom.mem_ker, h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hunit : ∀ s : S.ring, (s : L) ≠ 0 → S.ord s = 0 → IsUnit s := by
    intro s hs h0
    have hinv : (s : L)⁻¹ ∈ S.ring :=
      (S.ord_nonneg_iff (inv_ne_zero hs)).1 (by rw [S.ord_inv, h0, neg_zero])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hs))
  have hφt : φ t = 0 := by
    show ψ (φ₀ t) = 0
    rw [hker]
    intro hu
    have h := S.ord_eq_zero hu
    change S.ord (t : L) = 0 at h
    rw [ht] at h
    exact one_ne_zero h
  have hφu : φ u ≠ 0 := by
    intro hu0
    have hsp : Ideal.span {t, u} ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hφt
      · exact hu0
    have hle : ∀ f ∈ S.ring, f ∈ Q := by
      intro f hf
      obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f hf
      have hbu : IsUnit (⟨b, hb⟩ : Q) := by
        by_contra hnu
        have h1 : φ ⟨b, hb⟩ = 0 := hsp (hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu)
        exact (hker _).1 h1 (hunit (φ₀ ⟨b, hb⟩) hb0 hbo)
      obtain ⟨v, hv⟩ := hbu.exists_right_inv
      have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
      have hf' : f = a * (v : L) := by
        calc f = f * (b * v) := by rw [hv', mul_one]
          _ = a * v := by rw [← mul_assoc, e]
      rw [hf']
      exact Q.mul_mem ha v.2
    let e : Q ≃+* S.ring := RingEquiv.ofBijective φ₀
      ⟨fun x y h => Subtype.ext (congrArg (fun s : S.ring => (s : L)) h), fun s => ⟨⟨s, hle s s.2⟩, rfl⟩⟩
    have h := ringKrullDim_eq_of_ringEquiv e
    rw [hdim, IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    norm_num at h
  have hmemR : ∀ a : K, a ∈ φ.range ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a := by
    intro a
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φ₀ q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hfrac : ∀ a : K, ∃ x y : Q, φ y ≠ 0 ∧ a * φ y = φ x := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    obtain ⟨x, hx, y, hy, hy0, hyo, e⟩ := hS.2 s s.2
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => (hker _).1 h (hunit (φ₀ ⟨y, hy⟩) hy0 hyo), ?_⟩
    show ψ s * ψ (φ₀ ⟨y, hy⟩) = ψ (φ₀ ⟨x, hx⟩)
    rw [← map_mul]
    exact congrArg ψ (Subtype.ext e)
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  let R := φ.range
  let φR : Q →+* R := φ.rangeRestrict
  haveI : IsNoetherianRing R := isNoetherianRing_range φ
  haveI : IsLocalRing R := IsLocalRing.of_surjective' φR φ.rangeRestrict_surjective
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {φR u} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective φR φ.rangeRestrict_surjective, ← hm,
      Ideal.map_span, Set.image_pair]
    have h0 : φR t = 0 := Subtype.ext hφt
    rw [h0, Ideal.span_insert_zero]
  have hu0R : φR u ≠ 0 := fun h => hφu (congrArg Subtype.val h)
  have hnf : ¬ IsField R := by
    intro hf
    obtain ⟨w, hw⟩ := hf.mul_inv_cancel hu0R
    have hmem : φR u ∈ IsLocalRing.maximalIdeal R := hmR ▸ Ideal.subset_span rfl
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_mul_eq_one w hw)
  haveI hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).2
      (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨_, hmR⟩)
  let V : ValuationSubring K :=
    { R with
      mem_or_inv_mem' := by
        intro a
        obtain ⟨x, y, hy, e⟩ := hfrac a
        obtain ⟨c, hc | hc⟩ := ValuationRing.cond (φR x) (φR y)
        · right
          have hc' : φ x * (c : K) = φ y := congrArg Subtype.val hc
          have h1 : a * c = 1 := by
            refine mul_right_cancel₀ hy ?_
            linear_combination (c : K) * e + hc'
          rw [inv_eq_of_mul_eq_one_right h1]
          exact c.2
        · left
          have hc' : φ y * (c : K) = φ x := congrArg Subtype.val hc
          have h1 : a = c := by
            refine mul_right_cancel₀ hy ?_
            linear_combination e - hc'
          rw [h1]
          exact c.2 }
  have hconst : ∀ a, cK a ∈ V := fun a => (hmemR (cK a)).2 ⟨S.const a, hQ.const_mem a, hc a⟩
  have hφV : ∀ q : Q, φ q ∈ V := fun q => ⟨q, rfl⟩
  let φV : Q →+* V := φ.codRestrict V hφV
  have hφVs : Function.Surjective φV := by
    rintro ⟨v, q, rfl⟩
    exact ⟨q, rfl⟩
  haveI hdvrV : IsDiscreteValuationRing V := hdvr
  have hcomp : cK.codRestrict V hconst = φV.comp (cL.codRestrict Q hQ.const_mem) :=
    RingHom.ext fun a => Subtype.ext (hc a).symm
  let F : Place cK :=
    ⟨V, hconst, hdvrV, hcomp ▸ hQ.essFiniteType.comp (RingHom.FiniteType.of_surjective φV hφVs).essFiniteType⟩
  refine ⟨F, hmemR, fun us hus => ?_⟩
  have h1 : ψ us = ((φV u : V) : K) := by
    show ψ us = ψ (φ₀ u)
    exact congrArg ψ (Subtype.ext hus)
  have hmV : IsLocalRing.maximalIdeal V = Ideal.span {φV u} := hmR
  have hirr : Irreducible (φV u) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmV
  rw [h1]
  exact F.ord_irreducible hirr

end GlobalTheory.FieldPair
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  atlas_forward_decl GlobalTheory.FieldPair.residuePlace_of_locModel
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTrBasis

open IsLocalRing

theorem trdeg_le_of_residue {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (S : Place cL) (ψ : S.ring →+* K) (hψ : Function.Surjective ψ)
    (hc : ∀ a, ψ (S.const a) = cK a) (m : ℕ) (x : Fin (m + 2) → L) (hx : TrBasis cL x) :
    letI := cK.toAlgebra
    Algebra.trdeg ℂ K ≤ (m + 1 : ℕ) := by
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hL : Algebra.trdeg ℂ L = (m + 2 : ℕ) := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hR : Algebra.trdeg ℂ (ResidueField S.ring) = (m + 1 : ℕ) :=
    trdeg_residueField_of_trdeg ℂ S.ring L hL
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ K
  let res := IsLocalRing.residue S.ring
  let lift : s → S.ring := fun i => Function.surjInv hψ (i : K)
  have hlift : ψ ∘ lift = Subtype.val := funext fun i => Function.surjInv_eq hψ _
  have hg : AlgebraicIndependent ℂ (fun i => res (lift i)) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    have h0 : res (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) = 0 := by
      rw [MvPolynomial.eval₂_comp_left]
      exact hP
    rw [IsLocalRing.residue_eq_zero_iff, ← hker, RingHom.mem_ker, MvPolynomial.hom_eval₂,
      hcomp, show (fun i => ψ (lift i)) = Subtype.val from hlift] at h0
    exact algebraicIndependent_iff.1 hs.1 P h0
  have h1 := hg.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, hR] at h1
  exact h1

theorem trBasis_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  intro L K _ _ cL cK S ψ hψ hc F m π y ⟨x, hx⟩ hπ hy hP
  have htr := trdeg_le_of_residue cL cK S ψ hψ hc m x hx
  letI : Algebra ℂ F.ring := F.const.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by omega)
  let f : F.ring := ⟨π, hπm⟩
  have hf0 : f ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
  have hfm : f ∈ maximalIdeal F.ring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := F.ord_eq_zero hu
    change F.ord π = 0 at this
    omega
  let w : Fin m → F.ring := fun i => ⟨y i, hy i⟩
  have hev : ∀ P : MvPolynomial (Fin m) ℂ,
      ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) = MvPolynomial.eval₂ cK y P := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype w
    rw [ValuationSubring.subtype_apply] at h
    rw [h]
    rfl
  have hwu : ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P) := by
    intro P hP0
    obtain ⟨h1, h2⟩ := hP P hP0
    refine IsUnit.of_mul_eq_one (⟨_, h2⟩ : F.ring) (Subtype.ext ?_)
    change ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) * _ = 1
    rw [hev]
    exact mul_inv_cancel₀ h1
  have hsplit : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)
          (MvPolynomial.finSuccEquiv ℂ m P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ m : MvPolynomial (Fin (m + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons π y : Fin (m + 1) → K) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P :
          F.ring) : K) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype
      (Fin.cons f w : Fin (m + 1) → F.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hind : AlgebraicIndependent ℂ (Fin.cons π y : Fin (m + 1) → K) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ m P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf0 hfm _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      ext1 i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => Polynomial.coeff p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hQ, hQ0, map_zero])
  unfold TrBasis
  refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
  rw [Cardinal.mk_fin]
  exact htr

end GlobalTheory.FieldPair.ResidueTrBasis
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  atlas_forward_decl GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_cons_of_ord_eq_one : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  F.formOrd (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  intro K _ cK F m π y hπ hy hP hB
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)
  have hirr : Irreducible (⟨π, hπm⟩ : F.ring) := by
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible F.ring
    have hne : (⟨π, hπm⟩ : F.ring) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht
    have e : π = ((u : F.ring) : K) * (t : K) ^ n := by
      simpa using congrArg Subtype.val hu
    have hu0 : ((u : F.ring) : K) ≠ 0 := (u.isUnit.map F.ring.subtype).ne_zero
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have h1 : F.ord π = n := by
      rw [e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow,
        F.ord_irreducible ht]
      simp
    obtain rfl : n = 1 := by
      rw [hπ] at h1
      exact_mod_cast h1.symm
    rw [hu, pow_one]
    exact (irreducible_units_mul u).2 ht
  refine formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩
  intro P hP0
  obtain ⟨h0, hi⟩ := hP P hP0
  have e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) =
      MvPolynomial.eval₂ cK y P :=
    MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P
  refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)
  change ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1
  rw [e]
  exact mul_inv_cancel₀ h0

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_kaehlerWedge_uniformiser_residueIndependent_eq_zero : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  F.formOrd (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  atlas_forward_decl GlobalTheory.formOrd_dForm_cons_of_ord_eq_one
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem eval₂_residue_ne_zero_and_inv_mem_of_isUnit :
    ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  intro L K _ _ cL cK Q hQ S ψ F hSQ hc hF m z zs hz hu P hP
  let j : Q →+* S.ring := Q.subtype.codRestrict S.ring fun q => hSQ q q.2
  have h1 : (ψ.comp j).comp (cL.codRestrict Q hQ.const_mem) = cK := RingHom.ext fun a => hc a
  have h2 : (fun i => (ψ.comp j) (z i)) = fun i => ψ (zs i) :=
    funext fun i => congrArg ψ (Subtype.ext (hz i).symm)
  have h3 : (ψ.comp j) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) =
      MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P := by
    rw [MvPolynomial.hom_eval₂, h1, h2]
  obtain ⟨q, hq⟩ := (hu P hP).exists_right_inv
  have h4 : MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P * (ψ.comp j) q = 1 := by
    rw [← h3, ← map_mul, hq, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h4, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h4]
  exact (hF _).2 ⟨j q, q.2, rfl⟩

end GlobalTheory.FieldPair
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residuePlace_eval_ne_zero_inv_mem_of_isUnit : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  atlas_forward_decl GlobalTheory.FieldPair.eval₂_residue_ne_zero_and_inv_mem_of_isUnit
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUnit

variable {k L : Type} [Field k] [Field L] {c : k →+* L}

theorem isNoetherianRing {Q : Subring L} (hQ : IsLocModel c Q) : IsNoetherianRing Q := by
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
  exact Algebra.EssFiniteType.isNoetherianRing k Q

theorem isFractionRing {Q : Subring L} (hQ : IsLocModel c Q) : IsFractionRing Q L := by
  refine IsFractionRing.of_field Q L fun z => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩

theorem exists_place_of_height_eq_one {Q : Subring L} (hQ : IsLocModel c Q) [IsIntegrallyClosed Q]
    (p : Ideal Q) [p.IsPrime] (hp1 : p.height = 1) :
    ∃ P : Place c, P.IsPrimeOf Q ∧ ∀ a ∈ P.ring, ∃ s : Q, s ∉ p ∧ (s : L) * a ∈ Q := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  haveI : IsFractionRing Q L := isFractionRing hQ
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q L := Localization.subalgebra.ofField L p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hp
  haveI : IsLocalization.AtPrime A p := hA
  haveI : IsDiscreteValuationRing A := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 A
  haveI : IsFractionRing A L := Localization.subalgebra.isFractionRing_ofField L _ hp
  let V : ValuationSubring L :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, fun f hf => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    have e' : f * (b.1 : L) = a := congrArg Subtype.val e
    exact ⟨b.1, b.2, by rw [mul_comm, e']; exact a.2⟩

theorem mem_of_forall_isPrimeOf {Q : Subring L} (hQ : IsLocModel c Q) [IsIntegrallyClosed Q]
    (a : L) (h : ∀ P : Place c, P.IsPrimeOf Q → a ∈ P.ring) : a ∈ Q := by
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  haveI : IsFractionRing Q L := isFractionRing hQ
  obtain ⟨y, hy⟩ := (GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := Q) (K := L) a).2
    fun p _ hp1 => by
      obtain ⟨P, hP, hs⟩ := exists_place_of_height_eq_one hQ p hp1
      obtain ⟨s, hsp, hsa⟩ := hs a (h P hP)
      exact (GlobalTheory.mem_primeLocalSubalgebra_iff p a).2 ⟨s, hsp, ⟨⟨_, hsa⟩, rfl⟩⟩
  rw [← hy]
  exact y.2

end GlobalTheory.FieldPair.AdjUnit

namespace GlobalTheory.FieldPair.AdjUnit

theorem eq_unit_mul_zpow : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
    ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  intro L _ cL Q hQ t u hm hd E hE hu G hG hP
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  have hsp : (Ideal.span {t, u} : Ideal Q).spanFinrank ≤ 2 :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  haveI : IsRegularLocalRing Q := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q (by
    rw [← hm, hd]; exact_mod_cast hsp)
  have huL : (u : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hu
    exact zero_ne_one hu
  have hu0 : u ≠ 0 := fun h => huL (by rw [h]; rfl)
  have hum : u ∈ IsLocalRing.maximalIdeal Q := hm ▸ Ideal.subset_span (by simp)
  have htm : t ∈ IsLocalRing.maximalIdeal Q := hm ▸ Ideal.subset_span (by simp)
  have hu2 : u ∉ IsLocalRing.maximalIdeal Q ^ 2 := by
    intro h2
    have hle : IsLocalRing.maximalIdeal Q ≤ Ideal.span {t} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Q)
        (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
      rw [← hm, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Submodule.mem_sup_left (Ideal.subset_span rfl), Submodule.mem_sup_right ?_⟩
      rw [hm, smul_eq_mul, ← pow_two]
      exact h2
    have heq : IsLocalRing.maximalIdeal Q = Ideal.span {t} :=
      le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).2 htm)
    have h1 : (IsLocalRing.maximalIdeal Q).spanFinrank ≤ 1 := by
      rw [heq]
      exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
        (by rw [Set.ncard_singleton])
    have h3 := ringKrullDim_le_spanFinrank_maximalIdeal Q
    rw [hd] at h3
    have h4 : ((IsLocalRing.maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
    have := h3.trans h4
    norm_num at this
  haveI : IsRegularLocalRing (Q ⧸ Ideal.span ({u} : Set Q)) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hum hu2
  have hdom : IsDomain (Q ⧸ Ideal.span ({u} : Set Q)) := inferInstance
  have hpr : Prime u :=
    (Ideal.span_singleton_prime hu0).1 ((Ideal.Quotient.isDomain_iff_prime _).1 hdom)
  obtain ⟨S, -, -, hSo⟩ := GlobalTheory.FieldPair.AdjModel.exists_place hQ hpr
  have hES : E.ring = S.ring := by
    by_contra h
    have := hSo E hE h
    omega
  haveI : IsIntegrallyClosed Q := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing Q).2
  set b := E.ord G with hb
  set G' : L := G * (u : L) ^ (-b) with hG'
  have hG'0 : G' ≠ 0 := mul_ne_zero hG (zpow_ne_zero _ huL)
  have hord : ∀ P : Place cL, P.IsPrimeOf Q → P.ord G' = 0 := by
    intro P hPQ
    rw [hG', P.ord_mul hG (zpow_ne_zero _ huL), P.ord_zpow]
    by_cases hPE : P.ring = E.ring
    · obtain rfl : P = E := Place.ext hPE
      rw [hu, ← hb]; ring
    · rw [hP P hPQ hPE, hSo P hPQ (hES ▸ hPE)]; ring
  have h1 : G' ∈ Q := mem_of_forall_isPrimeOf hQ G' fun P hPQ =>
    (P.ord_nonneg_iff hG'0).1 (by rw [hord P hPQ])
  have h2 : G'⁻¹ ∈ Q := mem_of_forall_isPrimeOf hQ G'⁻¹ fun P hPQ =>
    (P.ord_nonneg_iff (inv_ne_zero hG'0)).1 (by rw [P.ord_inv, hord P hPQ]; rfl)
  refine ⟨⟨G', h1⟩, IsUnit.of_mul_eq_one (a := (⟨G', h1⟩ : Q)) (⟨G'⁻¹, h2⟩ : Q)
    (Subtype.ext (mul_inv_cancel₀ hG'0)), ?_⟩
  change G = G * (u : L) ^ (-b) * (u : L) ^ b
  rw [mul_assoc, ← zpow_add₀ huL, neg_add_cancel, zpow_zero, mul_one]

end GlobalTheory.FieldPair.AdjUnit
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
  ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
  ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  atlas_forward_decl GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTransport

variable {k M : Type} [Field k] [Field M] {c : k →+* M}

theorem ord_prod_zpow {ι : Type} (P : Place c) (s : Finset ι) (f : ι → M) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : P.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s)))
        (Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))),
      P.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ordQ_mapDomain {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) :
    P.ordQ (Finsupp.mapDomain f φ) = ∑ g ∈ φ.support, φ g * P.ord (f g) := by
  rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

theorem ord_prod_eq_mul_ordQ {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) (N : ℕ)
    (m : ι → ℤ) (hm : ∀ g ∈ φ.support, (m g : ℚ) = N * φ g) (hf : ∀ g ∈ φ.support, f g ≠ 0) :
    (P.ord (∏ g ∈ φ.support, f g ^ m g) : ℚ) = N * P.ordQ (Finsupp.mapDomain f φ) := by
  rw [ord_prod_zpow P _ f m hf, ordQ_mapDomain, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hm g hg]
  ring

theorem exists_common_den {ι : Type} (s : Finset ι) (φ : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ s, ∃ m : ℤ, (m : ℚ) = N * φ g := by
  classical
  refine ⟨∏ g ∈ s, (φ g).den, Finset.prod_pos fun g _ => (φ g).den_pos, fun g hg =>
    ⟨(φ g).num * ∏ x ∈ s.erase g, ((φ x).den : ℤ), ?_⟩⟩
  rw [← Finset.mul_prod_erase s _ hg]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

end GlobalTheory.FieldPair.ResidueTransport

namespace GlobalTheory.FieldPair

open ResidueTransport in

theorem ordQ_mapDomain_residue_eq {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (Q : Subring L) (u : Q) (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK)
    (hSQ : S.Contains Q) (hSu : S.ord (u : L) = 0) (hu0 : (u : L) ≠ 0)
    (hψ : Function.Surjective ψ)
    (hF : ∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a)
    (hFu : ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1)
    (hG : ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
      ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G)
    (φ : S.ring →₀ ℚ) (hsupp : ∀ g ∈ φ.support, ψ g ≠ 0)
    (hPφ : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) :
    F.ordQ (Finsupp.mapDomain ψ φ) =
      E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by

  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal S.ring :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
  have hunit : ∀ g ∈ φ.support, IsUnit g := fun g hg =>
    IsLocalRing.notMem_maximalIdeal.1 (by rw [← hker, RingHom.mem_ker]; exact hsupp g hg)
  choose! w hw using hunit
  obtain ⟨N, hN, hm⟩ := exists_common_den φ.support φ
  choose! m hm using hm
  have hg0 : ∀ g ∈ φ.support, ((g : S.ring) : L) ≠ 0 := fun g hg h =>
    hsupp g hg (by rw [show g = 0 from Subtype.ext h, map_zero])
  set G : L := ∏ g ∈ φ.support, ((g : S.ring) : L) ^ m g with hGdef
  set H : K := ∏ g ∈ φ.support, ψ g ^ m g with hHdef
  have hGord := fun P : Place cL => ord_prod_eq_mul_ordQ P φ (fun g : S.ring => (g : L)) N m hm hg0
  have hHord := ord_prod_eq_mul_ordQ F φ ψ N m hm hsupp
  have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.2 fun g hg => zpow_ne_zero _ (hg0 g hg)

  have hPG : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0 := by
    intro P hP hPE
    by_cases hPS : P.ring = S.ring
    · obtain rfl : P = S := Place.ext hPS
      rw [hGdef, ord_prod_zpow P _ _ m hg0]
      refine Finset.sum_eq_zero fun g hg => ?_
      rw [← hw g hg, P.ord_eq_zero (w g).isUnit, mul_zero]
    · have h := hGord P
      rw [hPφ P hP hPS hPE, mul_zero] at h
      exact_mod_cast h
  obtain ⟨q, hqU, hGq⟩ := hG G hG0 hPG
  set b := E.ord G with hb

  let uS : S.ring := ⟨u, hSQ _ u.2⟩
  have huS : IsUnit uS := by
    have h1 : (u : L) ∈ S.ring := hSQ _ u.2
    have h2 : (u : L)⁻¹ ∈ S.ring := by
      rw [← S.ord_nonneg_iff (inv_ne_zero hu0), S.ord_inv, hSu]; simp
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hu0))
  obtain ⟨r, hr⟩ := hqU.exists_right_inv
  let qS : S.ring := ⟨q, hSQ _ q.2⟩
  let rS : S.ring := ⟨r, hSQ _ r.2⟩
  have hqr : qS * rS = 1 := Subtype.ext (by change ((q * r : Q) : L) = 1; rw [hr]; rfl)
  let qU : S.ringˣ := (IsUnit.of_mul_eq_one rS hqr).unit
  let uU : S.ringˣ := huS.unit
  let W : S.ringˣ := ∏ g ∈ φ.support, w g ^ m g
  let e : S.ringˣ →* Lˣ := Units.map (S.ring.subtype : S.ring →* L)
  let f : S.ringˣ →* Kˣ := Units.map (ψ : S.ring →* K)
  have he : ∀ x, ((e x : Lˣ) : L) = ((x : S.ring) : L) := fun _ => rfl
  have hf : ∀ x, ((f x : Kˣ) : K) = ψ x := fun _ => rfl
  have heW : ((e W : Lˣ) : L) = G := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, he]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hfW : ((f W : Kˣ) : K) = H := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hf]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hWeq : W = qU * uU ^ b := by
    have hinj : Function.Injective e := fun x y h =>
      Units.ext (Subtype.ext (by rw [← he, ← he, h]))
    apply hinj
    apply Units.ext
    rw [heW, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, he, he,
      IsUnit.unit_spec, IsUnit.unit_spec]
    exact hGq
  have hH : H = ψ qS * ψ uS ^ b := by
    rw [← hfW, hWeq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hf, hf,
      IsUnit.unit_spec, IsUnit.unit_spec]

  have hq0 : ψ qS * ψ rS = 1 := by rw [← map_mul, hqr, map_one]
  have hψq0 : ψ qS ≠ 0 := left_ne_zero_of_mul_eq_one hq0
  have hψu0 : ψ uS ≠ 0 := (huS.map ψ).ne_zero
  have hFq : F.ord (ψ qS) = 0 := by
    have h1 : 0 ≤ F.ord (ψ qS) := (F.ord_nonneg_iff hψq0).2 ((hF _).2 ⟨qS, q.2, rfl⟩)
    have hinv : (ψ qS)⁻¹ = ψ rS := inv_eq_of_mul_eq_one_right hq0
    have h2 : 0 ≤ F.ord (ψ qS)⁻¹ := (F.ord_nonneg_iff (inv_ne_zero hψq0)).2
      (by rw [hinv]; exact (hF _).2 ⟨rS, r.2, rfl⟩)
    rw [F.ord_inv] at h2
    omega
  have hFH : F.ord H = b := by
    rw [hH, F.ord_mul hψq0 (zpow_ne_zero _ hψu0), F.ord_zpow, hFq, hFu uS rfl]
    ring
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hEG := hGord E
  rw [← hb, ← hFH, hHord] at hEG
  exact mul_left_cancel₀ hNq hEG

end GlobalTheory.FieldPair
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordQ_mapDomain_residuePlace_transport : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK),
  S.Contains Q → S.ord (u : L) = 0 → (u : L) ≠ 0 → Function.Surjective ψ →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  (∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1) →
  (∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G) →
  ∀ φ : S.ring →₀ ℚ, (∀ g ∈ φ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) →
  F.ordQ (Finsupp.mapDomain ψ φ) = E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by
  atlas_forward_decl GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.AdjCodimTwo

theorem irreducible_of_ord_one {k K : Type} [Field k] [Field K] {c : k →+* K} (P : Place c)
    (x : P.ring) (hx : P.ord (x : K) = 1) : Irreducible x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hv0 : ((v : P.ring) : K) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
  have e : P.ord (((v : P.ring) * π ^ n : P.ring) : K) = n := by
    push_cast
    rw [P.ord_mul hv0 (pow_ne_zero _ hπ0), P.ord_eq_zero v.isUnit, P.ord_pow, P.ord_irreducible hπ]
    simp
  rw [e] at hx
  obtain rfl : n = 1 := by exact_mod_cast hx
  rw [pow_one]
  exact (irreducible_isUnit_mul v.isUnit).2 hπ

theorem disc_residue_eq : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
  ringKrullDim Q = 2 → S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : L) = 1 → E.ord (u : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) = 0) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    F.disc (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) =
      E.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
        (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n Q hQ t u S E ψ f w θ hm hd hS hE hSt hEu hψ hc hf hw hθ hP
  classical
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters cL Q hQ t u hm hd
  obtain ⟨m, z, hzU, hzG⟩ := GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons cL Q hQ t u hm hd
  have hxe : (fun i => ((Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q) i : L)) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => rfl) j
  have hzT := GlobalTheory.T.isTranscendenceBasis_of_kaehlerWedge_freeGenerator cL Q hQ _ _ (by omega) hzG
  have hzO := GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf cL Q hQ _ _ hzG
  rw [hxe] at hzT hzO
  obtain ⟨F, hFr, hFu⟩ := GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel cL cK Q hQ t u hm hd S ψ hS hSt hψ hc
  have hQS : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let us : S.ring := ⟨u, hQS u⟩
  let ts : S.ring := ⟨t, hQS t⟩
  let zs : Fin m → S.ring := fun i => ⟨z i, hQS (z i)⟩
  have hF1 : F.ord (ψ us) = 1 := hFu us rfl
  have hB4 := GlobalTheory.T.residuePlace_eval_ne_zero_inv_mem_of_isUnit cL cK Q hQ S ψ F hS.1 hc hFr m z zs (fun _ => rfl) hzU
  have hzF : ∀ i, ψ (zs i) ∈ F.ring := fun i => (hFr _).2 ⟨zs i, (z i).2, rfl⟩
  have hTK := GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons cL cK S ψ hψ hc F m (ψ us) (fun i => ψ (zs i)) ⟨_, hzT⟩ hF1 hzF hB4
  have hFO := GlobalTheory.T.formOrd_kaehlerWedge_uniformiser_residueIndependent_eq_zero cK F m (ψ us) (fun i => ψ (zs i)) hF1 hzF hB4 hTK
  obtain rfl : n = m + 1 := by
    letI := cK.toAlgebra
    have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hw
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hTK
    rw [Cardinal.mk_fin] at h1 h2
    exact_mod_cast h1.trans h2.symm
  let v : Fin (m + 1) → S.ring := Fin.cons us zs
  have hv : (fun i => ψ (v i)) = (Fin.cons (ψ us) (fun i => ψ (zs i)) : Fin (m + 1) → K) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have htv : (Fin.cons (ts : L) (fun i => (v i : L)) : Fin (m + 2) → L) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  set Ω0 := (dForm cL (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L)) with hΩ0
  set η := dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (m + 1 + 1) → L) with hη
  have hfreeL := (GlobalTheory.T.dvrPlace_topForm_orders_api cL (m + 2) _ hzT).1
  obtain ⟨H, hH⟩ := hfreeL.2 η
  have ht_irr : Irreducible ts := irreducible_of_ord_one S ts hSt
  obtain ⟨h, hhf, hhw⟩ := GlobalTheory.T.residue_topForm_along_primeDivisor_adjunction cL cK (m + 1) S ψ hψ hc ts f v w H ht_irr hf (hv ▸ hTK)
    (htv ▸ hzT) (by rw [htv]; exact hH.symm)
  rw [hv] at hhw
  have hne : ∀ {A M : Type} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] {ω : M},
      IsFreeGen A ω → ω ≠ 0 := fun hω h0 => one_ne_zero (hω.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  have hIK := GlobalTheory.T.dvrPlace_topForm_orders_api cK (m + 1) _ hTK
  have hIL := GlobalTheory.T.dvrPlace_topForm_orders_api cL (m + 2) _ hzT
  have hwne := hne (GlobalTheory.T.dvrPlace_topForm_orders_api cK (m + 1) _ hw).1
  have hvne := hne hIK.1
  have hΩne : Ω0 ≠ 0 := hne hfreeL
  have hψh : ψ h ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hhw
    exact hwne hhw
  have hh0 : (h : L) ≠ 0 := fun h0 => hψh (by rw [show h = 0 from Subtype.ext h0, map_zero])
  have hf0 : (f : L) ≠ 0 := fun h0 => hf.ne_zero (Subtype.ext h0)
  have ht0 : (t : L) ≠ 0 := fun h0 => ht_irr.ne_zero (Subtype.ext h0)
  have hH0 : H ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hhf
    exact mul_ne_zero hh0 hf0 hhf
  have hFw : F.formOrd (dForm cK (fun i => ψ (w i))) = F.ord (ψ h) := by
    rw [hhw, (hIK.2 F).2.2.1 _ _ hvne hψh, hFO, add_zero]
  have hPη : ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd η = P.ord H := by
    intro P hPQ
    rw [← hH, (hIL.2 P).2.2.1 Ω0 H hΩne hH0, hzO P hPQ, add_zero]
  have hPo : ∀ P : Place cL, P.ord (h : L) + P.ord (f : L) = P.ord H + P.ord (t : L) := by
    intro P
    rw [← P.ord_mul hh0 hf0, ← P.ord_mul hH0 ht0, hhf]
  have hEt : E.ord (t : L) = 0 := (hA2 E hE).resolve_right (by rw [hEu]; norm_num)
  have hSu : S.ord (u : L) = 0 := (hA2 S hS).resolve_left (by rw [hSt]; norm_num)
  have hu0 : (u : L) ≠ 0 := by
    intro h0
    rw [h0] at hEu
    simp [Place.ord] at hEu
  have hE1 := GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo cL Q hQ t u hm hd E hE hEu
  set θ' := Finsupp.mapDomain (fun g : S.ring => (g : L)) θ with hθ'
  have hφs : ∀ g ∈ (Finsupp.single h 1 - θ).support, ψ g ≠ 0 := by
    intro g hg
    rcases Finset.mem_union.1 (Finsupp.support_sub hg) with hg | hg
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
      exact hψh
    · exact hθ g hg
  have hmc : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ) =
      Finsupp.single (h : L) 1 - θ' := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hmψ : Finsupp.mapDomain ψ (Finsupp.single h 1 - θ) =
      Finsupp.single (ψ h) 1 - Finsupp.mapDomain ψ θ := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hφP : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ)) = 0 := by
    intro P hPQ hPS hPE
    have h1 := hP P hPQ hPS hPE
    rw [Place.disc, map_add, Place.ordQ_single, hPη P hPQ] at h1
    have hPt : P.ord (t : L) = 0 := by
      by_contra hne'
      have h0 : 0 ≤ P.ord (t : L) := (P.ord_nonneg_iff ht0).2 (hPQ.1 t t.2)
      exact hPS (hA1 P S hPQ hS (lt_of_le_of_ne h0 (Ne.symm hne')) (by rw [hSt]; norm_num))
    have h2 := hPo P
    rw [hPt, add_zero] at h2
    rw [hmc, map_sub, Place.ordQ_single]
    have h3 : ((P.ord (h : L) : ℤ) : ℚ) = (P.ord H : ℚ) - (P.ord (f : L) : ℚ) := by
      rw [← h2]; push_cast; ring
    rw [h3]
    linarith
  have hE2 := GlobalTheory.T.ordQ_mapDomain_residuePlace_transport cL cK Q u S E ψ F hS.1 hSu hu0 hψ hFr hFu hE1 _ hφs hφP
  rw [hmc, hmψ, map_sub, map_sub, Place.ordQ_single, Place.ordQ_single] at hE2
  refine ⟨F, hFr, ?_⟩
  rw [Place.disc, Place.disc, hFw, map_add, Place.ordQ_single, hPη E hE]
  have h2 := hPo E
  rw [hEt, add_zero] at h2
  have h3 : ((E.ord H : ℤ) : ℚ) = (E.ord (h : L) : ℚ) + (E.ord (f : L) : ℚ) := by
    rw [← h2]; push_cast; ring
  rw [h3]
  linarith

end GlobalTheory.AdjCodimTwo
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_of_klt_restrict : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n T S hS ψ f w θ R hψ hc hf hw hθ hR hK
  refine ⟨?_, ?_, ?_⟩
  · have htr := (trBasis_uniformiser_cons cL cK n S ψ f w hψ hc hf hw).1
    have hfree := (formOrd_api cL (n + 1) _ htr).1
    exact fun h0 => one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  · have hf0 : (0 : L) ≠ (f : L) := fun h => hf.ne_zero (Subtype.ext h.symm)
    have hθ0 : θ 0 = 0 := by
      by_contra h
      exact hθ 0 (Finsupp.mem_support_iff.2 h) (map_zero ψ)
    have h1 : Finsupp.mapDomain (fun g : S.ring => (g : L)) θ ((0 : S.ring) : L) = θ 0 :=
      Finsupp.mapDomain_apply Subtype.val_injective θ 0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf0, add_zero]
    exact h1.trans hθ0
  intro Q hQ t u E hTQ hspan hdim hSQ hEQ hSt hEu hP
  obtain ⟨F, hF, hdisc⟩ := GlobalTheory.AdjCodimTwo.disc_residue_eq cL cK n Q hQ t u S E ψ f w θ hspan hdim
    hSQ hEQ hSt hEu hψ hc hf hw hθ hP
  rw [← hdisc]
  apply hK.lt_disc
  intro a ha
  obtain ⟨x, hx⟩ := hR a ha
  exact (hF a).2 ⟨⟨x, hS x x.2⟩, hTQ x.2, hx⟩

end GlobalTheory.FieldPair
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjunctionKlt_of_klt_along_residue_subring : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  atlas_forward_decl GlobalTheory.FieldPair.adjKlt_of_klt_restrict
end
