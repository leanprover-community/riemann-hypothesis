import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroCoind
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyTransfer

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

section Index

theorem index_gsOpenSubgroup :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index = Module.finrank K.1 L.1 := by
  rw [coe_gsOpenSubgroup]
  change (gsEmbedding (S := S) hL).fieldRange.fixingSubgroup.index = _
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact (gsEmbedding (S := S) hL).equivFieldRange.toLinearEquiv.finrank_eq.symm

theorem finiteIndex_gsOpenSubgroup :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).FiniteIndex :=
  ⟨by rw [index_gsOpenSubgroup]; exact Module.finrank_pos.ne'⟩

theorem card_coind_gsOpenSubgroup
    (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
    Nat.card (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) =
      Nat.card B ^ Module.finrank K.1 L.1 := by
  have := finiteIndex_gsOpenSubgroup S hL
  rw [card_coind_eq, index_gsOpenSubgroup]

end Index

section Count

variable (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

theorem finrank_eq_sum_index_mackeySubgroup (v : {v : InfinitePlace K.1 // v.IsReal}) :
    Module.finrank K.1 L.1 =
      ∑ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
        (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom d.out).index := by
  let N : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) :=
    zmodRep.{0} _ 2
  have h2 : Nat.card N = 2 := by
    change Nat.card (ULift.{0} (ZMod 2)) = 2
    simp
  have hC := card_coind_gsOpenSubgroup S hL N
  have hM := Nat.card_congr (mackeyEquiv (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (gsRealFamily S ιr v).toMonoidHom N).toEquiv
  rw [Nat.card_pi, hC, h2] at hM
  have hs : ∀ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom,
      Nat.card (mackeySummand (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom N d.out) =
        2 ^ (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom d.out).index := fun d => by
    rw [card_coind_eq]
    exact congrArg (· ^ _) h2
  rw [Finset.prod_congr rfl fun d _ => hs d, Finset.prod_pow_eq_pow_sum] at hM
  exact Nat.pow_right_injective le_rfl hM

open scoped Classical in

theorem index_mackeySubgroup_realFamily (v : {v : InfinitePlace K.1 // v.IsReal})
    (d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom) :
    (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom d.out).index =
      if mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom d.out = ⊤ then 1 else 2 := by
  split_ifs with h
  · rw [h, Subgroup.index_top]
  · rw [eq_bot_of_ne_top_realGal v _ h, Subgroup.index_bot, Nat.card_eq_fintype_card,
      card_realGal_eq_two v.1 v.2]

open scoped Classical in

theorem finrank_mul_card_real_eq_sum_index :
    Module.finrank K.1 L.1 * Nat.card {v : InfinitePlace K.1 // v.IsReal} =
      ∑ p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
          MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr v).toMonoidHom,
        (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1).toMonoidHom p.2.out).index := by
  rw [Fintype.sum_sigma, Finset.sum_congr rfl fun v _ => (finrank_eq_sum_index_mackeySubgroup S hL ιr v).symm,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

open scoped Classical in

theorem sum_index_eq_card_top_add :
    ∑ p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out).index =
      Nat.card (MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) +
        2 * Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
  have htop : ∀ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom //
      mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out).index = 1 := fun p =>
    (index_mackeySubgroup_realFamily S hL ιr p.1.1 p.1.2).trans (if_pos p.2)
  have hlow : ∀ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom //
      ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out).index = 2 := fun p =>
    (index_mackeySubgroup_realFamily S hL ιr p.1.1 p.1.2).trans (if_neg p.2)
  have h := Fintype.sum_subtype_add_sum_subtype (fun p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
    MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom =>
      mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤)
    (fun p => (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1).toMonoidHom p.2.out).index)
  simp only [htop, hlow, Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_eq_nat_card,
    mul_one] at h
  exact h.symm.trans (congrArg₂ (· + ·) rfl (Nat.mul_comm _ _))

theorem count_places_arith {n a a₁ a₂ c₁ c₂ b dK dL NK NL : ℕ} (hK : NK = a₁ + a₂) (hL : NL = c₁ + c₂)
    (h₀ : a = c₁) (h₁ : n * a₁ = a + 2 * b) (h₂ : a₁ + 2 * a₂ = dK) (h₃ : c₁ + 2 * c₂ = dL)
    (h₄ : dK * n = dL) : NL + b = n * NK := by
  subst hK hL h₂ h₃
  rw [h₀] at h₁
  have e : c₁ + 2 * c₂ = n * a₁ + 2 * (n * a₂) := by rw [← h₄]; ring
  rw [mul_add]
  generalize n * a₁ = X at *
  generalize n * a₂ = Y at *
  omega

theorem card_infinitePlace_eq_real_add_complex (F : FiniteSubfield) :
    Nat.card (InfinitePlace F.1) =
        Nat.card {w : InfinitePlace F.1 // w.IsReal} + Nat.card {w : InfinitePlace F.1 // w.IsComplex} ∧
      Nat.card {w : InfinitePlace F.1 // w.IsReal} + 2 * Nat.card {w : InfinitePlace F.1 // w.IsComplex} =
        Module.finrank ℚ F.1 := by
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F.1
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank F.1
  simp only [InfinitePlace.nrRealPlaces, InfinitePlace.nrComplexPlaces, Fintype.card_eq_nat_card] at h1 h2
  exact ⟨h1, h2⟩

theorem card_infinitePlace_add_card :
    Nat.card (InfinitePlace L.1) +
        Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} =
      Module.finrank K.1 L.1 * Nat.card (InfinitePlace K.1) := by
  have htop : Nat.card (MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) =
      Nat.card {w : InfinitePlace L.1 // w.IsReal} :=
    Nat.card_eq_of_bijective (realMemberPlace S ιr hL)
      ⟨realMemberPlace_injective S ιr hL, realMemberPlace_surjective S ιr hL⟩
  have hsum := (finrank_mul_card_real_eq_sum_index S hL ιr).trans (sum_index_eq_card_top_add S hL ιr)
  exact count_places_arith (card_infinitePlace_eq_real_add_complex K).1
    (card_infinitePlace_eq_real_add_complex L).1 htop hsum (card_infinitePlace_eq_real_add_complex K).2
    (card_infinitePlace_eq_real_add_complex L).2 (Module.finrank_mul_finrank ℚ K.1 L.1)

end Count

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

instance isDiscreteRep_res_gsBaseChange_symm
    (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    [IsDiscreteRep B] : IsDiscreteRep (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) :=
  IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom _) B

variable (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
  [IsDiscreteRep B]

theorem gsRealH0Card_coind (v : {v : InfinitePlace K.1 // v.IsReal}) :
    gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
        ιr v =
      ∏ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
        Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom B d.out) 0) :=
  (Nat.card_congr (mackeyCohomologyEquiv (gsOpenSubgroup S hL) (gsRealFamily S ιr v) B 0).toEquiv).trans
    Nat.card_pi

theorem card_cohomology_zero_mackeyRep_of_ne_top (v : {v : InfinitePlace K.1 // v.IsReal})
    (d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom)
    (hd : ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom d.out = ⊤) :
    Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom B d.out) 0) = Nat.card B :=
  card_cohomology_zero_of_forall_eq_one _ fun g => by
    have hb := eq_bot_of_ne_top_realGal v _ hd
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 (hb ▸ g.2))
    subst hg
    exact map_one _

theorem card_cohomology_zero_mackeyRep_top
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) (w : {w : InfinitePlace L.1 // w.IsReal})
    (e : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ (g : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion))
      (hg : p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e g)) :
    Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) =
      gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w := by
  have key : ∀ h : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out,
      (gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w (e h)) =
        mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out h := fun h =>
    (ContinuousMulEquiv.symm_apply_eq _).2 (he h h.2).symm
  have hiff : ∀ b : B,
      (∀ h : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out,
        B.ρ (mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out h) b = b) ↔
      (∀ g' : Gal(AlgebraicClosure w.1.Completion / w.1.Completion),
        B.ρ ((gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w g')) b = b) := by
    intro b
    constructor
    · intro hb g'
      have hm : e.symm g' ∈ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out := (Subgroup.eq_top_iff' _).1 p.2 (e.symm g')
      have h4 : (gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w g') =
          mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out ⟨e.symm g', hm⟩ :=
        (congrArg (fun t => (gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w t))
          (e.apply_symm_apply g').symm).trans (key ⟨e.symm g', hm⟩)
      exact (congrArg (fun t => B.ρ t b) h4).trans (hb ⟨e.symm g', hm⟩)
    · intro hb h
      exact (congrArg (fun t => B.ρ t b) (key h)).symm.trans (hb (e h))
  exact (Nat.card_congr (H0Iso (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out)).toLinearEquiv.toEquiv).trans <|
    (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans
      (Nat.card_congr (H0Iso (Rep.res (gsRealFamily (placesOver S) ιrL w).toMonoidHom
        (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B))).toLinearEquiv.toEquiv).symm

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
  [IsDiscreteRep B]

open scoped Classical in

theorem prod_gsRealH0Card_coind
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (mem : {w : InfinitePlace L.1 // w.IsReal} → MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (hmem : ∀ w, realMemberPlace S ιr hL (mem w) = w)
    (e : ∀ w, Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ w (g : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
      (hg : (mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨(mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e w g)) :
    ∏ v : {v : InfinitePlace K.1 // v.IsReal},
        gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
          ιr v =
      (∏ w : {w : InfinitePlace L.1 // w.IsReal},
          gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w) *
        Nat.card B ^ Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
  have hbij : Function.Bijective mem :=
    ⟨fun w w' h => (hmem w).symm.trans ((congrArg (realMemberPlace S ιr hL) h).trans (hmem w')),
      fun p => ⟨realMemberPlace S ιr hL p, realMemberPlace_injective S ιr hL (hmem _)⟩⟩
  have hlow : ∀ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom //
      ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
      Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) = Nat.card B := fun p =>
    card_cohomology_zero_mackeyRep_of_ne_top S hL ιr B p.1.1 p.1.2 p.2
  have htop : ∏ w : {w : InfinitePlace L.1 // w.IsReal},
        gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w =
      ∏ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
          MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr v).toMonoidHom //
        mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
        Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) :=
    Fintype.prod_equiv (Equiv.ofBijective mem hbij : {w : InfinitePlace L.1 // w.IsReal} ≃
        {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
          MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr v).toMonoidHom //
        mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤}) _ _ fun w =>
      (card_cohomology_zero_mackeyRep_top S hL ιr B ιrL (mem w) w (e w) (he w)).symm
  have hsplit := Fintype.prod_subtype_mul_prod_subtype
    (fun p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
      MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom =>
      mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤)
    (fun p => Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1).toMonoidHom B p.2.out) 0))
  simp only [hlow, Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card] at hsplit
  exact (Finset.prod_congr rfl fun v _ => gsRealH0Card_coind S hL ιr B v).trans <|
    (Fintype.prod_sigma (fun p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
      MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom =>
      Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom B p.2.out) 0))).symm.trans <|
    hsplit.symm.trans (congrArg (· * _) htop.symm)

theorem ratio_coind_arith {χ χ' PK PL nC nB : ℚ} {cK cL b n : ℕ} (hχ : χ = χ') (hC : nC = nB ^ n)
    (hP : PK = PL * nB ^ b) (hN : cL + b = n * cK) (hB : nB ≠ 0) :
    χ * nC ^ cK / PK = χ' * nB ^ cL / PL := by
  subst hχ hC hP
  rw [← pow_mul, ← hN, pow_add, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero _ hB)]

open scoped Classical in

theorem gsEulerRatio_coind_eq_of [Finite B]
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (mem : {w : InfinitePlace L.1 // w.IsReal} → MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (hmem : ∀ w, realMemberPlace S ιr hL (mem w) = w)
    (e : ∀ w, Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ w (g : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
      (hg : (mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨(mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e w g)) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) ιr =
      gsEulerRatio (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL := by
  have hχ := (eulerChar_coind (gsOpenSubgroup S hL) B).trans
    (eulerChar_res_continuousMulEquiv (gsBaseChange S hL).symm B).symm
  have hC : ((Nat.card (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) :
      ℕ) : ℚ) = (Nat.card B : ℚ) ^ Module.finrank K.1 L.1 := by
    exact_mod_cast card_coind_gsOpenSubgroup S hL B
  have hP := prod_gsRealH0Card_coind S hL ιr B ιrL mem hmem e he
  have hPq : (∏ v : {v : InfinitePlace K.1 // v.IsReal},
        (gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
          ιr v : ℚ)) =
      (∏ w : {w : InfinitePlace L.1 // w.IsReal},
          (gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w : ℚ)) *
        (Nat.card B : ℚ) ^ Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
    exact_mod_cast hP
  have hN := card_infinitePlace_add_card S hL ιr
  simp only [Nat.card_eq_fintype_card (α := InfinitePlace K.1), Nat.card_eq_fintype_card (α := InfinitePlace L.1)]
    at hN
  have hB : (Nat.card B : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  exact ratio_coind_arith hχ hC hPq hN hB

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

theorem exists_gsEulerRatio_coind_eq :
    ∃ ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion,
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
        [IsDiscreteRep B] [Finite B],
        gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
            ιr =
          gsEulerRatio (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL := by
  choose mem hmem using realMemberPlace_surjective S ιr hL
  choose ιrL e he using fun w => exists_real_data_of_eq S ιr hL (mem w) w
    ((coe_realMemberPlace S ιr hL (mem w)).symm.trans (congrArg Subtype.val (hmem w)))
  exact ⟨ιrL, fun B _ _ => gsEulerRatio_coind_eq_of S hL ιr B ιrL mem hmem e he⟩

end

end GroundTheory.ProfCoh
end
