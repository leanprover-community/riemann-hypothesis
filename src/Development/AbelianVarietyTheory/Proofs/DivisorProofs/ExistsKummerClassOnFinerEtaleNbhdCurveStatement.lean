import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away_of_isUnit_mod : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B),
    IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) →
    IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  intro B A' _ _ _ f s hA hs
  obtain ⟨hEt, h2, h3⟩ := hA
  obtain ⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s := ⟨_, rfl⟩
  rw [← hσ]

  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by
    obtain ⟨v, hv⟩ := hs.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f} := by
    intro n
    obtain ⟨c, hc⟩ := (sub_dvd_pow_sub_pow (s * t) 1 n)
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ ht
  haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ
  haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a', m⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) x
    have hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a' := by
      rw [← hx]; exact IsLocalization.mk'_spec _ _ _
    obtain ⟨n, hn⟩ := m.2
    rw [← hn] at hxs
    obtain ⟨b, hb⟩ := h2 (a' * algebraMap B A' t ^ n)
    refine ⟨b, ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hpow n)
    have hc' := congrArg (algebraMap A' (Localization.Away σ)) hc
    have hv' := congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩
    simp only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one,
      ← hσ] at hxs hc' hv' ⊢
    linear_combination hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨⟨c, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) y
    have hys := IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)
    have key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) =
        algebraMap A' (Localization.Away σ) (c * algebraMap B A' f) := by
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]
      simp only at hys
      rw [← hys]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key
    have hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨σ ^ k * c, ?_⟩
      simp only at hk
      rw [map_mul, map_pow, ← hσ, pow_add]
      linear_combination -hk
    have h1 := h3 _ hmem
    have h4 := hpow (k + n)
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h4
    rw [Ideal.mem_span_singleton']
    refine ⟨t ^ (k + n) * p - a * q, ?_⟩
    linear_combination t ^ (k + n) * hp - a * hq

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B), IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) → IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (exact GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.PicLoc

open Algebra in

theorem finite_maximalSpectrum_of_field (B : Type) [CommRing B] (S : Submonoid B) (K : Type)
    [Field K] [Algebra B K] [IsLocalization S K] (A' : Type) [CommRing A'] [Algebra B A']
    [FormallyUnramified B A'] [FiniteType B A'] (R : Type) [CommRing R] [Algebra A' R]
    [IsLocalization (algebraMapSubmonoid A' S) R] [Algebra B R] [IsScalarTower B A' R] :
    Finite (MaximalSpectrum R) := by
  letI : Algebra K R := localizationAlgebra S A'
  haveI : IsScalarTower B K R := isScalarTower_localizationAlgebra S A'
  haveI : FormallyEtale A' R := FormallyEtale.of_isLocalization (algebraMapSubmonoid A' S)
  haveI : FormallyUnramified B R := FormallyUnramified.comp B A' R
  haveI : FormallyUnramified K R := FormallyUnramified.of_restrictScalars B K R
  haveI : EssFiniteType A' R := EssFiniteType.of_isLocalization R (algebraMapSubmonoid A' S)
  haveI : EssFiniteType B R := EssFiniteType.comp B A' R
  haveI : EssFiniteType K R := EssFiniteType.of_comp B K R
  haveI : Module.Finite K R := FormallyUnramified.finite_of_free K R
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  infer_instance

theorem isField_localization (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (h0 : (0 : B) ∉ (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f) :
    IsField (Localization ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)) := by
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  haveI : IsDomain (Localization S) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors h0)

  have hbot : ∀ Q : Ideal (Localization S), Q.IsPrime → Q = ⊥ := by
    intro Q hQ
    set p := Q.comap (algebraMap B (Localization S)) with hp
    haveI : p.IsPrime := Ideal.comap_isPrime _ Q
    have hdisj : ∀ s ∈ S, s ∉ p := by
      intro s hs hsp
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp
        (IsLocalization.map_units (Localization S) ⟨s, hs⟩))
    have hp0 : p = ⊥ := by
      by_contra hne
      have hmax : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
      have hf : f ∉ p := fun h => hdisj f (Submonoid.mem_sup_right (Submonoid.mem_powers f)) h
      have htop : p ⊔ Ideal.span {f} = ⊤ := by
        refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hf ?_)
        rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : B) ∈ p ⊔ Ideal.span {f})
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a) := by
        have hb0 : Ideal.Quotient.mk (Ideal.span {f}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
        have : Ideal.Quotient.mk (Ideal.span {f}) a = 1 := by
          rw [← map_one (Ideal.Quotient.mk (Ideal.span {f})), ← hab, map_add, hb0, add_zero]
        rw [this]; exact isUnit_one
      exact hdisj a (Submonoid.mem_sup_left hunit) ha
    rw [← IsLocalization.map_under S (Localization S) Q]
    change Ideal.map _ p = ⊥
    rw [hp0, Ideal.map_bot]
  haveI : Ring.KrullDimLE 0 (Localization S) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (Localization S)) bot_ne_top
    rw [hbot I hI, ← hbot m hm.isPrime]
    exact hm
  exact Ring.KrullDimLE.isField_of_isDomain

end GlobalTheory.PicLoc

namespace GlobalTheory.PicLoc

theorem subsingleton_pic_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  intro B _ _ f A' _ _ _
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  suffices Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) from
    inferInstance
  by_cases h0 : (0 : B) ∈ S
  · have h0' : (0 : A') ∈ Algebra.algebraMapSubmonoid A' S :=
      Submonoid.mem_map.2 ⟨0, h0, map_zero _⟩
    letI := IsLocalization.uniqueOfZeroMem
      (S := Localization (Algebra.algebraMapSubmonoid A' S)) h0'
    haveI : IsEmpty (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) :=
      ⟨fun m => m.isMaximal.ne_top (by
        rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Localization _) 0]
        exact m.asIdeal.zero_mem)⟩
    infer_instance
  · letI : Field (Localization S) := (isField_localization B f h0).toField
    exact finite_maximalSpectrum_of_field B S (Localization S) A'
      (Localization (Algebra.algebraMapSubmonoid A' S))

end GlobalTheory.PicLoc
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  first | (exact @GlobalTheory.PicLoc.subsingleton_pic_localization) | (exact GlobalTheory.PicLoc.subsingleton_pic_localization) | (intros; apply GlobalTheory.PicLoc.subsingleton_pic_localization <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AwayCont

variable {A : Type} [CommRing A] (M : Submonoid A)

structure Idx (M : Submonoid A) where

  val : A
  mem : val ∈ M

instance : Preorder (Idx M) where
  le a b := ∃ t ∈ M, b.val = a.val * t
  le_refl a := ⟨1, M.one_mem, by simp⟩
  le_trans a b c := by
    rintro ⟨t, ht, h1⟩ ⟨s, hs, h2⟩
    exact ⟨t * s, M.mul_mem ht hs, by rw [h2, h1, mul_assoc]⟩

instance : IsDirected (Idx M) (· ≤ ·) where
  directed a b := ⟨⟨a.val * b.val, M.mul_mem a.mem b.mem⟩, ⟨b.val, b.mem, rfl⟩, ⟨a.val, a.mem, mul_comm _ _⟩⟩

instance : Nonempty (Idx M) := ⟨⟨1, M.one_mem⟩⟩

theorem isUnit_of_le {a b : Idx M} (h : a ≤ b) :
    IsUnit (algebraMap A (Localization.Away b.val) a.val) := by
  obtain ⟨t, -, ht⟩ := h
  have hb := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val
  rw [show algebraMap A (Localization.Away b.val) b.val =
      algebraMap A _ a.val * algebraMap A _ t by rw [← map_mul, ← ht]] at hb
  exact isUnit_of_mul_isUnit_left hb

def trans {a b : Idx M} (h : a ≤ b) : Localization.Away a.val →+* Localization.Away b.val :=
  IsLocalization.Away.lift a.val (isUnit_of_le M h)

theorem trans_comp {a b : Idx M} (h : a ≤ b) :
    (trans M h).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.Away.lift_comp _ _

theorem ext_away {a : A} {P : Type} [CommRing P] {f g : Localization.Away a →+* P}
    (hf : f.comp (algebraMap A _) = g.comp (algebraMap A _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) hf

def diag : Idx M ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (trans M h.le)
  map_id a := by
    ext1; apply ext_away
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    rw [trans_comp]; rfl
  map_comp {a b c} f g := by
    ext1; apply ext_away
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, trans_comp, trans_comp, trans_comp]

def toLoc (a : Idx M) : Localization.Away a.val →+* Localization M :=
  IsLocalization.Away.lift a.val (IsLocalization.map_units (Localization M) (⟨a.val, a.mem⟩ : M))

theorem toLoc_comp (a : Idx M) : (toLoc M a).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.Away.lift_comp _ _

def cocone : Cocone (diag M) where
  pt := CommRingCat.of (Localization M)
  ι := { app := fun a => CommRingCat.ofHom (toLoc M a)
         naturality := fun a b h => by
           ext1; apply ext_away
           simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, diag, Functor.const_obj_map,
             CommRingCat.hom_id, RingHom.id_comp]
           rw [RingHom.comp_assoc, trans_comp, toLoc_comp]
           exact (toLoc_comp M a).symm }

end GlobalTheory.EtC.AwayCont
end

noncomputable section

namespace GlobalTheory.EtC.AwayCont

variable {A : Type} [CommRing A] (M : Submonoid A)

theorem toLoc_trans {a b : Idx M} (h : a ≤ b) : (toLoc M b).comp (trans M h) = toLoc M a :=
  ext_away (by rw [RingHom.comp_assoc, trans_comp, toLoc_comp, toLoc_comp])

theorem trans_trans {a b c : Idx M} (h : a ≤ b) (h' : b ≤ c) :
    (trans M h').comp (trans M h) = trans M (h.trans h') :=
  ext_away (by rw [RingHom.comp_assoc, trans_comp, trans_comp, trans_comp])

theorem kill (a : Idx M) (z : Localization.Away a.val) (hz : toLoc M a z = 0) :
    ∃ (b : Idx M) (h : a ≤ b), trans M h z = 0 := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers a.val) z
  have h1 : algebraMap A (Localization M) x = 0 := by
    have := congrArg (toLoc M a) hs
    rw [map_mul, hz, zero_mul, ← RingHom.comp_apply, toLoc_comp] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M (Localization M) x).mp h1
  let b : Idx M := ⟨a.val * c, M.mul_mem a.mem c.2⟩
  have hab : a ≤ b := ⟨c, c.2, rfl⟩
  refine ⟨b, hab, ?_⟩
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val
  have hb : b.val = a.val * c := rfl
  rw [hb, map_mul] at hu
  have hua : IsUnit (algebraMap A (Localization.Away b.val) a.val) := isUnit_of_mul_isUnit_left hu
  have huc : IsUnit (algebraMap A (Localization.Away b.val) c) := isUnit_of_mul_isUnit_right hu
  have hx : algebraMap A (Localization.Away b.val) x = 0 := by
    have : algebraMap A (Localization.Away b.val) c * algebraMap A (Localization.Away b.val) x = 0 := by
      rw [← map_mul, hc, map_zero]
    exact (huc.mul_right_eq_zero).mp this
  have hs' := congrArg (trans M hab) hs
  rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, trans_comp, hx] at hs'
  obtain ⟨k, hk⟩ := s.2
  have hus : IsUnit (algebraMap A (Localization.Away b.val) (s : A)) := by
    rw [← hk, map_pow]; exact hua.pow k
  exact (hus.mul_left_eq_zero).mp hs'

def isColimit : IsColimit (cocone M) := by
  haveI : ReflectsColimitsOfShape (Idx M) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone M)) ?_ ?_)
  · intro (x : Localization M)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    refine ⟨⟨s.1, s.2⟩, IsLocalization.mk' (Localization.Away s.1) a
      (⟨s.1, Submonoid.mem_powers _⟩ : Submonoid.powers s.1), ?_⟩
    show _ = toLoc M ⟨s.1, s.2⟩ _
    rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq]
    have e1 := RingHom.congr_fun (toLoc_comp M ⟨s.1, s.2⟩) s.1
    have e2 := RingHom.congr_fun (toLoc_comp M ⟨s.1, s.2⟩) a
    simp only [RingHom.comp_apply] at e1 e2
    rw [← e1, ← map_mul, IsLocalization.mk'_spec, e2]
  · intro i j (xi : Localization.Away i.val) (xj : Localization.Away j.val) h
    change toLoc M i xi = toLoc M j xj at h
    let k : Idx M := ⟨i.val * j.val, M.mul_mem i.mem j.mem⟩
    have hik : i ≤ k := ⟨j.val, j.mem, rfl⟩
    have hjk : j ≤ k := ⟨i.val, i.mem, mul_comm _ _⟩
    have hz : toLoc M k (trans M hik xi - trans M hjk xj) = 0 := by
      have e1 := RingHom.congr_fun (toLoc_trans M hik) xi
      have e2 := RingHom.congr_fun (toLoc_trans M hjk) xj
      simp only [RingHom.comp_apply] at e1 e2
      rw [map_sub, e1, e2, h, sub_self]
    obtain ⟨b, hkb, hb⟩ := kill M k _ hz
    refine ⟨b, homOfLE (hik.trans hkb), homOfLE (hjk.trans hkb), ?_⟩
    show trans M (hik.trans hkb) xi = trans M (hjk.trans hkb) xj
    rw [← trans_trans M hik hkb, ← trans_trans M hjk hkb, RingHom.comp_apply, RingHom.comp_apply,
      ← sub_eq_zero, ← map_sub]
    exact hb

end GlobalTheory.EtC.AwayCont
end

namespace GlobalTheory.EtC.AwayCont

theorem kill_of_loc : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) →
    ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M,
    φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 →
    ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'),
      ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  intro hB q A _ M n i hq m hm y φ hφ hy
  let a : Idx M := ⟨m, hm⟩
  have hq' : IsUnit ((q : ℕ) : (diag M).obj a) := by
    have h0 : IsUnit ((q : ℕ) : Localization.Away m) := by
      simpa using hq.map (algebraMap A (Localization.Away m))
    exact h0
  have hφ' : ((cocone M).ι.app a).hom = φ := by
    show toLoc M a = φ
    exact ext_away (by rw [hφ]; exact toLoc_comp M a)
  have hy' : pull _ (spMap ((cocone M).ι.app a).hom) _ _ y = 0 := by
    rw [hφ']; exact hy
  obtain ⟨⟨k1, hk1⟩, f, hk⟩ := (hB q (diag M) (cocone M) (isColimit M) n i).2 a y hq' hy'
  obtain ⟨t, ht, hkt⟩ := f.le
  change k1 = m * t at hkt
  subst hkt
  refine ⟨t, ht, fun ψ hψ => ?_⟩
  have hψ' : ((diag M).map f).hom = ψ := by
    show trans M f.le = ψ
    exact ext_away (by rw [hψ]; exact trans_comp M f.le)
  rw [← hψ']
  exact hk

end GlobalTheory.EtC.AwayCont
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) → ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 → ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'), ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.AwayCont.kill_of_loc) | (exact GlobalTheory.EtC.AwayCont.kill_of_loc) | (intros; apply GlobalTheory.EtC.AwayCont.kill_of_loc <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem units_localization_descend_away (A : Type) [CommRing A] (M : Submonoid A)
    (u : (Localization M)ˣ) :
    ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M,
      φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  obtain ⟨⟨a, m₁⟩, ha⟩ := IsLocalization.mk'_surjective M (u : Localization M)
  obtain ⟨⟨b, m₂⟩, hb⟩ := IsLocalization.mk'_surjective M ((u⁻¹ : (Localization M)ˣ) : Localization M)
  simp only at ha hb
  have hprod : IsLocalization.mk' (Localization M) (a * b) (m₁ * m₂) = 1 := by
    rw [IsLocalization.mk'_mul, ha, hb]; simp
  have h1 : algebraMap A (Localization M) (a * b) = algebraMap A (Localization M) ((m₁ * m₂ : M) : A) := by
    have := IsLocalization.mk'_spec (Localization M) (a * b) (m₁ * m₂)
    rw [hprod, one_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
  set m : A := (m₁ : A) * m₂ * c with hm
  have hmM : m ∈ M := M.mul_mem (M.mul_mem m₁.2 m₂.2) c.2
  have hc' : (c : A) * (a * b) = (c : A) * ((m₁ : A) * m₂) := by
    simpa [Submonoid.coe_mul] using hc
  let s := IsLocalization.Away.invSelf (S := Localization.Away m) m
  have hs : algebraMap A (Localization.Away m) m * s = 1 := IsLocalization.Away.mul_invSelf m
  let x : Localization.Away m := algebraMap A _ (a * (m₂ * c)) * s
  let y : Localization.Away m := algebraMap A _ (b * (m₁ * c)) * s
  have hxy : x * y = 1 := by
    have e : a * (m₂ * c) * (b * (m₁ * c)) = m * m := by
      rw [hm]; linear_combination ((m₁ : A) * m₂ * c) * hc'
    calc x * y = algebraMap A _ (a * (m₂ * c) * (b * (m₁ * c))) * s * s := by
          simp only [x, y, map_mul]; ring
      _ = (algebraMap A (Localization.Away m) m * s) * (algebraMap A (Localization.Away m) m * s) := by
          rw [e, map_mul]; ring
      _ = 1 := by rw [hs, one_mul]
  refine ⟨m, hmM, ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  intro φ hφ
  have hφa : ∀ r : A, φ (algebraMap A _ r) = algebraMap A (Localization M) r := fun r =>
    congrArg (fun f : A →+* Localization M => f r) hφ
  apply Units.ext
  show φ x = (u : Localization M)
  have hu : (u : Localization M) * algebraMap A _ (m₁ : A) = algebraMap A _ a := by
    rw [← ha]; exact IsLocalization.mk'_spec _ _ _
  have hφs : algebraMap A (Localization M) m * φ s = 1 := by
    rw [← hφa, ← map_mul, hs, map_one]
  have hx : φ x * algebraMap A (Localization M) (m₁ : A) = algebraMap A _ a := by
    have : φ x * algebraMap A (Localization M) (m₁ : A)
        = algebraMap A (Localization M) a * (algebraMap A (Localization M) m * φ s) := by
      simp only [x, map_mul, hφa, hm]; ring
    rw [this, hφs, mul_one]
  have hunit : IsUnit (algebraMap A (Localization M) (m₁ : A)) := IsLocalization.map_units _ m₁
  exact hunit.mul_left_inj.1 (hx.trans hu.symm)

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_away_unit_map_eq : ∀ (A : Type) [CommRing A] (M : Submonoid A) (u : (Localization M)ˣ), ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  first | (exact @GlobalTheory.units_localization_descend_away) | (exact GlobalTheory.units_localization_descend_away) | (intros; apply GlobalTheory.units_localization_descend_away <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KummerLoc

noncomputable abbrev gU (R : Type) [CommRing R] : Rˣ →* (Γ(Spec (CommRingCat.of R), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom

theorem pull_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    {q : ℕ} {n i : ℤ} (x : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp φ)) _ _ x = pull _ (spMap ψ) _ _ (pull _ (spMap φ) _ _ x) := by
  rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp]; rfl

theorem pull_kum_gU (hnat : DivisorNaturality) (q : ℕ) [NeZero q] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hq : IsUnit (q : R)) (v : Rˣ) :
    pull _ (spMap φ) _ _ (kum q (gU R v)) = kum q (gU S (Units.map φ.toMonoidHom v)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rw [(hnat q).2.2.2 _ _ hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom (v : R)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simpa using h2.symm

set_option maxHeartbeats 1000000 in

theorem exists_kummer_on_finer_nbhd : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  intro q _ k B _ _ _ _ _ _ hq f _ A' _ _ hA' w
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hqA : IsUnit (q : A') := by simpa using hqB.map (algebraMap B A')
  haveI : Algebra.Etale B A' := hA'.1
  set SB : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
    (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hSB
  set M : Submonoid A' := Algebra.algebraMapSubmonoid A' SB with hM
  have hfM : (algebraMap B A' f) ∈ M := ⟨f, Submonoid.mem_sup_right (Submonoid.mem_powers f), rfl⟩
  let φf : Localization.Away (algebraMap B A' f) →+* Localization M :=
    IsLocalization.Away.lift (algebraMap B A' f) (IsLocalization.map_units (Localization M) (⟨(algebraMap B A' f), hfM⟩ : M))
  have hφf : φf.comp (algebraMap A' _) = algebraMap A' (Localization M) := IsLocalization.Away.lift_comp _ _
  haveI := GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo B f A'
  have hqL : IsUnit (q : Localization M) := by simpa using hqA.map (algebraMap A' (Localization M))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (Localization M) hqL (fun c _ => Subsingleton.elim _ _) (pull _ (spMap φf) _ _ w)
  let u₀ : (Localization M)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization M))).hom.hom.toMonoidHom u
  have hu₀ : gU _ u₀ = u := by ext; simp [u₀]
  obtain ⟨m₀, hm₀, v, hv⟩ := GlobalTheory.T.exists_away_unit_map_eq A' M u₀
  have hm₁ : (algebraMap B A' f) * m₀ ∈ M := M.mul_mem hfM hm₀
  have hunit1 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀)) ((algebraMap B A' f) * m₀)) := IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (algebraMap B A' f) →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift (algebraMap B A' f) (isUnit_of_mul_isUnit_left (by simpa using hunit1))
  let β : Localization.Away m₀ →+* Localization.Away ((algebraMap B A' f) * m₀) :=
    IsLocalization.Away.lift m₀ (isUnit_of_mul_isUnit_right (by simpa using hunit1))
  let φ₁ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization M :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (IsLocalization.map_units (Localization M) (⟨_, hm₁⟩ : M))
  have hα : α.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hβ : β.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hφ₁ : φ₁.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₀ : IsUnit (q : Localization.Away m₀) := by simpa using hqA.map (algebraMap A' _)
  have hqm₁ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀)) := by simpa using hqA.map (algebraMap A' _)
  have hnat := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  set y := pull _ (spMap α) _ _ w - kum q (gU _ (Units.map β.toMonoidHom v)) with hy
  have hy0 : pull _ (spMap φ₁) _ _ y = 0 := by
    rw [hy, map_sub, ← pull_spMap_comp, pull_kum_gU hnat q _ hqm₁]
    have e1 : φ₁.comp α = φf := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) (by rw [RingHom.comp_assoc, hα, hφ₁, hφf])
    have e2 : Units.map φ₁.toMonoidHom (Units.map β.toMonoidHom v) = u₀ := by
      rw [← hv (φ₁.comp β) (by rw [RingHom.comp_assoc, hβ, hφ₁])]; ext; rfl
    rw [e1, e2, hu₀, hu, sub_self]
  obtain ⟨m', hm', hψ⟩ := GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q A' M 1 1 hqA ((algebraMap B A' f) * m₀) hm₁ y φ₁ hφ₁ hy0
  obtain ⟨b, hb, hbm⟩ := M.mul_mem hm₁ hm'
  obtain ⟨s, hs, t, ht, rfl⟩ := Submonoid.mem_sup.1 hb
  obtain ⟨n, rfl⟩ := ht
  have hs' : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) := hs
  refine ⟨Localization.Away (algebraMap B A' s), inferInstance, inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' B A' f s hA' hs', ?_⟩
  set A₂ := Localization.Away (algebraMap B A' s)
  set g : A' →+* Localization.Away (algebraMap B A₂ f) := (algebraMap A₂ _).comp (algebraMap A' A₂) with hg
  have hgu : IsUnit (g ((algebraMap B A' f) * m₀ * m')) := by
    rw [← hbm]
    simp only [map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · exact (IsLocalization.Away.algebraMap_isUnit (algebraMap B A' s)).map (algebraMap A₂ _)
    · have : g (algebraMap B A' f) = algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) := by
        rw [hg, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂ f]
      rw [this]
      exact IsLocalization.Away.algebraMap_isUnit _
  let χ : Localization.Away ((algebraMap B A' f) * m₀ * m') →+* Localization.Away (algebraMap B A₂ f) :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀ * m') hgu
  have hχ : χ.comp (algebraMap A' _) = g := IsLocalization.Away.lift_comp _ _
  have hunit2 : IsUnit (algebraMap A' (Localization.Away ((algebraMap B A' f) * m₀ * m')) ((algebraMap B A' f) * m₀ * m')) :=
    IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away ((algebraMap B A' f) * m₀) →+* Localization.Away ((algebraMap B A' f) * m₀ * m') :=
    IsLocalization.Away.lift ((algebraMap B A' f) * m₀) (isUnit_of_mul_isUnit_left (by simpa using hunit2))
  have hψc : ψ.comp (algebraMap A' _) = algebraMap A' _ := IsLocalization.Away.lift_comp _ _
  have hqm₂ : IsUnit (q : Localization.Away ((algebraMap B A' f) * m₀ * m')) := by simpa using hqA.map (algebraMap A' _)
  clear_value χ ψ β α
  refine ⟨gU _ (Units.map (χ.comp (ψ.comp β)).toMonoidHom v), fun φ hφ => ?_⟩
  have e3 : φ = χ.comp (ψ.comp α) := IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f))
    (by rw [hφ, RingHom.comp_assoc, RingHom.comp_assoc, hα, hψc, hχ])
  have hw : pull _ (spMap α) _ _ w = y + kum q (gU _ (Units.map β.toMonoidHom v)) := by
    rw [hy, sub_add_cancel]
  subst e3
  rw [pull_spMap_comp, pull_spMap_comp, hw]
  have hψy := hψ ψ hψc
  rw [map_add (pull _ (spMap ψ) _ _)]
  rw [hψy, zero_add]
  rw [pull_kum_gU hnat q ψ hqm₁]
  have key : pull _ (spMap χ) _ _ (kum q (gU _ (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) =
      kum q (gU _ (Units.map χ.toMonoidHom (Units.map ψ.toMonoidHom (Units.map β.toMonoidHom v)))) :=
    pull_kum_gU hnat q χ hqm₂ _
  refine key.trans ?_
  exact congrArg (kum q) (congrArg (gU _) (Units.ext rfl))

end GlobalTheory.EtC.KummerLoc

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  first | (exact @GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (exact GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (intros; apply GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd <;> assumption)
end
