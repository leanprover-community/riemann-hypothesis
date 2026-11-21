import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OrdModEqLengthQuotSup
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

def ReducedCutLength.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime],
    I.IsRadical → (∀ p ∈ I.minimalPrimes, x ∉ p) → Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      ∑ᶠ p ∈ I.minimalPrimes, Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (p ⊔ Ideal.span {x})))

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

namespace ReducedCut

open IsLocalRing

theorem length_quot_map_mk {L : Type*} [CommRing L] (J₀ J : Ideal L) :
    Module.length (L ⧸ J₀) ((L ⧸ J₀) ⧸ J.map (Ideal.Quotient.mk J₀)) =
      Module.length L (L ⧸ (J₀ ⊔ J)) := by
  rw [← Module.length_eq_of_surjective (S := L) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ L J₀ J).toLinearEquiv.length_eq

theorem length_localizedModule_eq_one {B : Type*} [CommRing B] (hB : (⊥ : Ideal B).IsRadical)
    (p : Ideal B) [p.IsPrime] (hp : p ∈ (⊥ : Ideal B).minimalPrimes) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl B) = 1 := by
  have h1 := localMult_eq_one_of_isRadical hB hp
  unfold localMult at h1
  rw [dif_pos ‹p.IsPrime›, Ideal.map_bot] at h1
  have h2 : Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (⊥ : Ideal (Localization.AtPrime p))) = 1 := by
    have hne : Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ (⊥ : Ideal (Localization.AtPrime p))) ≠ ⊤ :=
      fun h => by rw [h] at h1; simp at h1
    rw [← ENat.natCast_toNat hne, h1]
    rfl
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e1 := (IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl B)
    (Algebra.linearMap B (Localization.AtPrime p))).restrictScalars (Localization.AtPrime p)
  rw [e1.length_eq, ← h2]
  exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq.symm

variable {T : Type} [CommRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime]

local notation "𝓛" => Localization.AtPrime Q
local notation "ι" => algebraMap T (Localization.AtPrime Q)
local notation "𝓘" => Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "𝓐" => Localization.AtPrime Q ⧸ Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "π" => Ideal.Quotient.mk (Ideal.map (algebraMap T (Localization.AtPrime Q)) I)

theorem isRadical_map (hI : I.IsRadical) : (𝓘).IsRadical := by
  show (𝓘).radical ≤ _
  rw [← IsLocalization.map_radical Q.primeCompl (Localization.AtPrime Q) I, hI.radical]

theorem mem_minimalPrimes_map_iff (q : Ideal 𝓛) :
    q ∈ (𝓘).minimalPrimes ↔ q.comap ι ∈ I.minimalPrimes := by
  rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q) I]
  rfl

def under (p : PrimeSpectrum 𝓐) : Ideal T := (p.asIdeal.comap π).comap ι

theorem map_map_under (p : PrimeSpectrum 𝓐) : ((under I Q p).map ι).map π = p.asIdeal := by
  rw [show (under I Q p).map ι = p.asIdeal.comap π from
      IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) _,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem le_comap_mk (p : Ideal 𝓐) : 𝓘 ≤ p.comap π := by
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact p.zero_mem

theorem isRadical_bot (hI : I.IsRadical) : (⊥ : Ideal 𝓐).IsRadical := by
  intro a ha
  obtain ⟨n, hn⟩ := ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact isRadical_map I Q hI ⟨n, hn⟩

theorem length_eq_finsum [IsNoetherianRing T] (hI : I.IsRadical) (hx : ∀ p ∈ I.minimalPrimes, x ∉ p)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes) :
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      ∑ᶠ p ∈ I.minimalPrimes, Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (p ⊔ Ideal.span {x}))) := by
  classical
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hILrad := isRadical_map I Q hI
  have hsup : (I ⊔ Ideal.span {x}).map (algebraMap T (Localization.AtPrime Q)) =
      I.map (algebraMap T (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap T (Localization.AtPrime Q) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : maximalIdeal (Localization.AtPrime Q) ∈
      (I.map (algebraMap T (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap T (Localization.AtPrime Q) x}).minimalPrimes := by
    rw [← hsup, IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q),
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hQ
  have hILtop : I.map (algebraMap T (Localization.AtPrime Q)) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top
      (top_le_iff.mp (h ▸ (le_sup_left.trans hmax.1.2)))
  have : Nontrivial (Localization.AtPrime Q ⧸ I.map (algebraMap T (Localization.AtPrime Q))) :=
    Ideal.Quotient.nontrivial_iff.mpr hILtop
  have : IsLocalRing (Localization.AtPrime Q ⧸ I.map (algebraMap T (Localization.AtPrime Q))) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmaxc : (maximalIdeal 𝓐).comap π = maximalIdeal 𝓛 :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmaxA : (maximalIdeal 𝓛).map π = maximalIdeal 𝓐 := by
    rw [← hmaxc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

  have hxq : ∀ q ∈ (𝓘).minimalPrimes, ι x ∉ q := fun q hq hxq =>
    hx _ ((mem_minimalPrimes_map_iff I Q q).mp hq) hxq

  have hcomapMin : ∀ p ∈ (⊥ : Ideal 𝓐).minimalPrimes, p.comap π ∈ (𝓘).minimalPrimes := by
    intro p hp
    have h := Ideal.minimalPrimes_comap_of_surjective Ideal.Quotient.mk_surjective hp
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
  have hyp : ∀ p ∈ (⊥ : Ideal 𝓐).minimalPrimes, π (ι x) ∉ p :=
    fun p hp h => hxq _ (hcomapMin p hp) (Ideal.mem_comap.mpr h)
  have hyM : π (ι x) ∈ maximalIdeal 𝓐 := by
    rw [← hmaxA]
    exact Ideal.mem_map_of_mem _ (le_sup_right.trans hmax.1.2 (Ideal.mem_span_singleton_self _))

  have hdim : ringKrullDim 𝓐 = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hmaxA]
      exact_mod_cast Ideal.map_height_le_one_of_mem_minimalPrimes hmax
    · obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal 𝓐) ≤ maximalIdeal 𝓐)
      have : p.IsPrime := hp.1.1
      rw [ringKrullDim, Order.one_le_krullDim_iff]
      refine ⟨⟨p, this⟩, ⟨maximalIdeal 𝓐, (maximalIdeal.isMaximal 𝓐).isPrime⟩, ?_⟩
      refine lt_of_le_of_ne (le_maximalIdeal this.ne_top) fun h => hyp p hp ?_
      have h' : p = maximalIdeal 𝓐 := congrArg PrimeSpectrum.asIdeal h
      rw [h']
      exact hyM

  have hinj : ∀ a : 𝓐, π (ι x) * a = 0 → a = 0 := by
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hILrad ?_
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun q hq =>
      ((hq.1.1).mem_or_mem (hq.1.2 ha)).resolve_left (hxq q hq)
  have htors : Module.length 𝓐 (Submodule.torsionBy 𝓐 𝓐 (π (ι x))) = 0 := by
    rw [Module.length_eq_zero_iff]
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [hinj a.1 (by simpa using (Submodule.mem_torsionBy_iff _ _).mp a.2),
      hinj b.1 (by simpa using (Submodule.mem_torsionBy_iff _ _).mp b.2)]
  have hann : Module.annihilator 𝓐 𝓐 = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hspan : (Ideal.span {π (ι x)} • ⊤ : Submodule 𝓐 𝓐) = Ideal.span {π (ι x)} := by
    show Ideal.span {π (ι x)} * ⊤ = _
    exact Ideal.mul_top _

  have hL : Module.length 𝓛 (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      Module.length 𝓐 (𝓐 ⧸ Ideal.span {π (ι x)}) := by
    rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, hsup, ← length_quot_map_mk,
      Ideal.map_span, Set.image_singleton]
  have hfin := NumbersDVR.length_localizedQuot_ne_top _ Q hQ
  have hC := NumbersDVR.NumbersBirationalInvariance.proof 𝓐 𝓐 (π (ι x)) hdim (by rw [hspan, ← hL]; exact hfin)
  rw [hspan, htors, zero_add, hann] at hC
  rw [hL, hC]

  have hterm : ∀ p : PrimeSpectrum 𝓐, p.asIdeal ∈ (⊥ : Ideal 𝓐).minimalPrimes →
      Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl 𝓐) *
          Module.length 𝓐 (𝓐 ⧸ (p.asIdeal ⊔ Ideal.span {π (ι x)})) =
        Module.length 𝓛 (LocalizedModule Q.primeCompl (T ⧸ (under I Q p ⊔ Ideal.span {x}))) := by
    intro p hp
    rw [length_localizedModule_eq_one (isRadical_bot I Q hI) p.asIdeal hp, one_mul,
      ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton,
      show (under I Q p).map ι = p.asIdeal.comap π from
        IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) _]
    have hpeq : p.asIdeal ⊔ Ideal.span {π (ι x)} =
        (p.asIdeal.comap π ⊔ Ideal.span {ι x}).map π := by
      rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.map_span,
        Set.image_singleton]
    rw [hpeq, length_quot_map_mk, ← sup_assoc, sup_eq_right.mpr (le_comap_mk I Q p.asIdeal)]
  rw [finsum_congr fun p => finsum_congr fun hp => hterm p hp.1]

  have hbij : Set.BijOn (under I Q)
      {p : PrimeSpectrum 𝓐 | p.asIdeal ∈ (⊥ : Ideal 𝓐).minimalPrimes ∧ p.asIdeal ≠ maximalIdeal 𝓐}
      {P | P ∈ I.minimalPrimes ∧ P ≤ Q} := by
    refine ⟨fun p hp => ⟨(mem_minimalPrimes_map_iff I Q _).mp (hcomapMin p.asIdeal hp.1), ?_⟩,
      fun p1 _ p2 _ h => PrimeSpectrum.ext ?_, fun P hP => ?_⟩
    · have h1 : p.asIdeal.comap π ≤ maximalIdeal 𝓛 := by
        rw [← hmaxc]
        exact Ideal.comap_mono (le_maximalIdeal p.isPrime.ne_top)
      exact (Ideal.comap_mono h1).trans Localization.AtPrime.under_maximalIdeal.le
    · rw [← map_map_under I Q p1, ← map_map_under I Q p2, h]
    · obtain ⟨hPmin, hPQ⟩ := hP
      have : P.IsPrime := hPmin.1.1
      have hdisj : Disjoint (Q.primeCompl : Set T) P :=
        Set.disjoint_left.mpr fun a ha haP => ha (hPQ haP)
      have hqc : (P.map ι).comap ι = P :=
        IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) this hdisj
      have hqmin : P.map ι ∈ (𝓘).minimalPrimes := by
        rw [mem_minimalPrimes_map_iff, hqc]
        exact hPmin
      have hpmin : (P.map ι).map π ∈ (⊥ : Ideal 𝓐).minimalPrimes := by
        have h := Ideal.minimalPrimes_map_of_surjective (Ideal.Quotient.mk_surjective (I := 𝓘)) (𝓘)
        rw [Ideal.map_quotient_self, Ideal.mk_ker, sup_idem] at h
        rw [h]
        exact ⟨_, hqmin, rfl⟩
      have : ((P.map ι).map π).IsPrime := hpmin.1.1
      refine ⟨⟨_, this⟩, ⟨hpmin, fun h => hyp _ hpmin (by rw [show (P.map ι).map π = maximalIdeal 𝓐 from h]; exact hyM)⟩, ?_⟩
      show (((P.map ι).map π).comap π).comap ι = P
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hqmin.1.2, hqc]
  refine (finsum_mem_eq_of_bijOn (under I Q) hbij
    (g := fun P => Module.length 𝓛 (LocalizedModule Q.primeCompl (T ⧸ (P ⊔ Ideal.span {x}))))
    fun _ _ => rfl).trans ?_

  refine finsum_mem_inter_support_eq' _ _ _ fun P hP => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  by_contra hPQ
  exact Function.mem_support.mp hP (Module.length_eq_zero_iff.mpr
    (NumbersDVR.localizedQuot_subsingleton_of_not_le _ Q fun h => hPQ (le_sup_left.trans h)))

end ReducedCut

theorem ReducedCutLength.intersectionNumber_baseChange : ReducedCutLength.Statement :=
  fun _ _ _ I x Q _ hI hx hQ => ReducedCut.length_eq_finsum I x Q hI hx hQ

end GroundTheory.Heights₂.Heights.Inter
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IsLocalRing
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

noncomputable section

namespace BCMultProof

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (φ : A →+* L) [IsLocalHom φ] (hflat : φ.Flat)
    (hmax : (maximalIdeal A).map φ = maximalIdeal L) (J : Ideal A) :
    Module.length L (L ⧸ J.map φ) = Module.length A (A ⧸ J) := by
  let _ := φ.toAlgebra
  have : Module.Flat A L := hflat
  have : IsLocalHom (algebraMap A L) := ‹IsLocalHom φ›
  have key := IsLocalRing.length_baseChange A L (A ⧸ J)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L J).toLinearEquiv.length_eq,
    RingHom.algebraMap_toAlgebra, hmax] at key
  have h1 : Module.length L (L ⧸ maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one] at key
  exact key

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem flat_map : (MvPolynomial.map (algebraMap ℚ ℂ) : MRing ι ℚ →+* MRing ι ℂ).Flat :=
  ReciprocityTheory.AnForm.R.BaseChangeC.flat_mvPolynomial_rat_complex (σ := Σ k, ι k)

end BCMultProof

open BCMultProof BaseChange

theorem BCMult.intersectionNumber_baseChange : BCMult.Statement := by
  intro K _ _ ι _ P0 e s a W Wa hP hs hsP hW hWa
  classical
  have := hP.1.isPrime
  have : W.IsPrime := hW.1.1.1
  have : Wa.IsPrime := hWa.1.1
  have hWc : Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = W :=
    ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC W Wa hWa
  have hrel : NumbersDVR.IsRelevant Wa := isRelevant_of_comap hW.2 hWc
  have hext : (P0 ⊔ Ideal.span {s}).map (MvPolynomial.map (algebraMap ℚ ℂ)) =
      extC P0 ⊔ Ideal.span {sC s} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl

  have hWaMin : Wa ∈ (extC P0 ⊔ Ideal.span {sC s}).minimalPrimes := by
    rw [← hext]
    refine ⟨⟨‹Wa.IsPrime›, (Ideal.map_mono hW.1.1.2).trans hWa.1.2⟩, fun Q hQ hQWa => ?_⟩
    have : Q.IsPrime := hQ.1
    have hle : Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) ≤ W := hWc ▸ Ideal.comap_mono hQWa
    have hge : W ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) :=
      hW.1.2 ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hle
    exact hWa.2 ⟨this, Ideal.map_le_iff_le_comap.mpr hge⟩ hQWa

  have hcomp : (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm).comp
      (algebraMap (MRing ι ℚ) (Localization.AtPrime W)) =
      (algebraMap (MRing ι ℂ) (Localization.AtPrime Wa)).comp
        (MvPolynomial.map (algebraMap ℚ ℂ)) :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hWc.symm z
  have hmaxL : (maximalIdeal (Localization.AtPrime W)).map
      (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm) =
      maximalIdeal (Localization.AtPrime Wa) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map]
    exact map_eq_maximalIdeal_of_isRadical (ReciprocityTheory.AnForm.R.extC_isRadical W) hWa
  have hflat := length_quot_map_of_flat
    (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm)
    (RingHom.Flat.localRingHom flat_map Wa W hWc.symm) hmaxL
    ((P0 ⊔ Ideal.span {s}).map (algebraMap (MRing ι ℚ) (Localization.AtPrime W)))
  have hJ : ((P0 ⊔ Ideal.span {s}).map (algebraMap (MRing ι ℚ) (Localization.AtPrime W))).map
      (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm) =
      (extC P0 ⊔ Ideal.span {sC s}).map (algebraMap (MRing ι ℂ) (Localization.AtPrime Wa)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hext]
  have h1 : NumbersDVR.multAt (P0 ⊔ Ideal.span {s}) W =
      NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa := by
    unfold NumbersDVR.multAt
    rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
      ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, ← hJ, hflat]

  have h2 : NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa =
      ∑ᶠ Z ∈ (extC P0).minimalPrimes, NumbersDVR.multAt (Z ⊔ Ideal.span {sC s}) Wa :=
    ReducedCutLength.intersectionNumber_baseChange (MRing ι ℂ) (extC P0) (sC s) Wa (ReciprocityTheory.AnForm.R.extC_isRadical P0)
      (fun _ hZ => sC_not_mem (comap_extC hZ) hsP) hWaMin
  have hfin : NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa ≠ ⊤ :=
    NumbersDVR.length_localizedQuot_ne_top _ Wa hWaMin

  have hterm : ∀ Z ∈ (extC P0).minimalPrimes, NumbersDVR.divCycle Z (sC s) Wa =
      ((NumbersDVR.multAt (Z ⊔ Ideal.span {sC s}) Wa).toNat : ℤ) := by
    intro Z hZ
    unfold NumbersDVR.divCycle
    by_cases hZW : Z ⊔ Ideal.span {sC s} ≤ Wa
    · have hm : Wa ∈ (Z ⊔ Ideal.span {sC s}).minimalPrimes :=
        ⟨⟨‹Wa.IsPrime›, hZW⟩, fun Q hQ hQW =>
          hWaMin.2 ⟨hQ.1, (sup_le_sup_right hZ.1.2 _).trans hQ.2⟩ hQW⟩
      rw [dif_pos ⟨hm, hrel⟩]
    · rw [dif_neg (fun h => hZW h.1.1.2)]
      unfold NumbersDVR.multAt
      rw [Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ Wa hZW)]
      rfl
  have hL : NumbersDVR.divCycle P0 s W =
      ((NumbersDVR.multAt (P0 ⊔ Ideal.span {s}) W).toNat : ℤ) := by
    unfold NumbersDVR.divCycle
    rw [dif_pos (show W ∈ (P0 ⊔ Ideal.span {s}).minimalPrimes ∧ NumbersDVR.IsRelevant W from hW)]
  have hM : (extC P0).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  rw [hL, finsum_mem_congr rfl hterm, h1, h2]
  rw [h2] at hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hM] at hfin ⊢
  rw [ENat.toNat_sum fun Z hZ hZt => hfin (top_unique
    (hZt ▸ Finset.single_le_sum (fun _ _ => zero_le) hZ)), Nat.cast_sum,
    finsum_mem_eq_finite_toFinset_sum _ hM]

end

end GroundTheory.Heights₂.Heights.Inter
end
