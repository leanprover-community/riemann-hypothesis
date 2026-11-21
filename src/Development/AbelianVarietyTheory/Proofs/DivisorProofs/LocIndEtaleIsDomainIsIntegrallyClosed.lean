import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos

section
open IsLocalRing

namespace GlobalTheory

namespace IndEtaleNormal

open Polynomial

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

lemma exists_mem_of_finset (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (T : Finset S) : ∃ i, ∀ t ∈ T, t ∈ Si i := by
  classical
  choose idx hidx using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (T.image idx)
  exact ⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩

lemma isDomain [Nontrivial S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (hdom : ∀ i, IsDomain (Si i)) : IsDomain S := by
  classical
  have : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov {x, y}
    have hx : x ∈ Si i := hi x (by simp)
    have hy : y ∈ Si i := hi y (by simp)
    haveI := hdom i
    have h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0 := Subtype.ext (by simpa using hxy)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact NoZeroDivisors.to_isDomain S

lemma isIntegrallyClosed [IsDomain S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i)
    (hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))
  haveI := (hic i).1
  haveI := (hic i).2
  have ha : a ∈ Si i := hi a (by simp)
  have hb' : b ∈ Si i := hi b (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S)
    with hg_def
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (Si i) →+* FractionRing S := IsFractionRing.lift hg
  have hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c := fun c =>
    IsFractionRing.lift_algebraMap hg c
  have hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ /
    algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def
  have hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b := by
    rw [hy_def, map_div₀, hφ, hφ]
    rfl
  have hyint : IsIntegral (Si i) y := by
    refine ⟨q, hqm, φ.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hφy]
    have : φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g :=
      RingHom.ext hφ
    rw [this, hg_def, ← Polynomial.eval₂_map, hq]
    exact hp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint
  refine ⟨(c : S), ?_⟩
  rw [← hφy, ← hc, hφ]
  rfl

end IndEtaleNormal

theorem indEtale_isDomain_isIntegrallyClosed :
    ∀ (R S : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S]
      [Nontrivial S], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
        ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
          (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) →
      IsDomain S ∧ IsIntegrallyClosed S := by
  intro R S _ _ _ _ _ _ h
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := h
  have hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    obtain ⟨h1, h2⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R A q
    exact ⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)
  exact ⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩

end GlobalTheory
end

section
open IsLocalRing

namespace GlobalTheory

namespace LocIndEtale

open Polynomial

lemma isIntegrallyClosed_of_forall_monic_root (T : Type) [CommRing T] [IsDomain T]
    (h : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  rintro x ⟨p, hpm, hp⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : p = 1 := hpm.natDegree_eq_zero.mp hn
      subst this
      simp at hp
    · obtain ⟨r, hr⟩ := h p hpm (hn ▸ hpos)
      have hroot : IsRoot p r := hr
      have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
      set q := p /ₘ (X - C r) with hq
      have hqm : q.Monic := by
        refine Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) ?_
        rw [hfac]; exact hpm
      have hqdeg : q.natDegree < n := by
        rw [hq, Polynomial.natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
        omega
      rw [← hfac, eval₂_mul] at hp
      rcases mul_eq_zero.mp hp with h1 | h1
      · refine ⟨r, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.mp h1).symm
      · exact ih _ hqdeg q hqm h1 rfl

end LocIndEtale

theorem locIndEtale_isDomain_isIntegrallyClosed :
    ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ∧ IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := by
  intro T O _ _ _ _ _ _ _ _ _ n hT _ _ hind
  haveI : IsIntegrallyClosed T := LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hT.2
  obtain ⟨hdom, hic⟩ := indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind

  have hinj : Function.Injective (algebraMap T O) := by
    obtain ⟨ι, _, _, _, Si, -, -, hloc⟩ := hind
    obtain ⟨A, _, _, _, P, _, ⟨e⟩⟩ := hloc (Classical.arbitrary ι)
    haveI : Module.Flat (Polynomial T) (Localization.AtPrime P) := inferInstance
    have hL : Function.Injective (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
      rw [injective_iff_map_eq_zero]
      intro f hf
      by_contra hne
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := Localization.AtPrime P) (mem_nonZeroDivisors_of_ne_zero hne)
      have h1 : f • (1 : Localization.AtPrime P) = f • 0 := by
        rw [Algebra.smul_def, hf, zero_mul, smul_zero]
      exact one_ne_zero (hreg h1)
    have hS : Function.Injective (algebraMap (Polynomial T) O) := by
      have : (algebraMap (Polynomial T) O) =
          (Si (Classical.arbitrary ι)).val.toRingHom.comp
            (e.toRingEquiv.toRingHom.comp (algebraMap (Polynomial T) (Localization.AtPrime P))) := by
        ext f
        · simp
        · simp
      rw [this]
      exact Subtype.val_injective.comp (e.injective.comp hL)
    rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
    exact hS.comp Polynomial.C_injective
  have hle : Algebra.algebraMapSubmonoid O (nonZeroDivisors T) ≤ nonZeroDivisors O := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ht (hinj ?_)
    rw [h, map_zero]
  exact ⟨IsLocalization.isDomain_localization hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory
end
