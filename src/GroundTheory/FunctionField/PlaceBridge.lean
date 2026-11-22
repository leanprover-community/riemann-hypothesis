module

public import Mathlib
public import GroundTheory.FunctionField.PlaceSum

@[expose] public section

namespace GroundTheory.FunctionField

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section General

variable (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
  (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range)

noncomputable abbrev ofHeightOneSpectrum (P : HeightOneSpectrum B) : Place k K where
  ring := HeightOneSpectrum.valuationSubringAtPrime K P
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    obtain ⟨b, hb⟩ := hk c
    rw [← hb]
    exact Subalgebra.algebraMap_mem
      (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b

theorem algebraMap_mem_ofHeightOneSpectrum (P : HeightOneSpectrum B) (b : B) :
    algebraMap B K b ∈ (ofHeightOneSpectrum B hk P).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b

noncomputable def centerHom (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) : B →+* v.ring :=
  RingHom.codRestrict (algebraMap B K) v.ring hv

noncomputable def center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    HeightOneSpectrum B where
  asIdeal := (maximalIdeal v.ring).comap (centerHom B v hv)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h0
    apply v.ne_top
    have hunit : ∀ b : B, b ≠ 0 → v.ring.valuation (algebraMap B K b) = 1 := by
      intro b hb
      refine le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv b)) (not_lt.1 fun hlt => hb ?_)
      have hmem : centerHom B v hv b ∈ maximalIdeal v.ring := (v.ring.valuation_lt_one_iff _).2 hlt
      have : b ∈ (maximalIdeal v.ring).comap (centerHom B v hv) := hmem
      rw [h0] at this
      exact this
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    rw [← v.ring.valuation_le_one_iff, map_div₀, hunit s hs0, div_one]
    exact (v.ring.valuation_le_one_iff _).2 (hv a)

variable [IsFunctionField k K]

theorem ofHeightOneSpectrum_center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    ofHeightOneSpectrum B hk (center B v hv) = v := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have hs' : centerHom B v hv s ∉ maximalIdeal v.ring := hs
  have hs1 : v.ring.valuation (algebraMap B K s) = 1 :=
    le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv s)) (not_lt.1 fun hlt =>
      hs' ((v.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : (algebraMap B K s)⁻¹ ∈ v.ring := by
    rw [← v.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem (hv a) hsinv

omit [IsFunctionField k K] in
theorem center_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    center B (ofHeightOneSpectrum B hk P) (algebraMap_mem_ofHeightOneSpectrum B hk P) = P := by
  ext b
  change centerHom B _ _ b ∈ maximalIdeal (ofHeightOneSpectrum B hk P).ring ↔ b ∈ P.asIdeal
  rw [ValuationSubring.valuation_lt_one_iff]
  change (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) < 1 ↔ b ∈ P.asIdeal
  have hbmem := algebraMap_mem_ofHeightOneSpectrum B hk P b
  constructor
  · intro hb
    by_contra hbP
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring :=
      ⟨1, b, hbP, by simp⟩
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      apply hbP
      have : b = 0 := IsFractionRing.injective B K (h0.trans (map_zero _).symm)
      rw [this]
      exact P.asIdeal.zero_mem
    have h1 := (ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbP
    by_contra hb
    have hb1 : (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) = 1 :=
      le_antisymm ((ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hbmem)
        (not_lt.1 hb)
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have h1 : P.valuation K (algebraMap B K b)⁻¹ ≤ 1 := hle hinv
    have h2 : P.valuation K (algebraMap B K b) < 1 := (P.valuation_lt_one_iff_mem (K := K) b).2 hbP
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)

theorem valuation_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum B hk P).valuation = P.valuation K := by
  refine valuation_eq_of_isEquiv ?_ (ofHeightOneSpectrum B hk P).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K P)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
  let Q : Place k K :=
    { ring := (P.valuation K).valuationSubring
      ne_top := (ofHeightOneSpectrum B hk P).ne_top ∘ fun htop => by
        apply le_antisymm le_top
        intro y _
        obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
        have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((ofHeightOneSpectrum B hk P).algebraMap_mem c) }
  have heq : ofHeightOneSpectrum B hk P = Q := Place.eq_of_le hle
  constructor
  · exact fun hx => hle hx
  · intro hx
    have hxQ : x ∈ Q.ring := hx
    rw [← heq] at hxQ
    exact hxQ

end General

section RatFunc

open scoped Polynomial

end RatFunc

section RingOfIntegers

open scoped Polynomial

variable [IsFunctionField k K] [Algebra k[X] K] [Algebra (RatFunc k) K]
  [IsScalarTower k[X] (RatFunc k) K] [IsScalarTower k k[X] K] [FunctionField k K]

end RingOfIntegers

section Separating

open scoped IntermediateField.algebraAdjoinAdjoin

variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]

attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin

end Separating

end Place

end GroundTheory.FunctionField
