import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsDirichletCharacterSmoothed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotient
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) → ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | exact GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | (intros; apply GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory

theorem exists_polynomial_closedSubgroup_fixed_eval_eq {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [IsGalois F Ω] (H : ClosedSubgroup (Ω ≃ₐ[F] Ω)) (ζ u : Ω)
    (h : ∀ s ∈ H.toSubgroup, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ H.toSubgroup, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u := by
  classical
  let T : IntermediateField F Ω := IntermediateField.fixedField H.toSubgroup
  have hT : T.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  let E : IntermediateField F Ω :=
    (IntermediateField.adjoin T ({ζ} : Set Ω)).restrictScalars F
  have hu : u ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    refine h s ?_ (hs ζ (IntermediateField.mem_adjoin_simple_self T ζ))
    have : s ∈ T.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hs x ((IntermediateField.adjoin T ({ζ} : Set Ω)).algebraMap_mem ⟨x, hx⟩)
    rw [hT] at this
    exact this
  have hint : IsIntegral T ζ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) ζ).isIntegral.tower_top
  have hu' : u ∈ (IntermediateField.adjoin T ({ζ} : Set Ω)).toSubalgebra := hu
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hu'
  obtain ⟨Q, hQ⟩ := hu'
  refine ⟨Q.map (algebraMap T Ω), ?_, ?_⟩
  · intro s hs d
    rw [Polynomial.coeff_map]
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup _).1 (Q.coeff d).2 s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hQ

theorem exists_polynomial_inertia_fixed_eval_eq (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω)
    (h : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u :=
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  exists_polynomial_closedSubgroup_fixed_eval_eq
    ⟨Ine (F := ℚ) A, isClosed_Ine (F := ℚ) A⟩ ζ u h

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω), (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧ P.eval ζ = u := by
  atlas_forward_decl GlobalTheory.exists_polynomial_inertia_fixed_eval_eq
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω), 1 ≤ n → IsPrimitiveRoot ζ (l ^ n) → A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_zeta_sub_one_pow_totient | exact GlobalTheory.valuation_zeta_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_zeta_sub_one_pow_totient <;> assumption)
end

section
section
namespace GlobalTheory

theorem mem_of_sum_mul_pow_mem_of_valuation_zpow (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω) (hN : 0 < N) (hℓ : ℓ ≠ 0)
    (hℓ1 : A.valuation ℓ < 1) (hπ : A.valuation π ^ N = A.valuation ℓ)
    (hc : ∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k)
    (hsum : (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A) : ∀ i < N, c i ∈ A := by
  classical
  set v := A.valuation with hv
  set b := v ℓ with hb
  have hb0 : 0 < b := lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff v).2 hℓ))
  set t : ℕ → A.ValueGroup := fun i => v (c i * π ^ i) with ht

  have hpow : ∀ i (k : ℤ), v (c i) = b ^ k → t i ^ N = b ^ ((N : ℤ) * k + i) := by
    intro i k hk
    simp only [ht, map_mul, map_pow, hk]
    rw [mul_pow, ← pow_mul, mul_comm i N, pow_mul, hπ, zpow_add₀ hb0.ne', mul_comm (N : ℤ) k,
      zpow_mul, zpow_natCast, zpow_natCast]

  have hdist : ∀ i < N, ∀ j < N, c i ≠ 0 → c j ≠ 0 → t i = t j → i = j := by
    intro i hi j hj hci hcj hij
    obtain ⟨k, hk⟩ := hc i hi hci
    obtain ⟨l, hl⟩ := hc j hj hcj
    have e : b ^ ((N : ℤ) * k + i) = b ^ ((N : ℤ) * l + j) := by
      rw [← hpow i k hk, ← hpow j l hl, hij]
    have e2 := (zpow_right_strictAnti₀ hb0 hℓ1).injective e
    have h1 : ((N : ℤ) * k + i) % N = (i : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have h2 : ((N : ℤ) * l + j) % N = (j : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have : (i : ℤ) = j := by rw [← h1, ← h2, e2]
    exact_mod_cast this

  have hle : ∀ i ∈ Finset.range N, t i ≤ 1 := by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range N) t ⟨0, Finset.mem_range.2 hN⟩
    suffices t j ≤ 1 from fun i hi => (hmax i hi).trans this
    by_cases htj : t j = 0
    · rw [htj]; exact zero_le'
    have hcj : c j ≠ 0 := by
      intro h; apply htj; simp [ht, h]
    have hlt : ∀ i ∈ Finset.range N \ {j}, v (c i * π ^ i) < v (c j * π ^ j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      refine lt_of_le_of_ne (hmax i hi.1) ?_
      intro heq
      by_cases hci : c i = 0
      · apply htj; show v (c j * π ^ j) = 0; rw [← heq]; simp [hci]
      · exact hi.2 (hdist i (Finset.mem_range.1 hi.1) j (Finset.mem_range.1 hj) hci hcj heq)
    have := Valuation.map_sum_eq_of_lt v hj hlt
    rw [← (A.valuation_le_one_iff _)] at hsum
    show v (c j * π ^ j) ≤ 1
    rw [← this]; exact hsum
  intro i hi
  by_cases hci : c i = 0
  · rw [hci]; exact A.zero_mem
  obtain ⟨k, hk⟩ := hc i hi hci
  have h1 : t i ^ N ≤ 1 := pow_le_one₀ zero_le' (hle i (Finset.mem_range.2 hi))
  rw [hpow i k hk, zpow_le_one_iff_right_of_lt_one₀ hb0 hℓ1] at h1
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push_neg at hneg
    have : (N : ℤ) * k ≤ -(N : ℤ) := by nlinarith
    omega
  rw [← A.valuation_le_one_iff, hk]
  exact zpow_le_one₀ hb0 hℓ1.le hk0

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow : ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω), 0 < N → ℓ ≠ 0 → A.valuation ℓ < 1 → A.valuation π ^ N = A.valuation ℓ → (∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k) → (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A → ∀ i < N, c i ∈ A := by
  atlas_forward_decl GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem GlobalTheory.ZetaPoly.exists_poly : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A hA n ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hζ1 : ζ = 1 := by simpa using hζ
    subst hζ1
    refine ⟨Polynomial.C u, fun d => ?_, by simp⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact ⟨hu, fun s hs => hfix s hs (map_one s)⟩
    · exact ⟨A.zero_mem, fun s _ => map_zero s⟩
  obtain ⟨P, hPfix, hPev⟩ := GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed Ω A ζ u hfix
  set N := (l ^ n).totient with hN
  have hlpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hNpos : 0 < N := Nat.totient_pos.2 hlpos
  set Φ := Polynomial.cyclotomic (l ^ n) Ω with hΦ
  have hΦm : Φ.Monic := Polynomial.cyclotomic.monic _ _
  have hΦdeg : Φ.natDegree = N := Polynomial.natDegree_cyclotomic _ _
  have hΦ1 : Φ ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hΦdeg; omega
  set P' := P %ₘ Φ with hP'
  have hroot : Φ.eval ζ = 0 := (hζ.isRoot_cyclotomic hlpos)
  have hev : P'.eval ζ = u := by
    rw [← hPev]
    show (P %ₘ Φ).eval ζ = P.eval ζ
    conv_rhs => rw [← Polynomial.modByMonic_add_div P Φ]
    rw [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul, add_zero]
  have hdeg : P'.natDegree < N := hΦdeg ▸ Polynomial.natDegree_modByMonic_lt P hΦm hΦ1
  have hPmap : ∀ s ∈ Ine (F := ℚ) A, P.map (s : Ω →+* Ω) = P := fun s hs =>
    Polynomial.ext fun d => by rw [Polynomial.coeff_map]; exact hPfix s hs d
  have hP'map : ∀ s ∈ Ine (F := ℚ) A, P'.map (s : Ω →+* Ω) = P' := fun s hs => by
    rw [hP', Polynomial.map_modByMonic _ hΦm, hPmap s hs, hΦ, Polynomial.map_cyclotomic]
  set T := Polynomial.taylor (1 : Ω) P' with hT
  have hTmap : ∀ s ∈ Ine (F := ℚ) A, T.map (s : Ω →+* Ω) = T := fun s hs => by
    rw [hT, Polynomial.map_taylor, hP'map s hs, map_one]
  have hTdeg : T.natDegree < N := by rw [hT, Polynomial.natDegree_taylor]; exact hdeg
  have hsum : (∑ i ∈ Finset.range N, T.coeff i * (ζ - 1) ^ i) = u := by
    rw [← Polynomial.eval_eq_sum_range' hTdeg, hT, Polynomial.taylor_eval, sub_add_cancel, hev]
  obtain ⟨v, hv, hlv⟩ := hA
  have hl1 : A.valuation (l : Ω) < 1 := by
    have := (hv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hcA : ∀ i < N, T.coeff i ∈ A := by
    refine GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow Ω A N (ζ - 1) (l : Ω) (fun i => T.coeff i) hNpos hl0 hl1
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg l Ω A n ζ hn hζ) (fun i _ hc => ?_) (hsum ▸ hu)
    refine GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure l Ω A ⟨v, hv, hlv⟩ _ hc (fun s hs => ?_)
    have := congrArg (fun p => Polynomial.coeff p i) (hTmap s hs)
    simpa [Polynomial.coeff_map] using this
  have hcA' : ∀ i, T.coeff i ∈ A := fun i => by
    rcases lt_or_ge i N with h | h
    · exact hcA i h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact A.zero_mem
  have hlift : T ∈ Polynomial.lifts (A.subtype) :=
    (Polynomial.lifts_iff_coeff_lifts T).2 fun i => ⟨⟨_, hcA' i⟩, rfl⟩
  obtain ⟨T₀, hT₀⟩ := Polynomial.mem_lifts T |>.1 hlift
  have hback : Polynomial.taylor (-1 : Ω) T = P' := by
    rw [hT, Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  refine ⟨P', fun d => ⟨?_, fun s hs => ?_⟩, hev⟩
  · rw [← hback, ← hT₀]
    have : ((-1 : A) : Ω) = -1 := by simp
    rw [← this, show ((-1 : A) : Ω) = A.subtype (-1) from rfl, ← Polynomial.map_taylor, Polynomial.coeff_map]
    exact (Polynomial.taylor (-1 : A) T₀).coeff d |>.2
  · have := congrArg (fun p => Polynomial.coeff p d) (hP'map s hs)
    simpa [Polynomial.coeff_map] using this

end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.ZetaPoly.exists_poly | exact GlobalTheory.ZetaPoly.exists_poly | (intros; apply GlobalTheory.ZetaPoly.exists_poly; all_goals assumption)
end
