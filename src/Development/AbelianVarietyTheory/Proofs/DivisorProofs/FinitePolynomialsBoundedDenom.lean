import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignatureStatement

section
open NumberField Polynomial

namespace GlobalTheory

theorem isIntegral_pow_mul_esymm (s : Multiset ℂ) (c : ℂ) (m : ℕ)
    (h : ∀ w ∈ s, IsIntegral ℤ (c * w)) : IsIntegral ℤ (c ^ m * s.esymm m) := by
  rw [Multiset.esymm, ← Multiset.sum_map_mul_left]
  refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  have : c ^ m * t.prod = (t.map (fun w => c * w)).prod := by
    rw [Multiset.prod_map_mul (f := fun _ => c) (g := fun w => w), Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_id', ht.2]
  rw [this]
  refine (integralClosure ℤ ℂ).multiset_prod_mem ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
  exact h w (Multiset.mem_of_le ht.1 hw)

theorem finite_monic_roots_bdd_mul_isIntegral :
    ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  intro F _ _ n N B hN
  let φ₀ : F →+* ℂ := (Classical.arbitrary (InfinitePlace F)).embedding
  let B₁ : ℝ := max |B| 1
  let C : ℝ := (N : ℝ) ^ n * (B₁ ^ n * 2 ^ n)
  have hT := Embeddings.finite_of_norm_le F ℂ C
  let f : F[X] → Fin (n + 1) → F := fun P k => (N : F) ^ n * P.coeff k
  refine Set.Finite.of_finite_image (f := f) ((Set.Finite.pi (fun _ => hT)).subset ?_) ?_
  · rintro _ ⟨P, ⟨hm, hd, hr⟩, rfl⟩ k -
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
    refine ⟨?_, fun φ => ?_⟩
    · have hcard : Multiset.card (P.map φ₀).roots = (P.map φ₀).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      have hdeg : (P.map φ₀).natDegree = n := by rw [hm.natDegree_map, hd]
      have hc := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
      rw [(hm.map φ₀).leadingCoeff, hdeg, one_mul, coeff_map] at hc
      rw [← isIntegral_algHom_iff φ₀.toIntAlgHom φ₀.injective]
      show IsIntegral ℤ (φ₀ ((N : F) ^ n * P.coeff k))
      rw [map_mul, map_pow, map_natCast, hc]
      have hsplit : (N : ℂ) ^ n * ((-1) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) =
          ((N : ℂ) ^ (k : ℕ) * (-1) ^ (n - k)) *
            ((N : ℂ) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) := by
        have : (N : ℂ) ^ n = (N : ℂ) ^ (k : ℕ) * (N : ℂ) ^ (n - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
        rw [this]; ring
      rw [hsplit]
      refine IsIntegral.mul (IsIntegral.mul ((isIntegral_natCast N).pow _)
        ((isIntegral_one.neg).pow _)) ?_
      exact GlobalTheory.isIntegral_pow_mul_esymm _ _ _ (fun w hw => (hr φ₀ w hw).2)
    · show ‖φ ((N : F) ^ n * P.coeff k)‖ ≤ C
      rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
      have hb := coeff_le_of_roots_le (p := P) (f := φ) (B := B₁) k hm (IsAlgClosed.splits _)
        (fun z hz => (hr φ z hz).1.trans ((le_abs_self B).trans (le_max_left _ _)))
      rw [coeff_map, hd] at hb
      have hB₁ : (1 : ℝ) ≤ B₁ := le_max_right _ _
      have h2 : B₁ ^ (n - k) * (n.choose k : ℝ) ≤ B₁ ^ n * 2 ^ n :=
        mul_le_mul (pow_le_pow_right₀ hB₁ (Nat.sub_le _ _))
          (by exact_mod_cast Nat.choose_le_two_pow n k) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)
  · rintro P ⟨-, hdP, -⟩ Q ⟨-, hdQ, -⟩ hPQ
    ext i
    by_cases hi : i ≤ n
    · have h := congrFun hPQ ⟨i, by omega⟩
      exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

end GlobalTheory
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral : ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  first | (exact @GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_roots_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_roots_bdd_mul_isIntegral <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Northcott

theorem isIntegral_eig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsIntegral ℤ M) {w : ℂ}
    {x : Fin n → ℂ} (hx : x ≠ 0) (hMx : M *ᵥ x = w • x) : IsIntegral ℤ w := by
  obtain ⟨q, hq, hqM⟩ := hM
  refine ⟨q, hq, ?_⟩
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) w x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMx), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap ℤ ℂ)) hv
  have h2 : Polynomial.aeval (Matrix.toLin' M) (q.map (algebraMap ℤ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have e := Polynomial.aeval_algHom_apply
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.restrictScalars ℤ) M q
    have e2 : Polynomial.aeval M q = 0 := hqM
    rw [e2, map_zero] at e
    exact e
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := (smul_eq_zero.1 h1.symm).resolve_right hx
  rwa [Polynomial.eval_map] at h3

theorem norm_le_of_isIntegral_inv (w : ℂ) (c : ℚ) (N : ℕ) (hN : 0 < N) (hw : ‖w‖ ^ 2 = (c : ℝ))
    (hc : (c : ℝ) ≠ 0) (hI : IsIntegral ℤ ((N : ℂ) * w⁻¹)) : ‖w‖ ≤ N := by
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne (hw ▸ sq_nonneg _) (Ne.symm hc)
  have hconj : IsIntegral ℤ (starRingEnd ℂ ((N : ℂ) * w⁻¹)) := hI.map (starRingEnd ℂ).toIntAlgHom
  have hprod := hI.mul hconj
  have e : (N : ℂ) * w⁻¹ * starRingEnd ℂ ((N : ℂ) * w⁻¹) = (((N : ℚ) ^ 2 / c : ℚ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_inv, mul_pow, inv_pow, hw,
      Complex.norm_natCast]
    push_cast
    ring
  rw [e] at hprod
  have hq : IsIntegral ℤ ((N : ℚ) ^ 2 / c) := by
    refine (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective
      (x := (N : ℚ) ^ 2 / c)).1 ?_
    simpa using hprod
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  have hcq : (0 : ℚ) < c := by exact_mod_cast hcpos
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) ^ 2 / c := by positivity
  have hk1 : (1 : ℚ) ≤ (N : ℚ) ^ 2 / c := by
    rw [← hk] at hpos ⊢
    rw [algebraMap_int_eq, eq_intCast] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ k := this
    exact_mod_cast this
  have hcN : (c : ℚ) ≤ (N : ℚ) ^ 2 := by rwa [le_div_iff₀ hcq, one_mul] at hk1
  have hcN' : (c : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcN
  rw [← hw] at hcN'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hcN'

end GlobalTheory.LKMid.Northcott
end
