import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation

section
universe u

namespace UpperTheory.NoetherNormalizationChart

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

private noncomputable def shear (b : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval (Fin.cases (X 0) (fun i : Fin n => X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ))))

private lemma shear_zero (b : ℕ) (c : A) : shear (n := n) b c (X 0) = X 0 := by
  simp [shear]

private lemma shear_succ (b : ℕ) (c : A) (i : Fin n) :
    shear (n := n) b c (X i.succ) = X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ)) := by
  simp [shear]

private lemma shear_comp (b : ℕ) (c d : A) (h : c + d = 0) :
    (shear (n := n) b c).comp (shear b d) = AlgHom.id _ _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  cases i using Fin.cases with
  | zero => simp [shear_zero]
  | succ i =>
    rw [AlgHom.comp_apply, shear_succ, map_add, map_mul, map_pow, shear_zero, shear_succ,
      algHom_C, algebraMap_eq, add_assoc, ← add_mul, ← C_add, h]
    simp

private noncomputable def chart (A : Type u) [CommRing A] (n b : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A) :=
  (AlgEquiv.ofAlgHom (shear b 1) (shear b (-1)) (shear_comp b 1 (-1) (by simp))
    (shear_comp b (-1) 1 (by simp))).trans (finSuccEquiv A n)

private lemma chart_X [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (i : Fin (n + 1)) :
    (chart A n b (X i)).IsMonicOfDegree (b ^ (i : ℕ)) := by
  cases i using Fin.cases with
  | zero =>
    have : chart A n b (X 0) = Polynomial.X := by
      simp [chart, shear_zero, finSuccEquiv_X_zero]
    rw [this]
    exact ⟨by simp, Polynomial.monic_X⟩
  | succ i =>
    have : chart A n b (X i.succ)
        = Polynomial.X ^ (b ^ (i.succ : ℕ)) + Polynomial.C (X i) := by
      simp [chart, shear_succ, finSuccEquiv_X_zero, finSuccEquiv_X_succ, add_comm]
    rw [this]
    exact ⟨Polynomial.natDegree_X_pow_add_C, Polynomial.monic_X_pow_add_C _ (pow_ne_zero _ hb)⟩

private lemma chart_C (b : ℕ) (a : A) : chart A n b (C a) = Polynomial.C (C a) :=
  (chart A n b).commutes a

private lemma chart_monomial [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (v : Fin (n + 1) →₀ ℕ) :
    (chart A n b (monomial v 1)).IsMonicOfDegree (∑ i, v i * b ^ (i : ℕ)) := by
  have h : chart A n b (monomial v 1) = ∏ i, chart A n b (X i) ^ v i := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  have hm : ∀ i ∈ Finset.univ, (chart A n b (X i) ^ v i).Monic :=
    fun i _ => (chart_X hb i).monic.pow _
  rw [h]
  refine ⟨?_, Polynomial.monic_prod_of_monic _ _ hm⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(chart_X hb i).monic.natDegree_pow, (chart_X hb i).natDegree_eq]

private lemma weight_inj {m b : ℕ} (v w : Fin m → ℕ) (hv : ∀ i, v i < b) (hw : ∀ i, w i < b)
    (h : ∑ i, v i * b ^ (i : ℕ) = ∑ i, w i * b ^ (i : ℕ)) : v = w := by
  have key : (fun i => (⟨v i, hv i⟩ : Fin b)) = fun i => ⟨w i, hw i⟩ := by
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  funext i
  exact congrArg Fin.val (congrFun key i)

end UpperTheory.NoetherNormalizationChart

open UpperTheory.NoetherNormalizationChart in
theorem UpperTheory.exists_monic_change_of_variables :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) A), f ≠ 0 → ∃ (e : MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A)) (a : A), a ≠ 0 ∧ (e f).leadingCoeff = MvPolynomial.C a := by
  intro A _ _ n f hf
  classical
  set b := f.totalDegree + 1 with hbdef
  have hb : b ≠ 0 := Nat.succ_ne_zero _
  let wt : (Fin (n + 1) →₀ ℕ) → ℕ := fun v => ∑ i, v i * b ^ (i : ℕ)
  have hlt : ∀ v ∈ f.support, ∀ i, v i < b := fun v hv i =>
    Nat.lt_succ_of_le ((MvPolynomial.monomial_le_degreeOf i hv).trans
      (MvPolynomial.degreeOf_le_totalDegree f i))
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image f.support wt (MvPolynomial.support_nonempty.mpr hf)
  have ha : f.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hsum : chart A n b f = ∑ w ∈ f.support,
      Polynomial.C (MvPolynomial.C (f.coeff w)) * chart A n b (MvPolynomial.monomial w 1) := by
    conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← chart_C b, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hdeg : (chart A n b f).natDegree ≤ wt v := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun w hw => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [(chart_monomial hb w).natDegree_eq]
    exact hmax w hw
  have hcoeff : (chart A n b f).coeff (wt v) = MvPolynomial.C (f.coeff v) := by
    rw [hsum, Polynomial.finset_sum_coeff, Finset.sum_eq_single_of_mem v hv]
    · have h1 := (chart_monomial (A := A) hb v).monic.coeff_natDegree
      rw [(chart_monomial hb v).natDegree_eq] at h1
      rw [Polynomial.coeff_C_mul, h1, mul_one]
    · intro w hw hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [(chart_monomial hb w).natDegree_eq]
      refine lt_of_le_of_ne (hmax w hw) fun h => hne ?_
      exact DFunLike.coe_injective (weight_inj w v (hlt w hw) (hlt v hv) h)
  refine ⟨chart A n b, f.coeff v, ha, ?_⟩
  have hne : (chart A n b f).coeff (wt v) ≠ 0 := by
    rw [hcoeff]
    simpa using ha
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hne, hcoeff]
end

section
universe u

theorem UpperTheory.pseudo_division :
    ∀ (R : Type u) [CommRing R] (g p : Polynomial R), g ≠ 0 → ∃ (k : ℕ) (q r : Polynomial R), Polynomial.C (g.leadingCoeff ^ k) * p = g * q + r ∧ r.degree < g.degree := by
  intro R _ g p hg
  induction p using (Polynomial.degree_lt_wf (R := R)).induction with
  | _ p ih =>
    by_cases h : p.degree < g.degree
    · exact ⟨0, 0, p, by simp, h⟩
    · have hle : g.degree ≤ p.degree := not_lt.mp h
      have hp : p ≠ 0 := by
        rintro rfl
        rw [Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot] at hle
        exact hg hle
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)
      have hlt : (Polynomial.C g.leadingCoeff * p
          - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + d := ⟨m - d, by omega⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]
        rcases Nat.eq_or_lt_of_le hm with he | hl
        · have hj : j = g.natDegree := by omega
          rw [← he, hj]
          exact sub_self _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
            Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]
          simp
      obtain ⟨k, q, r, he, hr⟩ := ih _ hlt
      refine ⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff,
        r, ?_, hr⟩
      rw [pow_succ, Polynomial.C_mul]
      linear_combination he
end

section
theorem UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof.{u} :
    GroundTheory.Heights₂.Heights.GenericNoetherNormalisation.Statement.{u} := by
  intro A _ _ n q _ hq _
  classical
  obtain ⟨f, hfq, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  obtain ⟨e, a, ha, hlc⟩ := UpperTheory.exists_monic_change_of_variables A n f hf
  have hg : e f ≠ 0 := fun h ↦ hf (e.injective (by simpa using h))
  let π : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] MvPolynomial (Fin (n + 1)) A ⧸ q :=
    (Ideal.Quotient.mkₐ A q).comp e.symm.toAlgHom
  have hπf : π (e f) = 0 := by
    simpa [π, Ideal.Quotient.eq_zero_iff_mem] using hfq
  have hsurj : Function.Surjective π :=
    (Ideal.Quotient.mkₐ_surjective A q).comp e.symm.surjective
  let z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q :=
    fun i ↦ π (Polynomial.C (MvPolynomial.X i))
  have hz : ∀ c : MvPolynomial (Fin n) A, MvPolynomial.aeval z c = π (Polynomial.C c) := by
    intro c
    have : MvPolynomial.aeval z = π.comp (Polynomial.CAlgHom) := by
      ext i
      simp [z]
    rw [this]
    rfl
  let N := (e f).natDegree
  refine ⟨a, ha, z, (Finset.range N).image (fun j ↦ π Polynomial.X ^ j), fun d ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hsurj d
  obtain ⟨k, s, r, hk, hr⟩ := UpperTheory.pseudo_division (MvPolynomial (Fin n) A) (e f) p hg
  have h1 : a ^ k • π p = π r := by
    have := congrArg π hk
    rw [map_add, map_mul π (e f), hπf, zero_mul, zero_add, hlc, map_mul, ← hz, ← map_pow,
      MvPolynomial.aeval_C, ← Algebra.smul_def] at this
    exact this
  have h2 : r = ∑ j ∈ Finset.range N, Polynomial.C (r.coeff j) * Polynomial.X ^ j := by
    rw [Polynomial.degree_eq_natDegree hg] at hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        Polynomial.as_sum_range' r N ((Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hr)
  refine ⟨k, fun t ↦ ∑ j ∈ Finset.range N with π Polynomial.X ^ j = t, r.coeff j, ?_⟩
  rw [h1, h2, map_sum, ← Finset.sum_fiberwise_of_maps_to (g := fun j ↦ π Polynomial.X ^ j)
    (fun j hj ↦ Finset.mem_image_of_mem _ hj), ← h2]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [map_mul, map_pow, hz, (Finset.mem_filter.mp hj).2]
end
