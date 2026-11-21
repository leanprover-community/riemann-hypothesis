import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLower

section
namespace PI.Residue

open scoped ENNReal

section Comb

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

def intersection_update_fsHerm_neg_one (N : α → ℕ) (idx : α → ι) (s : Multiset α) (i : ι) : ℕ :=
  ((s.filter (fun a => idx a = i)).map N).prod

theorem position_cons (N : α → ℕ) (idx : α → ι) (a : α) (s : Multiset α) (i : ι) :
    intersection_update_fsHerm_neg_one N idx (a ::ₘ s) i = (if idx a = i then N a else 1) * intersection_update_fsHerm_neg_one N idx s i := by
  unfold intersection_update_fsHerm_neg_one
  by_cases h : idx a = i
  · simp [h]
  · simp [h]

theorem prod_position [Fintype ι] (N : α → ℕ) (idx : α → ι) (s : Multiset α) :
    ∏ i, intersection_update_fsHerm_neg_one N idx s i = (s.map N).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [intersection_update_fsHerm_neg_one]
  | cons a s ih =>
    simp_rw [position_cons]
    rw [Finset.prod_mul_distrib, ih]
    simp

theorem factorization_multiset_prod (m : Multiset ℕ) (h : ∀ x ∈ m, x ≠ 0) (p : ℕ) :
    m.prod.factorization p = (m.map (fun x => x.factorization p)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hs' : s.prod ≠ 0 := by
      intro h0
      exact hs 0 (Multiset.prod_eq_zero_iff.mp h0) rfl
    rw [Multiset.prod_cons, Nat.factorization_mul ha hs', Multiset.map_cons, Multiset.sum_cons,
      Finsupp.add_apply, ih hs]

theorem factorization_position (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s : Multiset α} (hs : ∀ a ∈ s, a ∈ S) {a : α} (ha : a ∈ S) :
    (intersection_update_fsHerm_neg_one N idx s (idx a)).factorization (N a).minFac
      = s.count a * (N a).factorization (N a).minFac := by
  have hp : (N a).minFac.Prime := Nat.minFac_prime (h1 a ha).ne'
  unfold intersection_update_fsHerm_neg_one
  rw [factorization_multiset_prod, Multiset.map_map,
    Multiset.sum_map_eq_nsmul_single a,
    Multiset.count_filter_of_pos (p := fun b => idx b = idx a) rfl]
  · simp
  · intro b hba hb
    rw [Multiset.mem_filter] at hb
    simp only [Function.comp_apply]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    apply hba
    refine h2 b (hs b hb.1) a ha hb.2 ?_
    intro hcop
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdvd (Nat.minFac_dvd _) hcop
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Multiset.mem_filter] at hb
    exact (Nat.zero_lt_of_lt (h1 b (hs b hb.1))).ne'

theorem position_inj (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s t : Multiset α} (hs : ∀ a ∈ s, a ∈ S) (ht : ∀ a ∈ t, a ∈ S)
    (h : intersection_update_fsHerm_neg_one N idx s = intersection_update_fsHerm_neg_one N idx t) : s = t := by
  ext a
  by_cases ha : a ∈ S
  · have e1 := factorization_position N idx S h1 h2 hs ha
    have e2 := factorization_position N idx S h1 h2 ht ha
    rw [h, e2] at e1
    have hp : (N a).minFac.Prime := Nat.minFac_prime (h1 a ha).ne'
    have hpos : 0 < (N a).factorization (N a).minFac :=
      hp.factorization_pos_of_dvd (Nat.zero_lt_of_lt (h1 a ha)).ne' (Nat.minFac_dvd _)
    exact (Nat.eq_of_mul_eq_mul_right hpos e1).symm
  · rw [Multiset.count_eq_zero_of_notMem (fun h' => ha (hs a h')),
      Multiset.count_eq_zero_of_notMem (fun h' => ha (ht a h'))]

end Comb

section Sums

theorem tsum_pi_prod (w : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑' v : Fin m → ℕ, ∏ i, w (v i) = (∑' n, w n) ^ m := by
  induction m with
  | zero => simp [tsum_fintype]
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).tsum_eq, ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rw [pow_succ, mul_comm]

theorem tsum_le_pow {β : Type*} {m : ℕ} (n : β → Fin m → ℕ) (hinj : Function.Injective n)
    (w : ℕ → ℝ≥0∞) (W : β → ℝ≥0∞) (hw : ∀ b, W b = ∏ i, w (n b i)) :
    ∑' b, W b ≤ (∑' k, w k) ^ m := by
  rw [← tsum_pi_prod]
  simp_rw [hw]
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj (fun v => ∏ i, w (v i))

end Sums

end PI.Residue
end

section
namespace PI.Residue

open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal

variable (E : Type*) [Field E] [NumberField E]

def primeSet : Set (Ideal (𝓞 E)) := {P | P.IsPrime ∧ P ≠ ⊥}

variable {E}

theorem one_lt_absNorm_of_mem {P : Ideal (𝓞 E)} (hP : P ∈ primeSet E) : 1 < absNorm P := by
  have h0 : absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hP.2
  have h1 : absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.1.ne_top
  omega

variable (E)

set_option linter.deprecated false in
theorem exists_injOn_primesOver (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) :
    ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E), Set.InjOn g (p.primesOver (𝓞 E)) := by
  have hcard := Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hp
  have : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hfin : (p.primesOver (𝓞 E)).Finite := by
    rw [← IsDedekindDomain.coe_primesOverFinset hp (𝓞 E)]
    exact Finset.finite_toSet _
  obtain ⟨f, -, hf⟩ := hfin.exists_injOn_of_encard_le
    (t := (Set.univ : Set (Fin (Module.finrank ℚ E)))) (by
      rw [← IsDedekindDomain.coe_primesOverFinset hp (𝓞 E), Set.encard_coe_eq_coe_finsetCard,
        Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      exact_mod_cast hcard)
  exact ⟨f, hf⟩

variable {E}

theorem under_eq_of_not_coprime {P Q : Ideal (𝓞 E)} (hP : P ∈ primeSet E) (hQ : Q ∈ primeSet E)
    (hcop : ¬ Nat.Coprime (absNorm P) (absNorm Q)) : P.under ℤ = Q.under ℤ := by
  have := hP.1
  have := hQ.1
  have : NeZero P := ⟨hP.2⟩
  have : NeZero Q := ⟨hQ.2⟩
  have pP := Nat.absNorm_under_prime P
  have pQ := Nat.absNorm_under_prime Q
  have eP := absNorm_eq_pow_inertiaDeg'_of_liesOver P (P.under ℤ) inferInstance
    (Ideal.under_ne_bot ℤ hP.2)
  have eQ := absNorm_eq_pow_inertiaDeg'_of_liesOver Q (Q.under ℤ) inferInstance
    (Ideal.under_ne_bot ℤ hQ.2)
  by_contra hne
  apply hcop
  rw [eP, eQ]
  apply Nat.Coprime.pow
  rw [Nat.coprime_primes pP pQ]
  intro heq
  apply hne
  rw [← Int.ideal_span_absNorm_eq_self (P.under ℤ), ← Int.ideal_span_absNorm_eq_self (Q.under ℤ),
    heq]

variable (E)

theorem exists_idx : ∃ idx : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
    ∀ P ∈ primeSet E, ∀ Q ∈ primeSet E, idx P = idx Q →
      ¬ Nat.Coprime (absNorm P) (absNorm Q) → P = Q := by
  classical
  have H : ∀ p : Ideal ℤ, ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
      p.IsMaximal → p ≠ ⊥ → Set.InjOn g (p.primesOver (𝓞 E)) := by
    intro p
    by_cases h : p.IsMaximal ∧ p ≠ ⊥
    · have := h.1
      obtain ⟨g, hg⟩ := exists_injOn_primesOver E p h.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨fun _ => ⟨0, Module.finrank_pos⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using H
  refine ⟨fun P => g (P.under ℤ) P, ?_⟩
  intro P hP Q hQ hidx hcop
  have key := under_eq_of_not_coprime hP hQ hcop
  have := hP.1
  have := hQ.1
  have hbot : Q.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hQ.2
  have hprime : (Q.under ℤ).IsPrime := inferInstance
  have hmax : (Q.under ℤ).IsMaximal := hprime.isMaximal hbot
  simp only [key] at hidx
  refine hg (Q.under ℤ) hmax hbot ⟨hP.1, ⟨key.symm⟩⟩ ⟨hQ.1, ⟨rfl⟩⟩ hidx

theorem exists_tuple : ∃ n : {I : Ideal (𝓞 E) // I ≠ ⊥} → Fin (Module.finrank ℚ E) → ℕ,
    Function.Injective n ∧ ∀ I, ∏ i, n I i = absNorm I.1 := by
  classical
  obtain ⟨idx, hidx⟩ := exists_idx E
  have hmem : ∀ (I : Ideal (𝓞 E)), ∀ P ∈ normalizedFactors I, P ∈ primeSet E := by
    intro I P hP
    have hp := prime_of_normalized_factor P hP
    exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  refine ⟨fun I => intersection_update_fsHerm_neg_one (fun P => absNorm P) idx (normalizedFactors I.1), ?_, ?_⟩
  · intro I J hIJ
    have := position_inj (fun P : Ideal (𝓞 E) => absNorm P) idx (primeSet E)
      (fun P hP => one_lt_absNorm_of_mem hP) hidx (hmem I.1) (hmem J.1) hIJ
    apply Subtype.ext
    rw [← Ideal.prod_normalizedFactors_eq_self I.2, ← Ideal.prod_normalizedFactors_eq_self J.2,
      this]
  · intro I
    rw [prod_position, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self I.2]

theorem tsum_ideal_le (w : ℕ →* ℝ≥0∞) :
    ∑' I : {I : Ideal (𝓞 E) // I ≠ ⊥}, w (absNorm I.1) ≤ (∑' k, w k) ^ Module.finrank ℚ E := by
  obtain ⟨n, hinj, hn⟩ := exists_tuple E
  refine tsum_le_pow n hinj w _ (fun I => ?_)
  rw [← hn I, map_prod]

end PI.Residue
end

section
namespace PI.Residue

open NumberField
open scoped ENNReal NNReal

noncomputable def wt (s : ℝ) : ℕ →* ℝ≥0∞ where
  toFun n := (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞)
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, NNReal.mul_rpow, ENNReal.coe_mul]

theorem wt_apply (s : ℝ) (n : ℕ) : wt s n = (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) := rfl

theorem nnreal_of_ennreal {β : Type*} (f : β → ℝ≥0) (g : ℕ → ℝ≥0) (m : ℕ) (hg : Summable g)
    (h : ∑' b, (f b : ℝ≥0∞) ≤ (∑' k, (g k : ℝ≥0∞)) ^ m) :
    Summable f ∧ ∑' b, f b ≤ (∑' k, g k) ^ m := by
  rw [← ENNReal.coe_tsum hg, ← ENNReal.coe_pow] at h
  have hf : Summable f :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_top_of_le_ne_top ENNReal.coe_ne_top h)
  refine ⟨hf, ?_⟩
  rw [← ENNReal.coe_tsum hf] at h
  exact_mod_cast h

theorem zetaLePow : ZetaLePow := by
  intro E _ _ s hs
  have h := tsum_ideal_le E (wt s)
  have h0 : wt s 0 = 0 := by
    rw [wt_apply, Nat.cast_zero, NNReal.zero_rpow (by linarith : -s ≠ 0), ENNReal.coe_zero]
  rw [tsum_eq_zero_add' ENNReal.summable, h0, zero_add] at h
  simp only [wt_apply] at h
  have hg : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0) ^ (-s))) := by
    rw [← NNReal.summable_coe]
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s < -1))
    simpa using this
  obtain ⟨hf, hle⟩ := nnreal_of_ennreal
    (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => ((Ideal.absNorm I.1 : ℝ≥0) ^ (-s))) _ _ hg h
  constructor
  · have := NNReal.summable_coe.mpr hf
    simpa using this
  · have := NNReal.coe_le_coe.mpr hle
    rw [NNReal.coe_tsum, NNReal.coe_pow, NNReal.coe_tsum] at this
    simpa [idealZeta, zetaR] using this

end PI.Residue
end
