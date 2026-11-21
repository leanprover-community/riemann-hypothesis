import Formalism.GradedWeylDivisibility.StatementC

section
open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma pairW_apply {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) (b : Fin r)
    (t : Fin n) :
    pairW l j v (b, t) = if v.2 = j then (if (v.1, l) = (b, t) then 1 else 0)
      else (if v = (b, t) then 1 else 0) := by
  classical
  unfold pairW
  split_ifs <;> simp_all [Finsupp.single_apply]

theorem lcplead_weight_apply {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (d : Fin r × Fin n →₀ ℕ)
    (b : Fin r) (t : Fin n) :
    Finsupp.weight (pairW l j) d (b, t) =
      if t = l then d (b, l) + d (b, j) else if t = j then 0 else d (b, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, pairW_apply, smul_eq_mul]
  split_ifs with h1 h2
  · subst h1
    rw [Fintype.sum_eq_add (b, t) (b, j) (by simp [hlj])]
    · simp [hlj]
    · rintro ⟨a, s⟩ ⟨ha1, ha2⟩
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]
  · subst h2
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨a, s⟩ := x
    by_cases hs : s = t <;> simp_all [Prod.ext_iff]
  · rw [Fintype.sum_eq_single (b, t)]
    · simp [h2]
    · rintro ⟨a, s⟩ hx
      have h1' : l ≠ t := Ne.symm h1
      by_cases hs : s = j <;> simp_all [Prod.ext_iff]

section
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}

theorem lcplead_hom_row (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) : m (b, l) + m (b, j) = ω (b, l) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b l, if_pos rfl]

theorem lcplead_hom_off (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) (t : Fin n) (htl : t ≠ l) (htj : t ≠ j) : m (b, t) = ω (b, t) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b t, if_neg htl, if_neg htj]

private lemma support_eq_of_pairW_homogeneous_of_erase_eq (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m m' : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (hm' : m' ∈ g.support) (h1 : m' (a0, l) = m (a0, l))
    (h2 : (m'.erase (a0, l)).erase (a0, j) = (m.erase (a0, l)).erase (a0, j)) : m' = m := by
  ext v
  by_cases hv1 : v = (a0, l)
  · rw [hv1, h1]
  by_cases hv2 : v = (a0, j)
  · have e1 := lcplead_hom_row hlj hg hm a0
    have e2 := lcplead_hom_row hlj hg hm' a0
    rw [hv2]; omega
  have := congrArg (fun f => f v) h2
  simpa [Finsupp.erase_ne hv1, Finsupp.erase_ne hv2] using this

theorem lcplead_coeff_peel (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    coeff ((m.erase (a0, l)).erase (a0, j)) (peel l j a0 (m (a0, l)) g) = coeff m g := by
  classical
  unfold peel
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' hm' hne
    rw [Finset.mem_filter] at hm'
    rw [if_neg]
    intro heq
    exact hne (support_eq_of_pairW_homogeneous_of_erase_eq hlj a0 hg hm hm'.1 hm'.2 heq)
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hm, rfl⟩)).elim

theorem lcplead_mem_support_peel (a0 : Fin r) (k : ℕ) {g : MvPolynomial (Fin r × Fin n) B}
    {p : Fin r × Fin n →₀ ℕ} (hp : p ∈ (peel l j a0 k g).support) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ p = (m.erase (a0, l)).erase (a0, j) := by
  classical
  unfold peel at hp
  obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hp)
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, hm.2, Finset.mem_singleton.mp (support_monomial_subset hpm)⟩

theorem lcplead_recon (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    m = Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (ω (a0, l) - m (a0, l)) +
      (m.erase (a0, l)).erase (a0, j) := by
  have h := lcplead_hom_row hlj hg hm a0
  have hne : ((a0, l) : Fin r × Fin n) ≠ (a0, j) := by simp [hlj]
  ext v
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply]
  by_cases h1 : v = (a0, l)
  · subst h1; simp [hne, Ne.symm hlj]
  · by_cases h2 : v = (a0, j)
    · subst h2; simp [hne]; omega
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

end

theorem lcplead_cmIdx_val {r n : ℕ} (b : Fin r) (t : Fin n) :
    ((cmIdx r n (b, t) : Fin (n * r)) : ℕ) = b + r * t := by
  simp [cmIdx, finProdFinEquiv]

theorem lcplead_cmIdx_lt {r n : ℕ} {b a0 : Fin r} {t l : Fin n}
    (h : cmIdx r n (b, t) < cmIdx r n (a0, l)) : t < l ∨ (t = l ∧ b < a0) := by
  have h' : (b : ℕ) + r * t < a0 + r * l := by
    have := Fin.lt_def.mp h
    rwa [lcplead_cmIdx_val, lcplead_cmIdx_val] at this
  rcases lt_trichotomy (t : ℕ) l with h1 | h1 | h1
  · exact Or.inl (Fin.lt_def.mpr h1)
  · refine Or.inr ⟨Fin.ext h1, Fin.lt_def.mpr ?_⟩
    rw [h1] at h'
    exact Nat.lt_of_add_lt_add_right h'
  · exfalso
    have h2 := Nat.mul_le_mul_left r (show (l : ℕ) + 1 ≤ t from h1)
    have h3 := a0.isLt
    rw [Nat.mul_add, mul_one] at h2
    omega

end Formalism.GradedWeylDivisibility
end
end

section
open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem toLex_lt_of_eq_of_lt_at {N : ℕ} {a b : Fin N →₀ ℕ} (i : Fin N)
    (h1 : ∀ i', i' < i → a i' = b i') (h2 : a i < b i) : toLex a < toLex b := by
  first
  | exact Finsupp.lex_lt_iff.2 ⟨i, h1, h2⟩
  | exact Finsupp.lex_def.2 ⟨i, h1, h2⟩
  | exact ⟨i, h1, h2⟩

private theorem domCongr_cmIdx_apply_eq {r n : ℕ} (m : Fin r × Fin n →₀ ℕ)
    (x : Fin r × Fin n) :
    Finsupp.domCongr (cmIdx r n) m (cmIdx r n x) = m x := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (simp [Finsupp.domCongr_apply]; done)
  | rfl

private theorem toSyn_le_toSyn_degree_of_mem_support {σ R : Type*} [CommSemiring R] (M : MonomialOrder σ)
    {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    M.toSyn d ≤ M.toSyn (M.degree f) := by
  first
  | exact M.le_degree hd
  | (unfold MonomialOrder.degree; rw [AddEquiv.apply_symm_apply]; exact Finset.le_sup hd)

theorem sliceLeading : PeelLead := by
  unfold PeelLead
  intro B _ _ r n l j hlj a0 ω g K hg hω hK htop
  have hlj' : l ≠ j := ne_of_lt hlj
  have hd : (colLex r n).degree (peel l j a0 K g) ∈
      (peel l j a0 K g).support :=
    (colLex r n).degree_mem_support hK
  obtain ⟨m0, hm0, hm0K, hd_eq⟩ := lcplead_mem_support_peel a0 K hd
  have hm0_eq := lcplead_recon hlj' a0 hg hm0
  rw [hm0K, ← hd_eq] at hm0_eq
  rw [← hm0_eq]
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hm0
  have hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0 := by
    intro m hm
    rcases lt_trichotomy (m (a0, l)) K with hlt | heq | hgt
    · apply le_of_lt
      apply colLex_lt_iff.2
      refine toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_
      · intro i' hi'
        obtain ⟨⟨b, t⟩, rfl⟩ := (cmIdx r n).surjective i'
        rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]
        rcases lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩
        · have htl : t ≠ l := ne_of_lt ht
          have htj : t ≠ j := ne_of_lt (lt_trans ht hlj)
          rw [lcplead_hom_off hlj' hg hm b t htl htj,
            lcplead_hom_off hlj' hg hm0 b t htl htj]
        · rw [ht]
          have h1 := lcplead_hom_row hlj' hg hm b
          have h2 := lcplead_hom_row hlj' hg hm0 b
          have h3 := hω b hb
          omega
      · rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]
        exact hlt
    · have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [heq] at hc
      have he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support := by
        rw [mem_support_iff, hc]
        exact mem_support_iff.1 hm
      have hle := toSyn_le_toSyn_degree_of_mem_support (colLex r n) he
      have hm_eq := lcplead_recon hlj' a0 hg hm
      rw [heq] at hm_eq
      rw [hm_eq, hm0_eq]
      simp only [map_add]
      first
      | exact add_le_add le_rfl hle
      | exact add_le_add_left hle _
      | gcongr
    · exfalso
      have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [htop _ hgt, coeff_zero] at hc
      exact mem_support_iff.1 hm hc.symm
  exact (colLex r n).toSyn.injective
    (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0))
      (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))

end Formalism.GradedWeylDivisibility
end
end
