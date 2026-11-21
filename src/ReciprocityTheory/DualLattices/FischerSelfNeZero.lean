import ReciprocityTheory.DualLattices.FischerAdjointStatement

section
noncomputable section

open MvPolynomial Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def fw (A : Fin ν × ι →₀ ℕ) : ℂ := ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

private theorem finsupp_prod_factorial_add_single_one (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = B.prod (fun _ e => e.factorial) * (B v + 1) := by
  have hv : v ∈ insert v B.support := Finset.mem_insert_self v B.support
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hx
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rwa [if_neg (Ne.symm hxv), add_zero] at hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert v B.support
  have hrest : ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial
      = ∏ x ∈ (insert v B.support).erase v, (B x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, add_zero]
  calc (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = ∏ x ∈ insert v B.support, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => Nat.factorial_zero)
    _ = ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) v).factorial
          * ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        (Finset.mul_prod_erase _ (fun x => ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial) hv).symm
    _ = (B v).factorial * (∏ x ∈ (insert v B.support).erase v, (B x).factorial) * (B v + 1) := by
        rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]; ring
    _ = (∏ x ∈ insert v B.support, (B x).factorial) * (B v + 1) := by
        rw [← Finset.mul_prod_erase _ _ hv]
    _ = B.prod (fun _ e => e.factorial) * (B v + 1) := by
        rw [Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => Nat.factorial_zero)]

theorem fw_add_single (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    fw (B + Finsupp.single v 1) = fw B * ((B v : ℂ) + 1) := by
  unfold fw
  rw [finsupp_prod_factorial_add_single_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem fischer_eq_sum (P Q : MvPolynomial (Fin ν × ι) ℂ) (S : Finset (Fin ν × ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), P.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A P = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm

theorem fischer_add_left (P P' Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (P + P') Q = fischer P Q + fischer P' Q := by
  have hsub : (P + P').support ⊆ P.support ∪ P'.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hA
    rw [Finset.mem_union, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    rw [h.1, h.2, add_zero] at hA
    exact hA rfl
  rw [fischer_eq_sum (P + P') Q (P.support ∪ P'.support) hsub,
    fischer_eq_sum P Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx),
    fischer_eq_sum P' Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem fischer_smul_left (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (c • P) Q = c * fischer P Q := by
  have hsub : (c • P).support ⊆ P.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul] at hA
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hA
    rw [h, smul_zero]
  rw [fischer_eq_sum (c • P) Q P.support hsub,
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fischer_add_right (P Q Q' : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (Q + Q') = fischer P Q + fischer P Q' := by
  rw [fischer_eq_sum P (Q + Q') P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q' P.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add, map_add]
  ring

theorem fischer_smul_right (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (c • Q) = starRingEnd ℂ c * fischer P Q := by
  rw [fischer_eq_sum P (c • Q) P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul]
  ring

theorem fischer_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial (Fin ν × ι) ℂ)
    (f : α → MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (∑ i ∈ s, f i) = ∑ i ∈ s, fischer P (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum P 0 P.support (Finset.Subset.refl _)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

theorem fischer_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin ν × ι) ℂ)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum 0 Q ∅ (by simp)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

theorem fischer_C_left (c : ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (C c) Q = c * starRingEnd ℂ (coeff 0 Q) := by
  have hsub : (C c : MvPolynomial (Fin ν × ι) ℂ).support ⊆ {0} := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hA
    rw [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (fun e => h e.symm))
  rw [fischer_eq_sum (C c) Q {0} hsub, Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl]
  simp [fw]

private theorem fischer_eq_sum_of_support_subset (P Q : MvPolynomial (Fin ν × ι) ℂ)
    (S : Finset (Fin ν × ι →₀ ℕ)) (hS : Q.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), Q.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A Q = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_right _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm

private theorem fischer_monomial_right (P : MvPolynomial (Fin ν × ι) ℂ)
    (m : Fin ν × ι →₀ ℕ) (b : ℂ) :
    fischer P (monomial m b) = coeff m P * starRingEnd ℂ b * fw m := by
  rw [fischer_eq_sum_of_support_subset P (monomial m b) {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem fischer_mul_X (P Q : MvPolynomial (Fin ν × ι) ℂ) (v : Fin ν × ι) :
    fischer (P * X v) Q = fischer P (pderiv v Q) := by
  induction Q using MvPolynomial.induction_on'
  next m b =>
    rw [MvPolynomial.pderiv_monomial, fischer_monomial_right, fischer_monomial_right,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have hv : m v ≠ 0 := Finsupp.mem_support_iff.1 h
      have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := by
        ext x
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hx
        · subst hx
          omega
        · omega
      have hw : fw m = fw (m - Finsupp.single v 1) * (m v : ℂ) := by
        have h1 := fw_add_single (m - Finsupp.single v 1) v
        rw [hm, Finsupp.tsub_apply, Finsupp.single_eq_same,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv), Nat.cast_one, sub_add_cancel] at h1
        exact h1
      rw [hw, map_mul, map_natCast]
      ring
    · have hv : m v = 0 := by simpa [Finsupp.mem_support_iff] using h
      rw [hv]
      simp
  next Q₁ Q₂ h₁ h₂ =>
    rw [fischer_add_right, map_add, fischer_add_right, h₁, h₂]

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem rowSubst_X (g : Matrix (Fin ν) (Fin ν) ℂ) (p : Fin ν × ι) :
    rowSubst g (X p) = ∑ l, C (g l p.1) * X (l, p.2) := by
  simp [rowSubst]

theorem rowSubst_C (g : Matrix (Fin ν) (Fin ν) ℂ) (c : ℂ) :
    rowSubst g (C c : MvPolynomial (Fin ν × ι) ℂ) = C c := by
  simp [rowSubst]

theorem constantCoeff_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    constantCoeff (rowSubst h Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [rowSubst_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => simp [map_mul, hp, rowSubst_X]

theorem coeff_zero_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    coeff 0 (rowSubst h Q) = coeff 0 Q := by
  exact constantCoeff_rowSubst h Q

theorem pderiv_rowSubst_X (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι) (s : Fin ν × ι) :
    pderiv (k, a) (rowSubst h (X s : MvPolynomial (Fin ν × ι) ℂ)) =
      if s.2 = a then C (h k s.1) else 0 := by
  rw [rowSubst_X, map_sum]
  by_cases hs : s.2 = a
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]

theorem pderiv_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    pderiv (k, a) (rowSubst h Q) = ∑ m, C (h k m) * rowSubst h (pderiv (m, a) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [rowSubst_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e1 : ∀ m, rowSubst h (pderiv (m, a) (X n : MvPolynomial (Fin ν × ι) ℂ)) =
        if n = (m, a) then 1 else 0 := by
      intro m
      rw [pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    have e2 : ∑ m, C (h k m) * (rowSubst h p * (if n = (m, a) then 1 else 0)) =
        rowSubst h p * (if n.2 = a then C (h k n.1) else 0) := by
      by_cases hn : n.2 = a
      · rw [if_pos hn, Finset.sum_eq_single n.1]
        · rw [if_pos (show n = (n.1, a) from Prod.ext rfl hn)]
          ring
        · intro m _ hm
          rw [if_neg (fun h' => hm (congrArg Prod.fst h').symm)]
          ring
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · rw [if_neg hn, mul_zero]
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [if_neg (fun h' => hn (congrArg Prod.snd h'))]
        ring
    rw [map_mul, Derivation.leibniz, hp, pderiv_rowSubst_X, smul_eq_mul, smul_eq_mul, ← e2,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, e1]
    ring

theorem fischer_rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    rw [rowSubst_C, fischer_C_left, fischer_C_left, coeff_zero_rowSubst]
  | add p q hp hq =>
    rw [map_add, fischer_add_left, fischer_add_left, hp, hq]
  | mul_X p n hp =>
    rcases n with ⟨k, a⟩
    rw [map_mul, rowSubst_X, Finset.mul_sum, fischer_sum_left, fischer_mul_X, pderiv_rowSubst,
      fischer_sum_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_left_comm, MvPolynomial.C_mul', fischer_smul_left, fischer_mul_X, hp, MvPolynomial.C_mul',
      fischer_smul_right]
    simp [Matrix.conjTranspose_apply]

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def vw (p : Fin ν × ι) : ℕ := 2 ^ (ν - 1 - (p.1 : ℕ))

def wt (A : Fin ν × ι →₀ ℕ) : ℕ := A.sum fun p e => e * vw p

theorem wt_add (A B : Fin ν × ι →₀ ℕ) : wt (A + B) = wt A + wt B := by
  unfold wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

def tor (s : ℂ) : Matrix (Fin ν) (Fin ν) ℂ := Matrix.diagonal fun k => s ^ (2 ^ (ν - 1 - (k : ℕ)))

def comp (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : MvPolynomial (Fin ν × ι) ℂ :=
  ∑ A ∈ P.support.filter (fun A => wt A = d), monomial A (coeff A P)

def WtGe (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d ≤ wt A

def WtGt (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d < wt A

theorem WtGt.ge {d : ℕ} {P : MvPolynomial (Fin ν × ι) ℂ} (h : WtGt d P) : WtGe d P :=
  fun A hA => le_of_lt (h A hA)

theorem WtGt.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGt d P) (h2 : WtGt d Q) :
    WtGt d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]

theorem WtGe.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe d Q) :
    WtGe d (P + Q) := by
  intro A hA
  rcases Finset.mem_union.mp (MvPolynomial.support_add hA) with h | h
  exacts [h1 A h, h2 A h]

theorem WtGe.mul {d e : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe e Q) :
    WtGe (d + e) (P * Q) := by
  intro A hA
  obtain ⟨B, hB, B', hB', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hA)
  rw [wt_add]
  have := h1 B hB
  have := h2 B' hB'
  omega

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem fischer_self_ne_zero (P : MvPolynomial (Fin ν × ι) ℂ) (hP : P ≠ 0) : fischer P P ≠ 0 := by
  intro h0
  have hsum : fischer P P = ((∑ A ∈ P.support,
      ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold fischer
    rw [Finset.union_self]
    push_cast
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Finsupp.prod]
    push_cast
    ring
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hP (MvPolynomial.support_eq_empty.mp h))
  have hpos : 0 < ∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
    refine Finset.sum_pos (fun A hA => ?_) hne
    have h1 : coeff A P ≠ 0 := MvPolynomial.mem_support_iff.mp hA
    have h2 : 0 < ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun _ _ => Nat.factorial_pos _
    have h3 : 0 < ‖coeff A P‖ ^ 2 := by positivity
    positivity
  rw [hsum] at h0
  have h4 : (∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) = 0 := by
    exact_mod_cast h0
  linarith

theorem rowSubst_mul (g h : Matrix (Fin ν) (Fin ν) ℂ) (P : MvPolynomial (Fin ν × ι) ℂ) :
    rowSubst h (rowSubst g P) = rowSubst (h * g) P := by
  have key : (rowSubst (ι := ι) h).comp (rowSubst g) = rowSubst (h * g) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, rowSubst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact congrArg (fun F => F P) key

theorem rowSubst_one (P : MvPolynomial (Fin ν × ι) ℂ) : rowSubst (1 : Matrix (Fin ν) (Fin ν) ℂ) P = P := by
  have h : (fun p : Fin ν × ι => ∑ l, C ((1 : Matrix (Fin ν) (Fin ν) ℂ) l p.1) * X (l, p.2)) = X := by
    funext p
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl
      simp [Matrix.one_apply_ne hl]
    · simp
  unfold rowSubst
  rw [h, MvPolynomial.aeval_X_left_apply]

end ReciprocityTheory.PGsh
end
end
