import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistWt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr

section
open MvPolynomial FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

variable {p q r s : ℕ}

theorem der_sum_apply {ι : Type*} (t : Finset ι) (D : ι → Derivation ℂ (Pol p q r s) (Pol p q r s))
    (f : Pol p q r s) : (∑ c ∈ t, D c) f = ∑ c ∈ t, D c f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

def der1 (a b : Ix p q) : Derivation ℂ (Pol p q r s) (Pol p q r s) :=
  ∑ c : Ix r s, if linePos (a, c) = true then (X (a, c) : Pol p q r s) • pderiv (b, c)
    else -((X (b, c) : Pol p q r s) • pderiv (a, c))

def der2 (c d : Ix r s) : Derivation ℂ (Pol p q r s) (Pol p q r s) :=
  ∑ a : Ix p q, if linePos (a, c) = true then (X (a, c) : Pol p q r s) • pderiv (a, d)
    else -((X (a, d) : Pol p q r s) • pderiv (a, c))

theorem leftRootDerivation_X (a b : Ix p q) (v : Ln p q r s) :
    der1 a b (X v : Pol p q r s) = if linePos (a, v.2) = true then (if v.1 = b then X (a, v.2) else 0)
      else (if v.1 = a then -X (b, v.2) else 0) := by
  classical
  rw [der1, der_sum_apply, Finset.sum_eq_single v.2]
  · obtain ⟨v1, v2⟩ := v
    by_cases h : linePos (a, v2) = true
    · simp only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases hb : v1 = b
      · subst hb; simp
      · simp [Pi.single_apply, hb]
    · simp only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases ha : v1 = a
      · subst ha; simp
      · simp [Pi.single_apply, ha]
  · intro c _ hc
    obtain ⟨v1, v2⟩ := v
    have h1 : (v1, v2) ≠ (b, c) := fun e => hc (by simp at e; exact e.2.symm)
    have h2 : (v1, v2) ≠ (a, c) := fun e => hc (by simp at e; exact e.2.symm)
    split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]
  · simp

theorem rightRootDerivation_X (c d : Ix r s) (v : Ln p q r s) :
    der2 c d (X v : Pol p q r s) = if linePos (v.1, c) = true then (if v.2 = d then X (v.1, c) else 0)
      else (if v.2 = c then -X (v.1, d) else 0) := by
  classical
  rw [der2, der_sum_apply, Finset.sum_eq_single v.1]
  · obtain ⟨v1, v2⟩ := v
    by_cases h : linePos (v1, c) = true
    · simp only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases hb : v2 = d
      · subst hb; simp
      · simp [Pi.single_apply, hb]
    · simp only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases ha : v2 = c
      · subst ha; simp
      · simp [Pi.single_apply, ha]
  · intro a _ hc
    obtain ⟨v1, v2⟩ := v
    have h1 : (v1, v2) ≠ (a, d) := fun e => hc (by simp at e; exact e.1.symm)
    have h2 : (v1, v2) ≠ (a, c) := fun e => hc (by simp at e; exact e.1.symm)
    split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]
  · simp

theorem leftRootOperator_eq_derivation (a b : Ix p q) (hab : a ≠ b) (hblk : ∀ c : Ix r s, linePos (a, c) = linePos (b, c))
    (f : Pol p q r s) : rai1 (r := r) (s := s) a b f = der1 a b f := by
  classical
  rw [rai1, der1, der_sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [Module.End.mul_apply, raiB, lowB, ← hblk c]
  by_cases h : linePos (a, c) = true
  · simp [h, smul_eq_mul]
  · have hne : (a, c) ≠ (b, c) := fun e => hab (by simp at e; exact e)
    simp only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]
    rw [pderiv_mul, pderiv_X_of_ne hne.symm]
    ring

theorem rightRootOperator_eq_derivation (c d : Ix r s) (hcd : c ≠ d) (hblk : ∀ a : Ix p q, linePos (a, c) = linePos (a, d))
    (f : Pol p q r s) : rai2 (p := p) (q := q) c d f = der2 c d f := by
  classical
  rw [rai2, der2, der_sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Module.End.mul_apply, raiB, lowB, ← hblk a]
  by_cases h : linePos (a, c) = true
  · simp [h, smul_eq_mul]
  · have hne : (a, c) ≠ (a, d) := fun e => hcd (by simp at e; exact e)
    simp only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]
    rw [pderiv_mul, pderiv_X_of_ne hne.symm]
    ring

section Kill

variable {m k : ℕ}

theorem leadT_der_rows (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (ρ : Fin m → Ix p q)
    (κ : Fin k → Ix r s) (t : ℕ)
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (X (ρ i₀, κ j)) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : Pol p q r s,
        ∀ j : Fin k, j.val < t → D (X (ρ i₀, κ j)) = e * X (ρ i₁, κ j)) :
    D (leadT (varMat ρ κ) t) = 0 := by
  unfold leadT
  split_ifs with hh
  · apply deriv_det_eq_zero_rows
    intro i
    rcases h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩
    · left
      intro j
      simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro j
        simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
        rw [he _ (by simp)]
        rfl
  · simp

theorem leadT_der_cols (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (ρ : Fin m → Ix p q)
    (κ : Fin k → Ix r s) (t : ℕ)
    (h : ∀ j₀ : Fin k, j₀.val < t → (∀ i : Fin m, i.val < t → D (X (ρ i, κ j₀)) = 0) ∨
      ∃ j₁ : Fin k, j₁.val < t ∧ j₁ ≠ j₀ ∧ ∃ e : Pol p q r s,
        ∀ i : Fin m, i.val < t → D (X (ρ i, κ j₀)) = e * X (ρ i, κ j₁)) :
    D (leadT (varMat ρ κ) t) = 0 := by
  unfold leadT
  split_ifs with hh
  · apply deriv_det_eq_zero
    intro j
    rcases h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩
    · left
      intro i
      simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro i
        simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
        rw [he _ (by simp)]
        rfl
  · simp

theorem shapeProd_der (D : Derivation ℂ (Pol p q r s) (Pol p q r s))
    (M : Matrix (Fin m) (Fin k) (Pol p q r s)) (α : List ℕ) (h : ∀ t, D (leadT M t) = 0) :
    D (shapeProd M α) = 0 := by
  unfold shapeProd
  apply deriv_prod_eq_zero
  intro t _
  exact deriv_pow_eq_zero _ _ _ (h _)

theorem leadingMinor_leftRootDerivation_pos (x y : Ix p q) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hpos : ∀ j, linePos (x, κ j) = true)
    (hcl : ∀ i₀ : Fin m, i₀.val < t → ρ i₀ = y → ∃ i₁ : Fin m, i₁.val < t ∧ ρ i₁ = x) :
    der1 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_rows
  intro i₀ hi₀
  by_cases hy : ρ i₀ = y
  · right
    obtain ⟨i₁, hi₁, hx⟩ := hcl i₀ hi₀ hy
    refine ⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), 1, fun j _ => ?_⟩
    rw [leftRootDerivation_X]
    simp [hpos j, hy, hx]
  · left
    intro j _
    rw [leftRootDerivation_X]
    simp [hpos j, hy]

theorem leadingMinor_leftRootDerivation_neg (x y : Ix p q) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ j, linePos (x, κ j) = false)
    (hcl : ∀ i₀ : Fin m, i₀.val < t → ρ i₀ = x → ∃ i₁ : Fin m, i₁.val < t ∧ ρ i₁ = y) :
    der1 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_rows
  intro i₀ hi₀
  by_cases hx : ρ i₀ = x
  · right
    obtain ⟨i₁, hi₁, hy⟩ := hcl i₀ hi₀ hx
    refine ⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun j _ => ?_⟩
    rw [leftRootDerivation_X]
    simp [hneg j, hy, hx]
  · left
    intro j _
    rw [leftRootDerivation_X]
    simp [hneg j, hx]

theorem leadingMinor_rightRootDerivation_pos (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hpos : ∀ i, linePos (ρ i, x) = true)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = y → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = x) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_cols
  intro j₀ hj₀
  by_cases hy : κ j₀ = y
  · right
    obtain ⟨j₁, hj₁, hx⟩ := hcl j₀ hj₀ hy
    refine ⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), 1, fun i _ => ?_⟩
    rw [rightRootDerivation_X]
    simp [hpos i, hy, hx]
  · left
    intro i _
    rw [rightRootDerivation_X]
    simp [hpos i, hy]

theorem leadingMinor_rightRootDerivation_neg (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ i, linePos (ρ i, x) = false)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = x → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = y) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_cols
  intro j₀ hj₀
  by_cases hx : κ j₀ = x
  · right
    obtain ⟨j₁, hj₁, hy⟩ := hcl j₀ hj₀ hx
    refine ⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun i _ => ?_⟩
    rw [rightRootDerivation_X]
    simp [hneg i, hy, hx]
  · left
    intro i _
    rw [rightRootDerivation_X]
    simp [hneg i, hx]

end Kill

theorem hwVec_der (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (a b c d : List ℤ)
    (h1 : ∀ t, D (leadT (varMat (fun i : Fin p => (Sum.inl i : Ix p q))
      (fun k : Fin r => (Sum.inl k : Ix r s))) t) = 0)
    (h2 : ∀ t, D (leadT (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
      (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) t) = 0)
    (h3 : ∀ t, D (leadT (varMat (fun j : Fin q => (Sum.inr j : Ix p q))
      (fun l : Fin s => (Sum.inr l : Ix r s))) t) = 0)
    (h4 : ∀ t, D (leadT (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
      (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) t) = 0) :
    D (hwVec p q r s a b c d) = 0 := by
  rw [hwVec]
  simp only [Derivation.leibniz, shapeProd_der D _ _ h1, shapeProd_der D _ _ h2,
    shapeProd_der D _ _ h3, shapeProd_der D _ _ h4, smul_zero, add_zero]

theorem vecRaise1 (a b c d : List ℤ) (x y : Ix p q) (hxy : posC x y) :
    der1 (r := r) (s := s) x y (hwVec p q r s a b c d) = 0 := by
  cases x with
  | inl i =>
    cases y with
    | inr _ => exact hxy.elim
    | inl i' =>
      have hii : i < i' := hxy
      have hne : (Sum.inl i : Ix p q) ≠ Sum.inl i' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inl.injEq] at e
        subst e
        exact ⟨i, by omega, rfl⟩
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inl.injEq] at e
        refine ⟨Fin.rev i', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
  | inr j =>
    cases y with
    | inl _ => exact hxy.elim
    | inr j' =>
      have hjj : j < j' := hxy
      have hne : (Sum.inr j : Ix p q) ≠ Sum.inr j' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inr.injEq] at e
        subst e
        exact ⟨j, by omega, rfl⟩
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inr.injEq] at e
        refine ⟨Fin.rev j', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega

theorem vecRaise2 (a b c d : List ℤ) (x y : Ix r s) (hxy : posC x y) :
    der2 (p := p) (q := q) x y (hwVec p q r s a b c d) = 0 := by
  cases x with
  | inl k =>
    cases y with
    | inr _ => exact hxy.elim
    | inl k' =>
      have hkk : k < k' := hxy
      have hne : (Sum.inl k : Ix r s) ≠ Sum.inl k' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inl.injEq] at e
        subst e
        exact ⟨k, by omega, rfl⟩
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inl.injEq] at e
        refine ⟨Fin.rev k', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega
  | inr l =>
    cases y with
    | inl _ => exact hxy.elim
    | inr l' =>
      have hll : l < l' := hxy
      have hne : (Sum.inr l : Ix r s) ≠ Sum.inr l' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inr.injEq] at e
        refine ⟨Fin.rev l', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inr.injEq] at e
        subst e
        exact ⟨l, by omega, rfl⟩
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)

end PI.FJMX
end
end

section
open FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

theorem posPart_pw (a : List ℤ) (ha : a.Pairwise (· ≥ ·)) : (PI.FJM.posPart a).Pairwise (· ≥ ·) := by
  rw [PI.FJM.posPart, List.pairwise_map]
  exact ha.imp fun h => by omega

theorem negPart_pw (b : List ℤ) (hb : b.Pairwise (· ≥ ·)) : (PI.FJM.negPart b).Pairwise (· ≥ ·) := by
  rw [PI.FJM.negPart, List.pairwise_reverse, List.pairwise_map]
  exact hb.imp fun h => by omega

theorem posPart_getD (a : List ℤ) (ha : ∀ v ∈ a, 0 < v) (i : ℕ) :
    ((PI.FJM.posPart a).getD i 0 : ℚ) = if h : i < a.length then ((a[i] : ℤ) : ℚ) else 0 := by
  by_cases h : i < a.length
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa [PI.FJM.posPart] using h)]
    simp only [PI.FJM.posPart, List.getElem_map]
    have hpos := ha _ (List.getElem_mem h)
    have := Int.toNat_of_nonneg hpos.le
    exact_mod_cast this
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa [PI.FJM.posPart] using not_lt.1 h)]
    simp

theorem negPart_getD (b : List ℤ) (hb : ∀ v ∈ b, v < 0) (j : ℕ) :
    ((PI.FJM.negPart b).getD j 0 : ℚ) =
      if h : j < b.length then -((b[b.length - 1 - j]'(by omega) : ℤ) : ℚ) else 0 := by
  by_cases h : j < b.length
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa [PI.FJM.negPart] using h)]
    simp only [PI.FJM.negPart, List.getElem_reverse, List.getElem_map, List.length_map]
    have hneg := hb _ (List.getElem_mem (l := b) (n := b.length - 1 - j) (by omega))
    have := Int.toNat_of_nonneg (show 0 ≤ -b[b.length - 1 - j] by omega)
    have h2 : ((-b[b.length - 1 - j]).toNat : ℚ) = ((-b[b.length - 1 - j] : ℤ) : ℚ) := by
      exact_mod_cast this
    rw [h2]
    push_cast
    ring
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa [PI.FJM.negPart] using not_lt.1 h)]
    simp

theorem pad_getD (a b : List ℤ) (n : ℕ) (hn : a.length + b.length ≤ n) (ha : ∀ v ∈ a, 0 < v)
    (hb : ∀ v ∈ b, v < 0) (i : ℕ) (hi : i < n) :
    (pad a (n - a.length - b.length) b).getD i 0 =
      ((PI.FJM.posPart a).getD i 0 : ℚ) - ((PI.FJM.negPart b).getD (n - 1 - i) 0 : ℚ) := by
  rw [posPart_getD a ha, negPart_getD b hb]
  rw [pad, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map]
  by_cases h1 : i < a.length
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h1,
      dif_pos h1, dif_neg (by omega)]
    simp
  · by_cases h2 : i < a.length + (n - a.length - b.length)
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
        dif_neg h1, dif_neg (by omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega), dif_neg h1, dif_pos (by omega)]
      simp only [neg_neg, sub_neg_eq_add, zero_add]
      congr 2
      simp
      omega

end PI.FJMX
end
end

section
open MvPolynomial FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

variable {p q r s : ℕ}

def leftPositiveIndicator (x : Ix p q) : Ln p q r s → ℕ := fun v => if v.1 = x ∧ linePos v = true then 1 else 0

def leftNegativeIndicator (x : Ix p q) : Ln p q r s → ℕ := fun v => if v.1 = x ∧ linePos v = false then 1 else 0

def rightPositiveIndicator (y : Ix r s) : Ln p q r s → ℕ := fun v => if v.2 = y ∧ linePos v = true then 1 else 0

def rightNegativeIndicator (y : Ix r s) : Ln p q r s → ℕ := fun v => if v.2 = y ∧ linePos v = false then 1 else 0

theorem weight_fin (w : Ln p q r s → ℕ) (m : Ln p q r s →₀ ℕ) :
    Finsupp.weight w m = ∑ v, m v * w v := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem monomialLeftWeight_eq_weight_sub (m : Ln p q r s →₀ ℕ) (x : Ix p q) :
    wt1 m x = (Finsupp.weight (leftPositiveIndicator x) m : ℤ) - (Finsupp.weight (leftNegativeIndicator x) m : ℤ) := by
  classical
  rw [weight_fin, weight_fin, wt1]
  push_cast
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro c _
    cases h : linePos (x, c) <;> simp [leftPositiveIndicator, leftNegativeIndicator, h]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    simp [leftPositiveIndicator, leftNegativeIndicator, hb]
  · simp

theorem monomialRightWeight_eq_weight_sub (m : Ln p q r s →₀ ℕ) (y : Ix r s) :
    wt2 m y = (Finsupp.weight (rightPositiveIndicator y) m : ℤ) - (Finsupp.weight (rightNegativeIndicator y) m : ℤ) := by
  classical
  rw [weight_fin, weight_fin, wt2]
  push_cast
  rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single y]
  · cases h : linePos (a, y) <;> simp [rightPositiveIndicator, rightNegativeIndicator, h]
  · intro c _ hc
    simp [rightPositiveIndicator, rightNegativeIndicator, hc]
  · simp

theorem leftAction_diagonal_of (hW : FormWt1) (P : Pol p q r s) (x : Ix p q) (W : ℤ)
    (h : ∀ m, coeff m P ≠ 0 → wt1 m x = W) :
    fockAct1 p q r s (Eab x x) P = ((((W : ℚ) + sh1 p q r s x : ℚ)) : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have e : monomial m (coeff m P) = coeff m P • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hW, h m (mem_support_iff.1 hm), smul_comm]

theorem rightAction_diagonal_of (hW : FormWt2) (P : Pol p q r s) (y : Ix r s) (W : ℤ)
    (h : ∀ m, coeff m P ≠ 0 → wt2 m y = W) :
    fockAct2 p q r s (Eab y y) P = ((((W : ℚ) + sh2 p q r s y : ℚ)) : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have e : monomial m (coeff m P) = coeff m P • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hW, h m (mem_support_iff.1 hm), smul_comm]

theorem mem_wtSub1 (hW : FormWt1) (P : Pol p q r s) (μ : Ix p q → ℚ)
    (h : ∀ x, ∃ W : ℤ, (W : ℚ) + sh1 p q r s x = μ x ∧ ∀ m, coeff m P ≠ 0 → wt1 m x = W) :
    P ∈ wtSub (fockAct1 p q r s) μ := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x
  obtain ⟨W, hWx, hm⟩ := h x
  rw [LinearMap.sub_apply, leftAction_diagonal_of hW P x W hm, hWx]
  simp

theorem mem_wtSub2 (hW : FormWt2) (P : Pol p q r s) (μ : Ix r s → ℚ)
    (h : ∀ y, ∃ W : ℤ, (W : ℚ) + sh2 p q r s y = μ y ∧ ∀ m, coeff m P ≠ 0 → wt2 m y = W) :
    P ∈ wtSub (fockAct2 p q r s) μ := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y
  obtain ⟨W, hWy, hm⟩ := h y
  rw [LinearMap.sub_apply, rightAction_diagonal_of hW P y W hm, hWy]
  simp

theorem posC_ne {n m : ℕ} (x y : Ix n m) (h : posC x y) : x ≠ y := by
  cases x <;> cases y <;> simp only [posC] at h <;> first | exact h.elim | (intro e; simp at e; omega)

theorem isDiagonalBlockIndex_left_of_positiveRoot (x y : Ix p q) (h : posC x y) (c : Ix r s) : linePos (x, c) = linePos (y, c) := by
  cases x <;> cases y <;> cases c <;> simp only [posC] at h <;> first | exact h.elim | rfl

theorem isDiagonalBlockIndex_right_of_positiveRoot (x y : Ix r s) (h : posC x y) (a : Ix p q) : linePos (a, x) = linePos (a, y) := by
  cases x <;> cases y <;> cases a <;> simp only [posC] at h <;> first | exact h.elim | rfl

theorem hwVec_hom (w : Ln p q r s → ℕ) (a b c d : List ℤ) (d1 d2 d3 d4 : ℕ)
    (h1 : IsWeightedHomogeneous w (shapeProd (varMat (fun i : Fin p => (Sum.inl i : Ix p q))
      (fun k : Fin r => (Sum.inl k : Ix r s))) (posPart a)) d1)
    (h2 : IsWeightedHomogeneous w (shapeProd (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
      (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) (negPart b)) d2)
    (h3 : IsWeightedHomogeneous w (shapeProd (varMat (fun j : Fin q => (Sum.inr j : Ix p q))
      (fun l : Fin s => (Sum.inr l : Ix r s))) (posPart c)) d3)
    (h4 : IsWeightedHomogeneous w (shapeProd (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
      (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) (negPart d)) d4) :
    IsWeightedHomogeneous w (hwVec p q r s a b c d) (d1 + d2 + d3 + d4) := by
  unfold hwVec
  exact ((h1.mul h2).mul h3).mul h4

theorem wtVec1 (a b c d : List ℤ) (hd : ShapeData p q r s a b c d) (x : Ix p q) :
    ∃ W : ℤ, (W : ℚ) + sh1 p q r s x = wtOf1 p q r s a b c d x ∧
      ∀ m, coeff m (hwVec p q r s a b c d) ≠ 0 → wt1 m x = W := by
  obtain ⟨ha, hc, hb, hdd, hpa, hpb, hpc, hpd, h1, h2, h3, h4⟩ := hd
  cases x with
  | inl i₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftPositiveIndicator (Sum.inl i₀)) a b c d _ 0 0 0
      (shapeProd_hom_row _ _ _ i₀ (fun i k => by simp [leftPositiveIndicator, linePos]) _ (posPart_pw a hpa))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftNegativeIndicator (Sum.inl i₀)) a b c d 0 _ 0 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftNegativeIndicator, linePos]) _)
      (shapeProd_hom_row _ _ _ (Fin.rev i₀) (fun i l => by simp [leftNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw b hpb))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
    refine ⟨((posPart a).getD i₀ 0 : ℤ) - ((negPart b).getD (Fin.rev i₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev i₀).val = p - 1 - i₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf1, ofBlocks]
      rw [pad_getD a b p h1 ha hb i₀.val i₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialLeftWeight_eq_weight_sub, hP hm, hN hm]
      simp
  | inr j₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftPositiveIndicator (Sum.inr j₀)) a b c d 0 0 _ 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_row _ _ _ j₀ (fun j l => by simp [leftPositiveIndicator, linePos]) _ (posPart_pw c hpc))
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [leftPositiveIndicator, linePos]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftNegativeIndicator (Sum.inr j₀)) a b c d 0 0 0 _
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [leftNegativeIndicator, linePos]) _)
      (shapeProd_hom_row _ _ _ (Fin.rev j₀) (fun j k => by simp [leftNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw d hpd))
    refine ⟨((posPart c).getD j₀ 0 : ℤ) - ((negPart d).getD (Fin.rev j₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev j₀).val = q - 1 - j₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf1, ofBlocks]
      rw [pad_getD c d q h2 hc hdd j₀.val j₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialLeftWeight_eq_weight_sub, hP hm, hN hm]
      simp

theorem wtVec2 (a b c d : List ℤ) (hd : ShapeData p q r s a b c d) (y : Ix r s) :
    ∃ W : ℤ, (W : ℚ) + sh2 p q r s y = wtOf2 p q r s a b c d y ∧
      ∀ m, coeff m (hwVec p q r s a b c d) ≠ 0 → wt2 m y = W := by
  obtain ⟨ha, hc, hb, hdd, hpa, hpb, hpc, hpd, h1, h2, h3, h4⟩ := hd
  cases y with
  | inl k₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightPositiveIndicator (Sum.inl k₀)) a b c d _ 0 0 0
      (shapeProd_hom_col _ _ _ k₀ (fun i k => by simp [rightPositiveIndicator, linePos]) _ (posPart_pw a hpa))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightPositiveIndicator, linePos]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightNegativeIndicator (Sum.inl k₀)) a b c d 0 0 0 _
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightNegativeIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_col _ _ _ (Fin.rev k₀) (fun j k => by simp [rightNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw d hpd))
    refine ⟨((posPart a).getD k₀ 0 : ℤ) - ((negPart d).getD (Fin.rev k₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev k₀).val = r - 1 - k₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf2, ofBlocks]
      rw [pad_getD a d r h3 ha hdd k₀.val k₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialRightWeight_eq_weight_sub, hP hm, hN hm]
      simp
  | inr l₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightPositiveIndicator (Sum.inr l₀)) a b c d 0 0 _ 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightPositiveIndicator, linePos]) _)
      (shapeProd_hom_col _ _ _ l₀ (fun j l => by simp [rightPositiveIndicator, linePos]) _ (posPart_pw c hpc))
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightPositiveIndicator]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightNegativeIndicator (Sum.inr l₀)) a b c d 0 _ 0 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_col _ _ _ (Fin.rev l₀) (fun i l => by simp [rightNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw b hpb))
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightNegativeIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightNegativeIndicator]) _)
    refine ⟨((posPart c).getD l₀ 0 : ℤ) - ((negPart b).getD (Fin.rev l₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev l₀).val = s - 1 - l₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf2, ofBlocks]
      rw [pad_getD c b s h4 hc hb l₀.val l₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialRightWeight_eq_weight_sub, hP hm, hN hm]
      simp

theorem vecHW1_of (hW : FormWt1) (hR : FormRaise1) : VecHW1 := by
  intro p q r s a b c d hd
  refine Submodule.mem_inf.2 ⟨mem_wtSub1 hW _ _ (wtVec1 a b c d hd), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x y hxy
  rw [hR p q r s x y (posC_ne x y hxy), leftRootOperator_eq_derivation x y (posC_ne x y hxy) (isDiagonalBlockIndex_left_of_positiveRoot x y hxy)]
  exact vecRaise1 a b c d x y hxy

theorem vecHW2_of (hW : FormWt2) (hR : FormRaise2) : VecHW2 := by
  intro p q r s a b c d hd
  refine Submodule.mem_inf.2 ⟨mem_wtSub2 hW _ _ (wtVec2 a b c d hd), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x y hxy
  rw [hR p q r s x y (posC_ne x y hxy), rightRootOperator_eq_derivation x y (posC_ne x y hxy) (isDiagonalBlockIndex_right_of_positiveRoot x y hxy)]
  exact vecRaise2 a b c d x y hxy

end PI.FJMX
end
end

section
namespace PI.FJMX



end PI.FJMX
end
