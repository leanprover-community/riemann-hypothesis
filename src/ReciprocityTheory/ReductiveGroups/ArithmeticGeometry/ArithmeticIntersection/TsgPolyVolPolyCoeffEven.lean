import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

section
namespace ReciprocityTheory.ChartRestriction.G.AI


theorem symm_piecewise_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s t : Finset (Fin n))
    (hst : s.card = t.card) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (t.piecewise (fun _ => x) fun _ => y) := by
  classical
  have e : ∀ c : Bool, {a // decide (a ∈ t) = c} ≃ {b // decide (b ∈ s) = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      cases c
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = false) = tᶜ := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = false) = sᶜ := by ext; simp
        rw [h1, h2, Finset.card_compl, Finset.card_compl, hst]
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = true) = t := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = true) = s := by ext; simp
        rw [h1, h2, hst])
  have hσ : ∀ i, (Equiv.ofFiberEquiv e i ∈ s ↔ i ∈ t) := fun i => by
    have := Equiv.ofFiberEquiv_map e i
    rw [← decide_eq_decide]
    exact this
  have hfun : (s.piecewise (fun _ => x) fun _ => y) ∘ (Equiv.ofFiberEquiv e) =
      t.piecewise (fun _ => x) fun _ => y := by
    funext i
    rw [Function.comp_apply]
    by_cases hi : i ∈ t
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ ((hσ i).2 hi)]
    · have hi' : Equiv.ofFiberEquiv e i ∉ s := fun h => hi ((hσ i).1 h)
      first
        | rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi']
        | rw [Finset.piecewise_eq_of_not_mem _ _ _ hi, Finset.piecewise_eq_of_not_mem _ _ _ hi']
  rw [← hfun, hI]

theorem symm_piecewise_eq_mix {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s : Finset (Fin n)) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (mix s.card x y) := by
  classical
  set t : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) < s.card with ht_def
  have ht : t.card = s.card := by
    have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
    have hmap : t.map Fin.valEmbedding = Finset.range s.card := by
      ext m
      simp only [ht_def, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hm
        exact ⟨⟨m, by omega⟩, hm, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]
  rw [symm_piecewise_eq I hI x y s t ht.symm]
  congr 1
  funext i
  simp [ht_def, mix, Finset.piecewise]

theorem symm_expand {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (c : ℝ) :
    I (fun _ => y + c • x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c ^ j * I (mix j x y) := by
  classical
  have h1 : (fun _ : Fin n => y + c • x) = (fun _ => c • x) + (fun _ => y) := by
    funext i
    simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  have h2 : ∀ s : Finset (Fin n),
      I (s.piecewise (fun _ => c • x) fun _ => y) = c ^ s.card * I (mix s.card x y) := by
    intro s
    have h3 : (s.piecewise (fun _ => c • x) fun _ => y) =
        s.piecewise (fun i => c • (s.piecewise (fun _ => x) (fun _ => y)) i)
          (s.piecewise (fun _ => x) fun _ => y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [h3, MultilinearMap.map_piecewise_smul, symm_piecewise_eq_mix I hI, Finset.prod_const, smul_eq_mul]
  simp only [h2]
  have h4 := Finset.sum_powerset_apply_card (f := fun k => c ^ k * I (mix k x y))
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h4
  rw [h4]
  simp only [nsmul_eq_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AI

theorem symm_swap_nat {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (f : ℕ → V) (a b : ℕ)
    (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  have h := hI (Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩) (fun j => f j)
  refine h.symm.trans (congrArg I (funext fun j => ?_))
  show f ((Equiv.swap (⟨a, ha⟩ : Fin n) ⟨b, hb⟩ j : Fin n) : ℕ) =
    f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)
  refine congrArg f ?_
  by_cases h1 : (j : ℕ) = a
  · rw [if_pos h1]
    have hj : j = ⟨a, ha⟩ := Fin.ext h1
    simp [hj]
  · by_cases h2 : (j : ℕ) = b
    · rw [if_neg h1, if_pos h2]
      have hj : j = ⟨b, hb⟩ := Fin.ext h2
      simp [hj]
    · have h1' : j ≠ ⟨a, ha⟩ := fun h => h1 (congrArg Fin.val h)
      have h2' : j ≠ ⟨b, hb⟩ := fun h => h2 (congrArg Fin.val h)
      rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne h1' h2']

def interp {VW : Type*} (k i : ℕ) (x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j = 0 then x₂ else if j < 1 + 2 * i then x₁ else if j < 1 + 2 * k then x₂ else a

def consWord {VW : Type*} (k i : ℕ) (x x₁ x₂ a : VW) : ℕ → VW :=
  fun j => if j < 2 then x else if j = 2 then x₂ else if j < 3 + 2 * i then x₁ else
    if j < 1 + 2 * k then x₂ else a

theorem cons_cons_word {VW : Type*} (D k i : ℕ) (hk : 1 ≤ k) (x x₁ x₂ a : VW) :
    (Fin.cons x (Fin.cons x (word D k i x₁ x₂ a)) : Fin (D + 2) → VW) =
      fun j : Fin (D + 2) => consWord k i x x₁ x₂ a j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [consWord]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [consWord]
    · simp only [Fin.cons_succ, consWord, word, Fin.val_succ]
      split_ifs <;> first | rfl | omega

theorem symm_consWord_left {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin (D + 2) => V) ℝ) (hI : IsSymmForm I) (k i : ℕ) (hi : i < k)
    (hD : 2 * k ≤ D + 1) (x₁ x₂ a : V) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  refine (symm_swap_nat I hI (consWord k i x₁ x₁ x₂ a) 0 2 (by omega) (by omega)).trans ?_
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega

theorem symm_consWord_right {V : Type*} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin (D + 2) => V) ℝ) (hI : IsSymmForm I) (k i : ℕ) (hi : i < k)
    (hD : 2 * k ≤ D + 1) (x₁ x₂ a : V) :
    I (fun j => consWord k i x₂ x₁ x₂ a j) = I (fun j => interp k i x₁ x₂ a j) := by
  refine (symm_swap_nat I hI (consWord k i x₂ x₁ x₂ a) 1 (2 * i + 1) (by omega)
    (by omega)).trans ?_
  refine (symm_swap_nat I hI (fun m => consWord k i x₂ x₁ x₂ a
    (if m = 1 then 2 * i + 1 else if m = 2 * i + 1 then 1 else m)) 2 (2 * i + 2) (by omega)
    (by omega)).trans ?_
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega

theorem aPrime_thm : APrimeStatement := by
  intro D S k hk hkD
  have hstep : ∀ i ∈ Finset.range k,
      S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) =
        S.IW (fun j => interp k (i + 1) (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) -
          S.IW (fun j => interp k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← S.diag, cons_cons_word D k i hk, cons_cons_word D k i hk,
      symm_consWord_left S.IW S.symmW k i hi hkD,
      symm_consWord_right S.IW S.symmW k i hi hkD]
  have hsum : ∑ i ∈ Finset.range k, S.Φ (word D k i (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A)) =
      S.IW (fun j => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) -
        S.IW (fun j => interp k 0 (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    rw [Finset.sum_congr rfl hstep]
    exact Finset.sum_range_sub
      (fun m => S.IW (fun j => interp k m (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j)) k
  have hzero : S.IW (fun j => interp k 0 (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) = 0 := by
    have h := S.comp_right_eq_zero_alt
      (fun j : Fin (D + 2) => if (j : ℕ) < 1 + 2 * k then S.ξ else S.A)
    refine Eq.trans ?_ h
    congr 1
    funext j
    simp only [interp]
    split_ifs <;> first | rfl | exact S.base | omega
  have hfun : (Fin.cons (S.p₂ S.ξ) (fun j => S.p₁ (mix (2 * k) S.ξ S.A j)) :
      Fin (D + 2) → S.VW) =
      fun j : Fin (D + 2) => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) (j : ℕ) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [interp]
    · rw [Fin.cons_succ, Fin.val_succ]
      show S.p₁ (if (j : ℕ) < 2 * k then S.ξ else S.A) =
        (if (j : ℕ) + 1 = 0 then S.p₂ S.ξ else if (j : ℕ) + 1 < 1 + 2 * k then S.p₁ S.ξ else
          if (j : ℕ) + 1 < 1 + 2 * k then S.p₂ S.ξ else S.p₁ S.A)
      have h0 : ¬((j : ℕ) + 1 = 0) := by omega
      by_cases h : (j : ℕ) < 2 * k
      · have h1 : (j : ℕ) + 1 < 1 + 2 * k := by omega
        rw [if_pos h, if_neg h0, if_pos h1]
      · have h1 : ¬((j : ℕ) + 1 < 1 + 2 * k) := by omega
        rw [if_neg h, if_neg h0, if_neg h1, if_neg h1]
  have htop : S.I (mix (2 * k) S.ξ S.A) =
      -S.IW (fun j => interp k k (S.p₁ S.ξ) (S.p₂ S.ξ) (S.p₁ S.A) j) := by
    rw [← S.cons_comp_left, show -(S.p₂ S.ξ) = (-1 : ℝ) • S.p₂ S.ξ by simp,
      MultilinearMap.cons_smul, neg_one_smul, hfun]
  rw [hsum, hzero, htop, sub_zero]

end ReciprocityTheory.ChartRestriction.G.AI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AI

open Polynomial

private theorem neg_X_pow_eq_C_neg_one_pow_mul_X_pow (j : ℕ) : ((-X : ℝ[X]) ^ j) = C ((-1 : ℝ) ^ j) * X ^ j := by
  have hX : (-X : ℝ[X]) = C (-1) * X := by
    ext n
    rw [Polynomial.coeff_neg, Polynomial.coeff_C_mul]
    ring
  rw [hX, mul_pow, ← map_pow]

theorem volPoly_coeff (D : ℕ) (J : ℕ → ℝ) (n : ℕ) :
    (volPoly D J).coeff n = (D.choose n : ℝ) * J n * (-1) ^ n := by
  have h : ∀ j, (C ((D.choose j : ℝ) * J j) * (-X) ^ j : ℝ[X]) =
      C ((D.choose j : ℝ) * J j * (-1) ^ j) * X ^ j := by
    intro j
    rw [neg_X_pow_eq_C_neg_one_pow_mul_X_pow, ← mul_assoc, ← map_mul]
  rw [volPoly, Finset.sum_congr rfl fun j _ => h j, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simp at hn; omega)]
    simp

theorem tsgPoly_coeff_zero (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : (tsgPoly D κ P).coeff 0 = 0 := by
  rw [tsgPoly, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun n _ => ?_
  split_ifs <;> simp [Polynomial.coeff_C_mul_X_pow]

theorem tsgPoly_coeff_succ (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (m : ℕ) :
    (tsgPoly D κ P).coeff (m + 1) =
      if Odd m then ((D : ℝ) + 1) * κ ((m + 1) / 2) / (((m + 1) / 2 : ℕ) : ℝ) * P.coeff m else 0 := by
  rw [tsgPoly, Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
  · by_cases ho : Odd m
    · rw [if_pos ho, if_pos ho, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · rw [if_neg ho, if_neg ho, Polynomial.coeff_zero]
  · intro n _ hnm
    by_cases ho : Odd n
    · rw [if_pos ho, Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
    · rw [if_neg ho, Polynomial.coeff_zero]
  · intro hm
    have h0 : P.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hm; omega)
    by_cases ho : Odd m
    · rw [if_pos ho, Polynomial.coeff_C_mul_X_pow, if_pos rfl, h0, mul_zero]
    · rw [if_neg ho, Polynomial.coeff_zero]

noncomputable def FibreSquare.evenPoly {D : ℕ} (S : FibreSquare D) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1 + 1),
    C (((D + 1).choose j : ℝ) * ((-1) ^ j + 1) * S.I (mix j S.ξ S.A)) * X ^ j

theorem tsgPoly_volPoly_coeff_even (D : ℕ) (J κ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (tsgPoly D κ (volPoly D J)).coeff (2 * k) =
      -(2 * ((D + 1).choose (2 * k) : ℝ) * (κ k * J (2 * k - 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
  have h3 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  have hodd : Odd (2 * j + 1) := ⟨j, rfl⟩
  rw [h2, tsgPoly_coeff_succ, if_pos hodd, volPoly_coeff, h3, Nat.add_sub_cancel,
    Odd.neg_one_pow hodd]
  have hc : (D + 1) * D.choose (2 * j + 1) = (D + 1).choose (2 * j + 1 + 1) * (2 * j + 1 + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq D (2 * j + 1)
    | exact Nat.succ_mul_choose_eq D (2 * j + 1)
  have hc' : ((D : ℝ) + 1) * (D.choose (2 * j + 1) : ℝ) =
      ((D + 1).choose (2 * j + 1 + 1) : ℝ) * (2 * j + 1 + 1) := by exact_mod_cast hc
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hj ⊢
  field_simp
  first
  | linear_combination (κ (j + 1) * J (2 * j + 1)) * hc'
  | linear_combination (-(κ (j + 1) * J (2 * j + 1))) * hc'
  | linear_combination (2 * κ (j + 1) * J (2 * j + 1)) * hc'
  | linear_combination (-(2 * κ (j + 1) * J (2 * j + 1))) * hc'

theorem tsgPoly_coeff_odd (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) (k : ℕ) :
    (tsgPoly D κ P).coeff (2 * k + 1) = 0 := by
  rw [tsgPoly_coeff_succ, if_neg (Nat.not_odd_iff_even.2 (even_two_mul k))]

end ReciprocityTheory.ChartRestriction.G.AI
end
