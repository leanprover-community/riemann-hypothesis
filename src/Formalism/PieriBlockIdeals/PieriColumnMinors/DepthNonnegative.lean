import Formalism.PieriBlockIdeals.BlockIdealBound5Derived
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
import Formalism.PieriBlockIdeals.FactorialValuationSum
import Formalism.PieriBlockIdeals.PieriColumnMinors.LabelSumNeedsLeFalse
import Formalism.PieriBlockIdeals.PieriColumnMinors.LastGradedImpliesOneBlock
import Mathlib
import Formalism.PieriBlockIdeals.Statement
import Formalism.PieriBlockIdeals.JointCW5
import Formalism.RankGapBounds.RankGapProofs.FormsTensorLocalization
import Formalism.PieriBlockIdeals.PieriColumnMinors.RegularCuspidalTrace

section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.UnitNormBounds

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

theorem rowStart_rev_eq (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (hb : ∀ a, w ≤ lam a ∧ lam a ≤ M)
    (b : Fin (k + j)) :
    U k j t lam (Fin.rev b) = (M : ℤ) - (dual M lam b : ℤ) + (t : ℤ) + (b.val : ℤ) := by
  have h1 := Fin.val_rev b
  have h2 := hb (Fin.rev b)
  have h3 := b.isLt
  unfold U dual
  omega

theorem content_label_eq (t w M : ℕ) (hwM : w ≤ M) (ct : ℤ) : cont t w M ct = (M : ℤ) - ct + (t : ℤ) - 1 := by
  unfold cont maxB
  omega

theorem good_labels_holds : GoodLabels := by
  intro k j t w M i lam hb tau htau b col h1 h2
  have hU := rowStart_rev_eq k j t w M lam hb b
  have hw := hb (Fin.rev b)
  have hd : dual M lam b = M - lam (Fin.rev b) := rfl
  obtain ⟨_, _, _, _, hbox⟩ := Finset.mem_filter.mp htau
  constructor
  · by_contra hcon
    unfold boxesOfContent at hbox
    rw [Finset.card_eq_zero] at hbox
    have hmem : b ∈ Finset.univ.filter fun a : Fin (k + j) =>
        (dual M lam a : ℤ) ≤ ((M - w : ℕ) : ℤ) + (a.val : ℤ) ∧
          ((M - w : ℕ) : ℤ) + (a.val : ℤ) < (tau a : ℤ) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · omega
      · unfold label maxB at hcon
        omega
    rw [hbox] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · unfold label
    omega

theorem card_filter_rev_lt_le (k j : ℕ) (p : Fin (k + j) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b).card ≤ k := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b)
    (t := Finset.range k) (fun b => (Fin.rev b).val)
    (by
      intro b hb
      have := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr this))
    (by
      intro a _ b _ hab
      exact Fin.rev_injective (Fin.ext hab))
  simpa using h

theorem card_filter_not_rev_lt_le (k j : ℕ) (p : Fin (k + j) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin (k + j) => ¬ (Fin.rev b).val < k ∧ p b).card ≤ j := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : Fin (k + j) => ¬ (Fin.rev b).val < k ∧ p b)
    (t := Finset.range j) (fun b => b.val)
    (by
      intro b hb
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
      have h2 := Fin.val_rev b
      have h3 := b.isLt
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by show b.val < j; omega)))
    (by
      intro a _ b _ hab
      exact Fin.ext hab)
  simpa using h

theorem counts_rows_holds : CountsRows := by
  intro k j t w M i lam xm xp hR tau _ ct
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  unfold boxesOfLabel boxesOfContent cloudBoxes
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun a : Fin (k + j) =>
      (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ))
      (fun b : Fin (k + j) => (Fin.rev b).val < k), add_comm]
  rw [Finset.filter_filter, Finset.filter_filter]
  refine Nat.add_le_add ?_ (le_of_eq ?_)
  · split_ifs with hct
    · refine le_trans (le_of_eq ?_) (card_filter_not_rev_lt_le k j (fun a : Fin (k + j) =>
        (dual M lam a : ℤ) ≤ cont t w M ct + (a.val : ℤ) ∧ cont t w M ct + (a.val : ℤ) < (tau a : ℤ)))
      congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro b _ ⟨⟨h1, _⟩, h3⟩
      have hU := rowStart_rev_eq k j t w M lam hb b
      have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
      have hr := hR.rest (Fin.rev b) (by omega)
      omega
  · congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

theorem counts_cloud_holds : CountsCloud := by
  intro k j t w M i lam tau htau ct
  constructor
  · exact card_filter_rev_lt_le k j _
  · refine le_trans ?_ (ld_boxes_le t (M - w) i (k + j) (dual M lam) tau htau (cont t w M ct))
    unfold cloudBoxes boxesOfContent
    refine Finset.card_le_card ?_
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩

theorem counts_deep_holds : CountsDeep := by
  intro k j t w M i lam xm xp hR tau htau ct hct
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  obtain ⟨hpi, _, hsum, _, _⟩ := Finset.mem_filter.mp htau
  have hle : ∀ b, dual M lam b ≤ tau b := fun b => (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hpi) b)).1
  have htot : ∑ b : Fin (k + j), ((tau b : ℤ) - (dual M lam b : ℤ)) = (i : ℤ) := by
    rw [Finset.sum_sub_distrib]
    have : ((∑ a, tau a : ℕ) : ℤ) = ((∑ a, dual M lam a + i : ℕ) : ℤ) := by rw [hsum]
    push_cast at this
    linarith
  unfold cloudBoxes
  rw [← htot, ← nsmul_eq_mul, ← Finset.sum_const]
  refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
  · intro b hbm
    obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.mp hbm
    have hU := rowStart_rev_eq k j t w M lam hb b
    have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
    have hr := (hR.cloud (Fin.rev b) h1).1
    omega
  · intro b _ _
    have := hle b
    omega

theorem boxesOfLabel_le_bound (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (tau : Fin (k + j) → ℕ) (htau : tau ∈ shapes t (M - w) i (dual M lam)) (ct : ℤ) :
    (boxesOfLabel t w M lam tau ct : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ)) := by
  have h1 := counts_rows_holds k j t w M i lam xm xp hR tau htau ct
  have h2 := counts_cloud_holds k j t w M i lam tau htau ct
  have hk : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ k := by exact_mod_cast h2.1
  have ht : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ t := by exact_mod_cast h2.2
  by_cases hct : ct < xm
  · rw [if_pos hct] at h1
    rw [if_pos hct, if_pos hct]
    have h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (j : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ) := by
      exact_mod_cast h1
    have h3 := counts_deep_holds k j t w M i lam xm xp hR tau htau ct hct
    have h3' : (cloudBoxes k j t w M lam tau ct : ℝ) * ((xm - ct : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast h3
    have hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)
    have h4 : (cloudBoxes k j t w M lam tau ct : ℝ) ≤ (i : ℝ) / ((xm - ct : ℤ) : ℝ) := (le_div_iff₀ hpos).mpr h3'
    have h5 := le_min (le_min hk ht) h4
    linarith
  · rw [if_neg hct] at h1
    rw [if_neg hct, if_neg hct]
    have h1' : (boxesOfLabel t w M lam tau ct : ℝ) ≤ (0 : ℝ) + (cloudBoxes k j t w M lam tau ct : ℝ) := by
      exact_mod_cast h1
    have h5 := le_min (le_min hk ht) hk
    linarith

theorem multiplicity_bound_holds : MuBound := by
  intro k j t w M i lam xm xp hR ct
  unfold mu
  by_cases hne : (shapes t (M - w) i (dual M lam)).Nonempty
  · obtain ⟨tau, htau, heq⟩ := Finset.exists_mem_eq_sup _ hne
      (fun tau => boxesOfContent (dual M lam) tau (cont t w M ct))
    rw [heq]
    exact boxesOfLabel_le_bound k j t w M i lam xm xp hR tau htau ct
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty]
    have h0 : (((⊥ : ℕ) : ℕ) : ℝ) = 0 := by simp
    rw [h0]
    refine add_nonneg (by split_ifs <;> positivity) (le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_)
    split_ifs with hct
    · exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (by omega : (0 : ℤ) ≤ xm - ct))
    · exact Nat.cast_nonneg _

theorem mem_label_interval_of_mu_ne_zero (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (ct : ℤ) (hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0) : maxB t w < ct ∧ ct < xp := by
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  unfold mu at hmu
  obtain ⟨tau, htau, hbx⟩ := (Finset.lt_sup_iff).mp (Nat.pos_of_ne_zero hmu)
  unfold boxesOfContent at hbx
  obtain ⟨b, hbm⟩ := Finset.card_pos.mp hbx
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hbm).2
  have hU := rowStart_rev_eq k j t w M lam hb b
  have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
  obtain ⟨col, hcol⟩ : ∃ col : ℕ, (col : ℤ) = cont t w M ct + (b.val : ℤ) :=
    ⟨(cont t w M ct + (b.val : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hg := (good_labels_holds k j t w M i lam hb tau htau b col (by omega) (by omega)).1
  unfold label at hg
  constructor
  · omega
  · by_cases hk : (Fin.rev b).val < k
    · have := (hR.cloud (Fin.rev b) hk).2
      omega
    · have := hR.rest (Fin.rev b) (by omega)
      have := hR.le
      omega

theorem padicValInt_prod_eq_sum (l : ℕ) [Fact l.Prime] (s : Finset ℕ) (g : ℕ → ℤ) (hg : ∀ x ∈ s, g x ≠ 0) :
    padicValInt l (∏ x ∈ s, g x) = ∑ x ∈ s, padicValInt l (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValInt.mul (hg a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun x hx => hg x (Finset.mem_insert_of_mem hx)),
      ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]

theorem padicValInt_pow_eq_mul (l : ℕ) [Fact l.Prime] (x : ℤ) (_hx : x ≠ 0) (m : ℕ) :
    padicValInt l (x ^ m) = m * padicValInt l x := by
  unfold padicValInt
  rw [Int.natAbs_pow, padicValNat.pow]

theorem depth_valuation_sum_holds : DnValSum := by
  intro l k j t w M i lam xm xp hl hR
  have : Fact l.Prime := ⟨hl⟩
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  have hdw : ∀ b, dual M lam b ≤ M - w := fun b => by
    have := hb (Fin.rev b)
    unfold dual
    omega
  have hcont : ∀ c : ℤ, cont t w M (maxB t w + (((M - w : ℕ) : ℤ) - c)) = c := by
    intro c
    unfold cont
    ring
  unfold Dn
  have hne : ∀ x ∈ Finset.range (k + j + (M - w) + i),
      (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^
        mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0 := by
    intro x _
    by_cases h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0
    · have hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ) := by omega
      rw [hc, ld_mu_w]
      simp
    · exact pow_ne_zero _ h
  have hterm : ∀ x ∈ Finset.range (k + j + (M - w) + i),
      padicValInt l ((((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^
        mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ))) =
      mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) *
        vl l (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) := by
    intro x _
    by_cases h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0
    · have hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ) := by omega
      rw [hc, ld_mu_w]
      simp
    · unfold vl
      exact padicValInt_pow_eq_mul l _ h _
  rw [padicValInt_prod_eq_sum l _ _ hne, Finset.sum_congr rfl hterm]
  refine Finset.sum_bij_ne_zero
    (fun x _ _ => maxB t w + (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ)))) ?_ ?_ ?_ ?_
  · intro a _ h2
    have hmu : mu t (M - w) i (dual M lam) ((a : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0 := left_ne_zero_of_mul h2
    rw [← hcont ((a : ℤ) - ((k + j : ℕ) : ℤ))] at hmu
    exact Finset.mem_Ioo.mpr (mem_label_interval_of_mu_ne_zero k j t w M i lam xm xp hR _ hmu)
  · intro a1 _ _ a2 _ _ h
    omega
  · intro ct _ h2
    have hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0 := left_ne_zero_of_mul h2
    obtain ⟨h3, h4⟩ := muSupport t (M - w) i (k + j) (dual M lam) _ hdw hmu
    have ha : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) = cont t w M ct + ((k + j : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    have hx : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) - ((k + j : ℕ) : ℤ) = cont t w M ct := by
      rw [ha]; ring
    have hv : ((M - w : ℕ) : ℤ) - cont t w M ct = ct - maxB t w := by
      unfold cont; ring
    refine ⟨(cont t w M ct + ((k + j : ℕ) : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · rw [hx, hv]
      exact h2
    · rw [hx, hv]
      ring
  · intro a _ _
    rw [hcont]
    congr 2
    ring

theorem sum_padicVal_shift_eq_factorial (l : ℕ) [Fact l.Prime] (mB : ℤ) (n : ℕ) :
    ∑ ct ∈ Finset.Ioo mB (mB + 1 + (n : ℤ)), vl l (ct - mB) = padicValNat l n.factorial := by
  induction n with
  | zero =>
    have : Finset.Ioo mB (mB + 1 + ((0 : ℕ) : ℤ)) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [this]
    simp
  | succ n ih =>
    have hins : Finset.Ioo mB (mB + 1 + ((n + 1 : ℕ) : ℤ)) =
        insert (mB + 1 + (n : ℤ)) (Finset.Ioo mB (mB + 1 + (n : ℤ))) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hnot : (mB + 1 + (n : ℤ)) ∉ Finset.Ioo mB (mB + 1 + (n : ℤ)) := by
      simp
    rw [hins, Finset.sum_insert hnot, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
    congr 1
    unfold vl
    have : mB + 1 + (n : ℤ) - mB = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, padicValInt.of_nat]

theorem first_bound_holds : FactorialValuationSum := by
  intro l xm mB hl hlt
  have : Fact l.Prime := ⟨hl⟩
  have hn : (((xm - mB - 1).toNat : ℕ) : ℤ) = xm - mB - 1 := Int.toNat_of_nonneg (by omega)
  constructor
  · have h := sum_padicVal_shift_eq_factorial l mB (xm - mB - 1).toNat
    rw [hn] at h
    have he : mB + 1 + (xm - mB - 1) = xm := by ring
    rw [he] at h
    exact h
  · have h3 := sub_one_mul_padicValNat_factorial (p := l) (xm - mB - 1).toNat
    have h4 : (l - 1) * padicValNat l ((xm - mB - 1).toNat).factorial ≤ (xm - mB - 1).toNat := by
      rw [h3]; exact Nat.sub_le _ _
    have hl2 := hl.two_le
    have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
      linarith
    rw [le_div_iff₀ hl1]
    have h5 : (((l - 1 : ℕ) : ℝ)) * (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤
        (((xm - mB - 1).toNat : ℕ) : ℝ) := by exact_mod_cast h4
    have h6 : (((l - 1 : ℕ) : ℝ)) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h7 : (((xm - mB - 1).toNat : ℕ) : ℝ) = ((xm - mB : ℤ) : ℝ) - 1 := by
      have : ((((xm - mB - 1).toNat : ℕ) : ℤ) : ℝ) = ((xm - mB - 1 : ℤ) : ℝ) := by rw [hn]
      push_cast at this ⊢
      linarith
    rw [h6, h7] at h5
    linarith

theorem harmonic_positive_log_holds : HarmPosLog := by
  intro l h i hi
  have hil : 0 ≤ i / (l : ℝ) := div_nonneg hi (Nat.cast_nonneg _)
  constructor
  · unfold harm
    split_ifs with hlh
    · exact mul_nonneg hil (add_nonneg zero_le_one Real.posLog_nonneg)
    · refine mul_le_mul_of_nonneg_left ?_ hil
      have : Real.log ((h : ℝ) / (l : ℝ)) ≤ Real.posLog ((h : ℝ) / (l : ℝ)) := le_max_right _ _
      linarith
  · intro h1 h2
    unfold harm
    rw [if_neg (by omega)]
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast h1
    have hx : (1 : ℝ) ≤ (h : ℝ) / (l : ℝ) := by
      rw [le_div_iff₀ hl0, one_mul]
      exact_mod_cast h2
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hx)]

theorem labelLHS_shift_to_zero (l k t : ℕ) (i : ℝ) (xm xp mB : ℤ) :
    labelLHS l k t i xm xp mB = labelLHS l k t i (xm - mB) (xp - mB) 0 := by
  unfold labelLHS
  congr 1
  · refine Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_
    · intro ct h
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · intro ct h
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · intro ct _
      ring
    · intro ct _
      ring
    · intro ct _
      rw [sub_zero]
  · refine Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_
    · intro ct h
      simp only [Finset.mem_Ioo] at h ⊢
      omega
    · intro ct h
      simp only [Finset.mem_Ioo] at h ⊢
      omega
    · intro ct _
      ring
    · intro ct _
      ring
    · intro ct _
      have e1 : xm - mB - (ct - mB) = xm - ct := by ring
      rw [e1, sub_zero]

theorem indexIntegral_shift (l : ℕ) (xm xp mB : ℤ) : IlInd l (xm - mB) (xp - mB) 0 = IlInd l xm xp mB := by
  unfold IlInd
  have h : (∃ y : ℤ, xm - mB ≤ y ∧ y ≤ xp - mB ∧ (l : ℤ) ∣ y - 0) ↔
      (∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB) := by
    constructor
    · rintro ⟨y, h1, h2, h3⟩
      exact ⟨y + mB, by omega, by omega, by simpa using h3⟩
    · rintro ⟨y, h1, h2, h3⟩
      exact ⟨y - mB, by omega, by omega, by simpa using h3⟩
  by_cases hc : ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB
  · rw [if_pos hc, if_pos (h.mpr hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (h.mp h'))]

theorem indexIntegral_nonneg (l : ℕ) (xm xp mB : ℤ) : 0 ≤ IlInd l xm xp mB := by
  unfold IlInd
  split_ifs <;> norm_num

theorem gated_min_nonneg (l k t : ℕ) (i : ℝ) (hi : 0 ≤ i) (D : ℤ) :
    0 ≤ (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (i / (d0 l D : ℝ)) else 0) := by
  split_ifs
  · exact le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg hi (Nat.cast_nonneg _))
  · exact le_rfl

theorem label_sum_plus_holds : LabelSumPlus := by
  intro l k t h i xm xp mB hl hi hmx hxx hxp hh
  by_cases hlh : h < l
  · have hlhZ : (h : ℤ) < (l : ℤ) := by exact_mod_cast hlh
    have hz : ∀ ct : ℤ, mB < ct → ct ≤ xp → (vl l (ct - mB) : ℝ) = 0 := by
      intro ct h1 h2
      rw [label_vl_zero_small (by omega) (by omega)]
      simp
    have hL : labelLHS l k t i xm xp mB = 0 := by
      unfold labelLHS
      rw [Finset.sum_eq_zero (fun ct hct => by
            rw [hz ct (by have := Finset.mem_Icc.mp hct; omega) (Finset.mem_Icc.mp hct).2, mul_zero]),
          Finset.sum_eq_zero (fun ct hct => by
            rw [hz ct (Finset.mem_Ioo.mp hct).1 (by have := Finset.mem_Ioo.mp hct; omega), mul_zero]),
          add_zero]
    rw [hL]
    unfold labelSumBoundPos harm
    rw [if_pos hlh, add_zero]
    refine add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg ?_ (Nat.cast_nonneg _))
      (indexIntegral_nonneg _ _ _ _))) (gated_min_nonneg l k t i hi _)
    exact_mod_cast (by omega : (0 : ℤ) ≤ xp - xm)
  · have h1 := labelSumLe_holds l k t h i (xm - mB) (xp - mB) 0 hl hi le_rfl (by omega) (by omega) (by omega) hh
      (by omega)
    rw [← labelLHS_shift_to_zero] at h1
    unfold labelSumBound at h1
    unfold labelSumBoundPos harm
    rw [if_neg hlh]
    have e : xp - mB - (xm - mB) = xp - xm := by ring
    rw [indexIntegral_shift, e] at h1
    simp only [sub_zero] at h1
    exact h1

theorem harmonic_monotone (l h : ℕ) : Monotone (harm l h) := by
  intro a b hab
  unfold harm
  split_ifs with hlh
  · exact le_rfl
  · have hlog : 0 ≤ Real.log ((h : ℝ) / (l : ℝ)) := by
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · rw [h0]; simp
      · have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast h0
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ hl0, one_mul]
        exact_mod_cast (by omega : l ≤ h)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _)) (by linarith)

theorem gated_min_monotone (l k t : ℕ) (D : ℤ) {a b : ℝ} (hab : a ≤ b) :
    (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (a / (d0 l D : ℝ)) else 0) ≤
      (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (b / (d0 l D : ℝ)) else 0) := by
  split_ifs
  · exact min_le_min_left _ (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))
  · exact le_rfl

theorem labelRHSPlus_monotone (l k t h : ℕ) (xm xp mB : ℤ) {a b : ℝ} (hab : a ≤ b) :
    labelSumBoundPos l k t h a xm xp mB ≤ labelSumBoundPos l k t h b xm xp mB := by
  unfold labelSumBoundPos
  have h1 := gated_min_monotone l k t (xm - mB) hab
  have h2 := harmonic_monotone l h hab
  linarith

theorem second_valuation_holds : Step2Val := by
  intro l k j t w M h i lam xm xp hl hR hxp hh
  have hsum := depth_valuation_sum_holds l k j t w M i lam xm xp hl hR
  have hA1 := first_bound_holds l xm (maxB t w) hl hR.above
  have hLS := label_sum_plus_holds l k t h (i : ℝ) xm xp (maxB t w) hl (Nat.cast_nonneg _) hR.above hR.le hxp hh
  rw [hsum, Nat.cast_sum]
  simp only [Nat.cast_mul]
  have hdisj : Disjoint (Finset.Ioo (maxB t w) xm) (Finset.Ico xm xp) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have := (Finset.mem_Ioo.mp h1).2
    have := (Finset.mem_Ico.mp h2).1
    omega
  have hun : Finset.Ioo (maxB t w) xp = Finset.Ioo (maxB t w) xm ∪ Finset.Ico xm xp := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_Ico]
    have := hR.above
    have := hR.le
    omega
  rw [hun, Finset.sum_union hdisj]
  have h1 : ∑ ct ∈ Finset.Ioo (maxB t w) xm,
        (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤
      (j : ℝ) * ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) +
        ∑ ct ∈ Finset.Ioo (maxB t w) xm,
          min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - maxB t w) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro ct hct
    have hlt := (Finset.mem_Ioo.mp hct).2
    have hm := multiplicity_bound_holds k j t w M i lam xm xp hR ct
    rw [if_pos hlt, if_pos hlt] at hm
    calc (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ)
        ≤ ((j : ℝ) + min (min (k : ℝ) (t : ℝ)) ((i : ℝ) / ((xm - ct : ℤ) : ℝ))) * (vl l (ct - maxB t w) : ℝ) :=
          mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _)
      _ = _ := by ring
  have h2 : ∑ ct ∈ Finset.Ico xm xp,
        (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) * (vl l (ct - maxB t w) : ℝ) ≤
      ∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - maxB t w) : ℝ) := by
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self ?_)
    · intro ct hct
      have hge := (Finset.mem_Ico.mp hct).1
      have hm := multiplicity_bound_holds k j t w M i lam xm xp hR ct
      rw [if_neg (by omega), if_neg (by omega), zero_add] at hm
      exact mul_le_mul_of_nonneg_right (le_trans hm (min_le_right _ _)) (Nat.cast_nonneg _)
    · intro ct _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA : ∑ ct ∈ Finset.Ioo (maxB t w) xm, (vl l (ct - maxB t w) : ℝ) ≤
      (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) := by
    have h3 := hA1.2
    rw [← hA1.1, Nat.cast_sum] at h3
    exact h3
  have hA' := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  unfold labelLHS at hLS
  linarith

theorem second_valuation_up_to_holds : Step2ValUpTo := by
  intro l k j t w M h i I lam xm xp hl hR hxp hh hiI
  have h1 := second_valuation_holds l k j t w M h i lam xm xp hl hR hxp hh
  have h2 := labelRHSPlus_monotone l k t h xm xp (maxB t w) hiI
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
    linarith
  have hD : ((xm - maxB t w : ℤ) : ℝ) ≤ (h : ℝ) := by
    have := hR.le
    exact_mod_cast (by omega : xm - maxB t w ≤ (h : ℤ))
  have h3 : (((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by linarith) hl1
  have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  linarith

theorem c_prime_le_coarse_holds : CPrimeLeCoarse := by
  intro l k j t q h N' ecl xm xp mB I hl hI
  unfold cPrime cCoarse labelSumBoundPos
  have h1 := (harmonic_positive_log_holds l h I hI).1
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have h2 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6 := by
    have h3 : ((h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg _; linarith) hl1
    linarith
  have h4 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ (q : ℝ) + 2 * (j : ℝ))
  linarith

theorem labelRHSPlus_shift_invariant (l k t h : ℕ) (I : ℝ) (xm xp mB c : ℤ) :
    labelSumBoundPos l k t h I (xm + c) (xp + c) (mB + c) = labelSumBoundPos l k t h I xm xp mB := by
  unfold labelSumBoundPos
  have e1 : xp + c - (xm + c) = xp - xm := by ring
  have e2 : xm + c - (mB + c) = xm - mB := by ring
  have e3 : xp + c - (mB + c) = xp - mB := by ring
  have e4 : IlInd l (xm + c) (xp + c) (mB + c) = IlInd l xm xp mB := by
    rw [← indexIntegral_shift l (xm + c) (xp + c) (mB + c), e2, e3, indexIntegral_shift]
  rw [e1, e2, e4]

end Formalism.CohomologicalDescent.UnitNormBounds
end
end

section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Formalism.RankGapBounds.ChebyshevFactorialBounds

lemma jw_Il_eq {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) = D.Icl τ l := by
  unfold IlInd Data.Icl
  by_cases h : ∃ y : ℤ, D.xlo τ ≤ y ∧ y ≤ D.xhi τ ∧ (l : ℤ) ∣ y - D.maxB τ
  · rw [if_pos h]
  · rw [if_neg h]

lemma jw_Icl_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : 0 ≤ D.Icl τ l := by
  rw [← jw_Il_eq]
  unfold IlInd
  split_ifs <;> norm_num

lemma jw_gate_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    (0 : ℝ) ≤ (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := by
  split_ifs
  · exact le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact le_rfl

end Formalism.CohomologicalDescent
end
end

section
noncomputable section

open TensorProduct MvPolynomial

namespace Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

theorem isUnit_intCast_of_not_dvd' (R : Type) [CommRing R] (l : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : R) := by
  have h1 : ¬ l ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
  have h2 := hu _ h1
  rcases Int.natAbs_eq m with h | h
  · have e : (m : R) = ((m.natAbs : ℕ) : R) := by
      conv_lhs => rw [h]
      simp
    rw [e]
    exact h2
  · have e : (m : R) = -((m.natAbs : ℕ) : R) := by
      conv_lhs => rw [h]
      simp
    rw [e]
    exact h2.neg

theorem pow_smul_weighted_component_mem_weyl (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ)
    (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) (hE : ExpLe l r ν μ e)
    (x : MvPolynomial (Fin r × Fin r) R) (hx : x ∈ dualWeyl R r r ν) :
    (l : R) ^ e • weightedHomogeneousComponent (rowW r r) μ x ∈ weyl R r r le_rfl ν := by
  classical
  rw [standardMonomialSpanDomain R r r ν] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    have hhom := ldbasis_bidet_rowHom R sz hsz I
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hhom)]
    split_ifs with hw
    · have h1 : bideterminant ℤ sz hsz I ∈ nablaWt r ν μ := by
        refine Submodule.mem_inf.2 ⟨hshape ▸ bidetMem ℤ r r K sz hsz I, ?_⟩
        rw [hw]
        exact (mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_bidet_rowHom ℤ sz hsz I)
      obtain ⟨m, hm, h2⟩ := hE _ h1
      have h3 := LA.la_map_weyl R le_rfl ν _ h2
      rw [LA.la_map_smul, ldlat_map_bidet] at h3
      obtain ⟨u, hu'⟩ := isUnit_intCast_of_not_dvd' R l hu m hm
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : R) h3
      rw [smul_smul] at h4
      convert h4 using 2
      push_cast
      rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [smul_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ _ hx





theorem application_window : ApplicationWindow := by
  intro hD l k j t q h lam xm xp hl ht hanti hconst hspread hh hcloud hlows habove hle htop ecl hecl I μ hμ
  refine expLeMono l _ _ μ _ _ ?_
    (applicationSteps hD l k j t q h lam hl ht hanti hconst hspread ecl hecl I μ hμ)
  refine Nat.le_floor ?_
  have hb : ∀ a : Fin (k + j), lam (k + j) ≤ res (k + j) lam a ∧ res (k + j) lam a ≤ lam 0 := fun a =>
    ⟨hanti a.val (k + j) (by have := a.isLt; omega) (by omega),
      hanti 0 a.val (Nat.zero_le _) (by have := a.isLt; omega)⟩
  have eU : ∀ a : Fin (k + j),
      UN (k + j + t + q) lam a.val = U k j t (res (k + j) lam) a + (q : ℤ) := by
    intro a
    unfold UN U res
    push_cast
    ring
  have e3 : UN (k + j + t + q) lam (k + j) = maxB t (lam (k + j)) + (q : ℤ) := by
    unfold UN maxB
    push_cast
    ring
  have hR : Rows k j t (lam (k + j)) (lam 0) (res (k + j) lam) (xm - q) (xp - q) := by
    refine ⟨fun a => (hb a).1, fun a => (hb a).2, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h1 := hcloud a.val ha
      rw [eU a] at h1
      constructor <;> omega
    · intro a ha
      have h1 := hlows a.val ha a.isLt
      rw [eU a] at h1
      omega
    · rw [e3] at habove
      omega
    · omega
  have hxp : (xp - q) - maxB t (lam (k + j)) ≤ (h : ℤ) := by
    rw [e3] at htop
    omega
  have hh1 : 1 ≤ h := by omega
  have hcost : (blockCost l (k + j) t I lam : ℝ) ≤ (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) +
      labelSumBoundPos l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) := by
    unfold blockCost
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (I + 1)) ⟨0, by simp⟩
      (fun i => padicValInt l (Dn t (lam 0 - lam (k + j)) i fun b : Fin (k + j) =>
        lam 0 - res (k + j) lam (Fin.rev b)))
    rw [heq]
    exact second_valuation_up_to_holds l k j t (lam (k + j)) (lam 0) h i (I : ℝ) (res (k + j) lam) _ _ hl hR hxp hh
      (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hP : (((h - 1) / (l - 1) : ℕ) : ℝ) ≤ ((h : ℝ) - 1) / ((l : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (α := ℝ) (m := h - 1) (n := l - 1)
    have hl2 := hl.two_le
    rw [Nat.cast_sub hh1, Nat.cast_sub (by omega : 1 ≤ l)] at h1
    simpa using h1
  have hs := labelRHSPlus_shift_invariant l k t h (I : ℝ) (xm - q) (xp - q) (maxB t (lam (k + j))) q
  rw [sub_add_cancel, sub_add_cancel] at hs
  unfold cPrime
  rw [e3, hs]
  have hq := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))
  have hj := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
  push_cast
  linarith

section SizeData₂

open Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem c_prime_le_weight_correction_holds : CPrimeLeCW5 := by
  intro ι D τ l hl hτ hP
  obtain ⟨hh1, _, _, hD0, _, _, _, _, _, hT⟩ := hP
  obtain ⟨hmB, hlo, hxx, hS, hxh, _⟩ := hT τ hτ
  have hl0R : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hl1R : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hk : (0 : ℝ) ≤ D.k := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ (D.depth τ l : ℝ) := Nat.cast_nonneg _
  have hil : (0 : ℝ) ≤ (D.depth τ l : ℝ) / (l : ℝ) := div_nonneg hi hl0R.le
  have hpeel : ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) - 1) / ((l : ℝ) - 1)) ≤
      ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ((D.h : ℝ) - 1) / ((l : ℝ) - 1) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right _ hl1R.le
      have : (0 : ℝ) ≤ (D.Nr : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hA : (D.k : ℝ) * (((D.xhi τ - D.xlo τ : ℤ) : ℝ) / (l : ℝ) + D.Icl τ l) ≤
      (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l) := by
    apply mul_le_mul_of_nonneg_left _ hk
    have h1 : ((D.xhi τ - D.xlo τ : ℤ) : ℝ) ≤ (D.S : ℝ) := by exact_mod_cast hS
    have := div_le_div_of_nonneg_right h1 hl0R.le
    linarith
  have hH : harm l D.h (D.depth τ l : ℝ) ≤
      ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ))) := by
    unfold harm
    split_ifs
    · exact mul_nonneg hil (le_max_left _ _)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hil
  have hG : (if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then
      min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0) =
      (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
      min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := rfl
  unfold cPrime labelSumBoundPos Cor.coefficientBoundTau
  rw [jw_Il_eq, hG]
  linarith


theorem coefficientBoundTau_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) (hl : l.Prime) : 0 ≤ Cor.coefficientBoundTau D τ l := by
  have hl0R : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hl1R : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have h1 : (0 : ℝ) ≤ ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    have : (0 : ℝ) ≤ ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1) := div_nonneg (by positivity) hl1R.le
    positivity
  have h2 : (0 : ℝ) ≤ (D.ecl τ l : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (jw_Icl_nonneg D τ l))
  have h4 := jw_gate_nonneg D τ l
  have h5 : (0 : ℝ) ≤ ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ))) :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hl0R.le) (le_max_left _ _)
  unfold Cor.coefficientBoundTau
  linarith

theorem tau_term_le_correction_bound {ι : Type} [DecidableEq ι] (D : Data ι) (hP : D.Params) (l : ℕ) (hl : l.Prime) (τ : ι) :
    ((cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ) ≤
      (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ)) := by
  unfold cTau
  split_ifs with hτ
  · rw [Nat.cast_min]
    apply min_le_min le_rfl
    by_cases h0 : 0 ≤ cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
        (D.depth τ l : ℝ)
    · exact (Nat.floor_le h0).trans (c_prime_le_weight_correction_holds ι D τ l hl hτ hP)
    · show ((⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊ : ℕ) : ℝ) ≤ _
      rw [Nat.floor_of_nonpos (not_le.1 h0).le]
      simpa using coefficientBoundTau_nonneg D τ l hl
  · exact le_rfl


end SizeData₂

section Subquotients

open CategoryTheory CategoryTheory.Limits

theorem subquotient_iso_holds : SubquotIso := by
  intro A _ V G G' _ _ _ _ _ _ ⟨e⟩ ⟨E, ψ, hψ⟩
  exact ⟨E, e.toLinearMap ∘ₗ ψ, e.surjective.comp hψ⟩


def mulOntoScaledSubmodule {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : V →ₗ[A] scaleSub A V c where
  toFun v := ⟨c • v, v, rfl⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' b x := Subtype.ext (smul_comm c b x)


theorem simple_subquotient_of_power_holds : SimpleSubquotOfPower := by
  intro O _ A _ _ V _ _ _ _ ϖ n F F' hFF hn hsimple
  classical
  have hcov : F ⋖ F' := (covBy_iff_quot_is_simple hFF).mpr hsimple
  set Fa : ℕ → Submodule A V := fun a => F ⊔ (F' ⊓ scaleSub A V (ϖ ^ a)) with hFa
  have hle : ∀ a, F ≤ Fa a := fun a => le_sup_left
  have hle' : ∀ a, Fa a ≤ F' := fun a => sup_le hFF inf_le_left
  have h0 : Fa 0 = F' := by
    apply le_antisymm (hle' 0)
    intro x hx
    exact Submodule.mem_sup_right ⟨hx, x, by simp⟩
  have hnF : Fa n = F := le_antisymm (sup_le le_rfl (inf_le_right.trans hn)) (hle n)
  have hex : ∃ a, Fa a = F := ⟨n, hnF⟩
  have ha1 := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h, h0] at ha1
    exact hcov.ne ha1.symm
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have haF' : Fa a = F' := by
    rcases hcov.eq_or_eq (hle a) (hle' a) with h | h
    · exact absurd h (Nat.find_min hex (by omega))
    · exact h
  have haF : Fa (a + 1) = F := by rw [← Nat.succ_eq_add_one, ← ha]; exact ha1

  let m : V →ₗ[A] V := (scaleSub A V (ϖ ^ a)).subtype ∘ₗ mulOntoScaledSubmodule A V (ϖ ^ a)
  have hm : ∀ v, m v = ϖ ^ a • v := fun v => rfl
  let E0 : Submodule A V := F'.comap m
  let ψ0 : E0 →ₗ[A] (F' ⧸ F.comap F'.subtype) :=
    (F.comap F'.subtype).mkQ ∘ₗ m.restrict (p := E0) (q := F') (fun x hx => hx)
  have hψ0 : Function.Surjective ψ0 := by
    intro z
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hz' : z ∈ Fa a := haF'.symm ▸ hz
    obtain ⟨u, hu, v, ⟨hv, y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz'
    refine ⟨⟨y, hv⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have : (ϖ ^ a • y) - (u + ϖ ^ a • y) = -u := by abel
    show (ϖ ^ a • y) - (u + ϖ ^ a • y) ∈ F
    rw [this]
    exact F.neg_mem hu
  let π : E0 →ₗ[A] E0.map (scaleSub A V ϖ).mkQ :=
    ((scaleSub A V ϖ).mkQ).restrict (p := E0) (q := E0.map (scaleSub A V ϖ).mkQ)
      (fun x hx => Submodule.mem_map_of_mem hx)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker ψ0 := by
    rintro ⟨x, hx⟩ hxk
    rw [LinearMap.mem_ker] at hxk ⊢
    have h1 : (scaleSub A V ϖ).mkQ x = 0 := congrArg Subtype.val hxk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨y, rfl⟩ := h1
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show ϖ ^ a • ϖ • y ∈ F
    rw [← haF]
    refine Submodule.mem_sup_right ⟨hx, y, ?_⟩
    rw [pow_succ, mul_smul]
  refine ⟨E0.map (scaleSub A V ϖ).mkQ,
    (LinearMap.ker π).liftQ ψ0 hker ∘ₗ (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := hψ0 z
  refine ⟨LinearMap.quotKerEquivOfSurjective π hπ (Submodule.Quotient.mk x), ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl







end Subquotients

theorem factor_action_on_tensor_product_holds : AtFactorTprod := by
  intro O _ ι _ _ Nb _ _ τ p x
  unfold atFactor
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext σ
  by_cases h : σ = τ
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem tprod_mem_tensorSubmodule {O : Type} [CommRing O] {ι : Type} [Fintype ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (x : ∀ τ, Nb τ)
    (hx : ∀ τ, x τ ∈ B τ) : PiTensorProduct.tprod O x ∈ tensSub B := by
  refine ⟨PiTensorProduct.tprod O (fun τ => (⟨x τ, hx τ⟩ : B τ)), ?_⟩
  rw [PiTensorProduct.map_tprod]
  rfl

theorem tensorSubmodule_le_of_tprod_mem {O : Type} [CommRing O] {ι : Type} [Fintype ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ))
    (U : Submodule O (⨂[O] τ, Nb τ))
    (h : ∀ x : ∀ τ, Nb τ, (∀ τ, x τ ∈ B τ) → PiTensorProduct.tprod O x ∈ U) : tensSub B ≤ U := by
  rintro _ ⟨z, rfl⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact U.smul_mem _ (h _ fun τ => (u τ).2)
  | add a b ha hb =>
    rw [map_add]
    exact U.add_mem ha hb

theorem tensor_weight_kill_holds : TensorWeightKill := by
  intro O _ ι _ _ Nb _ _ B s a p l c ha hp
  have key : tensSub (chainB B (insert a s)) ≤
      (tensSub (chainB B s)).comap ((l ^ c) • atFactor a p) := by
    apply tensorSubmodule_le_of_tprod_mem
    intro x hx
    rw [Submodule.mem_comap, LinearMap.smul_apply, factor_action_on_tensor_product_holds,
      ← MultilinearMap.map_update_smul]
    try rw [Function.update_idem]
    apply tprod_mem_tensorSubmodule
    intro τ
    by_cases h : τ = a
    · subst h
      simp only [Function.update_self, chainB, if_neg ha]
      exact hp _
    · rw [Function.update_of_ne h]
      have h1 := hx τ
      simp only [chainB, Finset.mem_insert, h, false_or] at h1 ⊢
      exact h1
  intro y hy
  exact key hy

theorem chain_monotone_holds : ChainMono := by
  intro O _ ι _ _ Nb _ _ B s s' hss
  apply tensorSubmodule_le_of_tprod_mem
  intro x hx
  apply tprod_mem_tensorSubmodule
  intro τ
  have h1 := hx τ
  simp only [chainB] at h1 ⊢
  by_cases h : τ ∈ s
  · rw [if_pos (hss h)]
    trivial
  · rw [if_neg h] at h1
    split_ifs
    · trivial
    · exact h1

theorem chain_ends_holds : ChainEnds := by
  intro O _ ι _ _ Nb _ _ B
  constructor
  · have h0 : chainB B ∅ = B := by
      funext τ
      simp [chainB]
    rw [h0]
  · rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    apply tprod_mem_tensorSubmodule
    intro τ
    simp [chainB]


theorem factorAction_id {O : Type} [CommRing O] {ι : Type} [Fintype ι] [DecidableEq ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (a : ι) (y : ⨂[O] τ, Nb τ) :
    atFactor a (LinearMap.id : Nb a →ₗ[O] Nb a) y = y := by
  unfold atFactor
  rw [Function.update_eq_self a (fun τ => (LinearMap.id : Nb τ →ₗ[O] Nb τ)), PiTensorProduct.map_id]
  rfl

theorem forms_induction_holds : FormsStep := by
  intro O _ A _ _ G _ Γ K jK T _ V W _ _ _ _ _ _ _ _ _ _ S F F' ψ hst hnat hker hsub f hf
  have hmem : (fun g => ψ ⟨(f : G → V) g, hf g⟩) ∈ Forms O Γ jK W := by
    intro γ g κ
    have h1 : (⟨(f : G → V) ((γ : G) * g * κ), hf _⟩ : F') = jK κ⁻¹ • ⟨(f : G → V) g, hf g⟩ :=
      Subtype.ext (f.2 γ g κ)
    show ψ _ = jK κ⁻¹ • ψ _
    rw [h1, map_smul]
  let φ : Forms O Γ jK W := ⟨_, hmem⟩
  have h0 : LocalizedModule.mk φ (1 : S) = LocalizedModule.mk 0 (1 : S) := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h0
  have hu' : (u : T) • φ = 0 := by
    simpa [Submonoid.smul_def] using hu
  refine ⟨u, u.2, fun g => ?_⟩
  apply hker ⟨_, hst F' u f hf g⟩
  rw [← hnat F' ψ u f φ hf (hst F' u f hf) (fun _ => rfl) g, hu']
  rfl

theorem forms_devissage_holds : FormsDevissage := by
  intro O _ A _ _ G _ Γ K jK T _ V _ _ _ _ _ S D₀ D E hN hA hD0 hDE hstep f hf
  let Φ : Submodule A V → Submodule O (V ⧸ D₀) := fun F => (F.restrictScalars O).map D₀.mkQ
  have hΦmono : ∀ F1 F2 : Submodule A V, F1 ≤ F2 → Φ F1 ≤ Φ F2 := fun F1 F2 h =>
    Submodule.map_mono (fun x hx => h hx)
  have hΦ : ∀ F1 F2 : Submodule A V, D ≤ F1 → Φ F2 ≤ Φ F1 → F2 ≤ F1 := by
    intro F1 F2 h1 h x hx
    obtain ⟨y, hy, hxy⟩ := h (Submodule.mem_map_of_mem (f := D₀.mkQ) (show x ∈ F2.restrictScalars O from hx))
    have h2 : y - x ∈ D₀ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      exact sub_eq_zero.mpr hxy
    have h3 : y - x ∈ F1 := h1 (hD0 h2)
    have h4 : x = y - (y - x) := by abel
    rw [h4]
    exact F1.sub_mem hy h3
  let PP : Set (Submodule A V) := {F | D ≤ F ∧ F ≤ E ∧
    ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F}
  have hE : E ∈ PP := ⟨hDE, le_rfl, 1, S.one_mem, by simpa using hf⟩
  obtain ⟨_, ⟨F, hF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (Φ '' PP) ⟨_, E, hE, rfl⟩
  obtain ⟨hDF, hFE, s, hs, hsf⟩ := hF
  by_cases hEq : F ≤ D
  · exact ⟨s, hs, fun g => hEq (hsf g)⟩
  · exfalso
    have hlt : D < F := lt_of_le_not_ge hDF hEq
    have hNA : IsNoetherian A V := isNoetherian_of_tower O hN
    obtain ⟨F0, ⟨hDF0, hF0F⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr hNA
      {F0 : Submodule A V | D ≤ F0 ∧ F0 < F} ⟨D, le_rfl, hlt⟩
    have hcov : F0 ⋖ F := ⟨hF0F, fun c h1 h2 => hmax c ⟨hDF0.trans h1.le, h2⟩ h1⟩
    obtain ⟨s', hs', hs'f⟩ := hstep F0 F hDF0 hcov hFE (s • f) hsf
    have hF0 : F0 ∈ PP := ⟨hDF0, hF0F.le.trans hFE, s' * s, S.mul_mem hs' hs, by
      intro g
      rw [mul_smul]
      exact hs'f g⟩
    apply hmin (Φ F0) ⟨F0, hF0, rfl⟩
    refine lt_of_le_not_ge (hΦmono _ _ hF0F.le) fun h => ?_
    exact absurd (hΦ F0 F hDF0 h) (not_le_of_gt hF0F)

theorem theorem_w_central_of_simple_quotients (hSS : SimpleSubquotOfPower) (hIso : SubquotIso) : TheoremWCore := by
  intro O _ A _ _ G _ Γ K jK ι _ _ Nb _ _ B _ _ T _ _ _ _ S l ϖ n₀ ω pr e Λ L _ _ _ _ _ hwt depth i T2
    ex c' hNoe hArt hdvd hstab he hHS hHN hclass hhw hIN1 hex hIN2
  let DA : Finset ι → Submodule A (⨂[O] τ, Nb τ) := fun s =>
    { toAddSubmonoid := (tensSub (chainB B s)).toAddSubmonoid
      smul_mem' := fun a x hx => hstab s a x hx }
  have hDA : ∀ s x, x ∈ DA s ↔ x ∈ tensSub (chainB B s) := fun s x => Iff.rfl
  have hends := chain_ends_holds O ι Nb B
  have hmono : ∀ s s' : Finset ι, s ⊆ s' → DA s ≤ DA s' := fun s s' h x hx =>
    chain_monotone_holds O ι Nb B s s' h hx
  have hval : ∀ (c : ℕ) (f : Forms O Γ jK (⨂[O] τ, Nb τ)) (g : G),
      (((algebraMap O T l) ^ c • f : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g =
        l ^ c • (f : G → ⨂[O] τ, Nb τ) g := by
    intro c f g
    rw [← map_pow, algebraMap_smul]
    rfl
  have hpow : scaleSub A (⨂[O] τ, Nb τ) (ϖ ^ (n₀ * ∑ τ, ex τ)) ≤ DA ∅ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, hu⟩ := hdvd
    rw [hDA, hends.1, pow_mul, hu, mul_pow, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (tensor_reduction_holds O ι Nb B l ex hex y)
  have hstep : ∀ (s : Finset ι) (a : ι), a ∉ s → ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ),
      (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA (insert a s)) →
      ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ cTau T2 ex c' a • f) :
        Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s := by
    intro s a ha f hf
    have hkill : ∀ c : ℕ, (∀ x : Nb a, l ^ c • x ∈ B a) →
        ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ c • f) :
          Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s := by
      intro c hc
      refine ⟨1, S.one_mem, fun g => ?_⟩
      rw [one_smul, hval]
      have h1 := tensor_weight_kill_holds O ι Nb B s a LinearMap.id l c ha hc _ (hf g)
      rwa [factorAction_id] at h1
    by_cases haT : a ∈ T2
    swap
    · have hc : cTau T2 ex c' a = ex a := by simp [cTau, haT]
      rw [hc]
      exact hkill _ (hex a)
    by_cases hle : ex a ≤ c' a
    · have hc : cTau T2 ex c' a = ex a := by simp [cTau, haT, hle]
      rw [hc]
      exact hkill _ (hex a)
    have hc : cTau T2 ex c' a = c' a := by
      simp only [cTau, haT, if_true]
      omega
    rw [hc]
    let E : Submodule A (⨂[O] τ, Nb τ) :=
      { carrier := {x | ∃ d ∈ DA s, ∃ n ∈ DA (insert a s), x = d + l ^ c' a • n}
        zero_mem' := ⟨0, (DA s).zero_mem, 0, (DA _).zero_mem, by simp⟩
        add_mem' := by
          rintro _ _ ⟨d, hd, n, hn, rfl⟩ ⟨d', hd', n', hn', rfl⟩
          exact ⟨d + d', (DA s).add_mem hd hd', n + n', (DA _).add_mem hn hn', by
            rw [smul_add]; abel⟩
        smul_mem' := by
          rintro b _ ⟨d, hd, n, hn, rfl⟩
          exact ⟨b • d, (DA s).smul_mem b hd, b • n, (DA _).smul_mem b hn, by
            rw [smul_add, smul_comm]⟩ }
    have hDE : DA s ≤ E := fun d hd => ⟨d, hd, 0, (DA _).zero_mem, by simp⟩
    have hD0 : tensSub B ≤ (DA s).restrictScalars O := by
      intro x hx
      rw [← hends.1] at hx
      exact hmono ∅ s (Finset.empty_subset _) hx
    refine forms_devissage_holds O A G Γ K jK T (⨂[O] τ, Nb τ) S (tensSub B) (DA s) E hNoe hArt hD0 hDE
      ?_ _ (fun g => ⟨0, (DA s).zero_mem, _, hf g, by rw [hval, zero_add]⟩)
    intro F F' hDF hcov hF'E
    have hsimple : IsSimpleModule A (F' ⧸ F.comap F'.subtype) :=
      (covBy_iff_quot_is_simple hcov.le).mp hcov
    have hsq := hSS O A (⨂[O] τ, Nb τ) ϖ _ F F' hcov.le
      (hpow.trans ((hmono ∅ s (Finset.empty_subset _)).trans hDF)) hsimple
    obtain ⟨μ, ⟨iso⟩⟩ := hclass _ hsimple hsq
    have hcf := hIso A _ _ (L μ) ⟨iso⟩ hsq
    let ψ : F' →ₗ[A] L μ := iso.toLinearMap.comp (F.comap F'.subtype).mkQ
    have hψ0 : ∀ x : F', (x : ⨂[O] τ, Nb τ) ∈ F → ψ x = 0 := by
      intro x hx
      show iso ((F.comap F'.subtype).mkQ x) = 0
      have h1 : (F.comap F'.subtype).mkQ x = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (show x ∈ F.comap F'.subtype from hx)
      rw [h1, map_zero]
    have hker : ∀ x : F', ψ x = 0 → (x : ⨂[O] τ, Nb τ) ∈ F := by
      intro x hx
      have h1 : (F.comap F'.subtype).mkQ x = 0 := iso.injective (by rw [map_zero]; exact hx)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    have hdeep : i a < depth a (hwt μ a) := by
      by_contra hnot
      have hle' : depth a (hwt μ a) ≤ i a := not_lt.mp hnot
      obtain ⟨z, hz⟩ := hhw μ a
      obtain ⟨x, rfl⟩ : ∃ x, ψ x = z :=
        (iso.surjective.comp (Submodule.mkQ_surjective _)) z
      apply hz
      rw [← map_smul]
      apply hψ0
      obtain ⟨d, hd, n, hn, hxe⟩ := hF'E x.2
      rw [Submodule.coe_smul, hxe, smul_add, smul_comm]
      refine F.add_mem (hDF ((DA s).smul_mem _ hd)) (hDF ?_)
      rw [he]
      exact tensor_weight_kill_holds O ι Nb B s a (pr a (hwt μ a)) l (c' a) ha
        (hIN2 a haT _ hle') n hn
    have hvan : Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) := by
      by_contra hns
      exact absurd (hIN1 μ hcf hns a haT) (not_le.mpr hdeep)
    exact forms_induction_holds O A G Γ K jK T (⨂[O] τ, Nb τ) (L μ) S F F' ψ hHS (hHN μ) hker hvan
  have hall : ∀ s : Finset ι, ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ),
      (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA s) →
      ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) • f) :
        Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      exact ⟨1, S.one_mem, by simpa using hf⟩
    | insert a s ha ih =>
      intro f hf
      obtain ⟨σ1, hσ1, h1⟩ := hstep s a ha f hf
      obtain ⟨σ2, hσ2, h2⟩ := ih _ h1
      refine ⟨σ2 * σ1, S.mul_mem hσ2 hσ1, fun g => ?_⟩
      have e1 : (σ2 * σ1) • ((algebraMap O T l) ^ (∑ τ ∈ insert a s, cTau T2 ex c' τ) • f) =
          σ2 • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) •
            (σ1 • ((algebraMap O T l) ^ cTau T2 ex c' a • f))) := by
        rw [Finset.sum_insert ha]
        simp only [smul_smul]
        congr 1
        ring
      rw [e1]
      exact h2 g
  intro y
  induction y using LocalizedModule.induction_on with
  | h f σ0 =>
    obtain ⟨σ, hσ, h⟩ := hall Finset.univ f (fun g => by rw [hDA, hends.2]; trivial)
    refine ⟨σ • ((algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • f), ?_, ⟨σ, hσ⟩ * σ0, ?_⟩
    · refine ⟨Subtype.property _, fun g _ => ?_⟩
      have h1 := h g
      rwa [hDA, hends.1] at h1
    · rw [LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel_common_left ⟨σ, hσ⟩ σ0 _

theorem dualWeyl_module_finite (O : Type) [CommRing O] [IsNoetherianRing O] (r n : ℕ) (ν : Fin n → ℕ) :
    Module.Finite O (dualWeyl O r n ν) := by
  have h : dualWeyl O r n ν ≤ homogeneousSubmodule (Fin r × Fin n) O (∑ s, ν s) := by
    intro f hf
    have h1 := (mem_dualWeyl_iff.1 hf).1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← lclosedeq_weight_sum, h1 hm]
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le (homogeneousSubmodule_fg _ _ _) h)

theorem finite_quotient_of_pow_smul_mem (O : Type) [CommRing O] [IsNoetherianRing O] (V : Type) [AddCommGroup V]
    [Module O V] [Module.Finite O V] (l : O) (J : ℕ) (U : Submodule O V)
    (hfin : Finite (O ⧸ Ideal.span {l})) (hU : ∀ x : V, l ^ J • x ∈ U) : Finite (V ⧸ U) := by
  haveI : Finite (O ⧸ (Ideal.span {l}) ^ J) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (Ideal.span {l})) J
  haveI : Finite (V ⧸ ((Ideal.span {l}) ^ J • ⊤ : Submodule O V)) :=
    Module.finite_of_finite (O ⧸ (Ideal.span {l}) ^ J)
  have hle : ((Ideal.span {l}) ^ J • ⊤ : Submodule O V) ≤ U := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    rw [mul_comm, mul_smul]
    exact U.smul_mem _ (hU n)
  exact Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

theorem theorem_w_top_of_simple_quotients (hSS : SimpleSubquotOfPower) (hIso : SubquotIso) : TheoremWTop := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  obtain ⟨hl, hu, hfin, hdvd, hh, ht, hshape, hecl, hex, hstab, he, hHS, hHN, hclass, hhw, hIN1⟩ := hT
  haveI : ∀ τ : ι, Module.Finite O (dualWeyl O N N (res N (lam τ))) :=
    fun τ => dualWeyl_module_finite O N N _
  let pr : ∀ τ : ι, (Fin N → ℕ) →
      dualWeyl O N N (res N (lam τ)) →ₗ[O] dualWeyl O N N (res N (lam τ)) := fun τ w =>
    (weightedHomogeneousComponent (rowW N N) w).restrict
      (fun x hx => dualWeylRowGraded O N N (res N (lam τ)) w x hx)
  have hexO : ∀ τ, LatIncl (l : O) (deltaIn O N lam τ) (ex τ) := fun τ x =>
    LA.la_incl_R_of_Z O N N le_rfl (res N (lam τ)) l (ex τ) hu (hex τ) x x.2
  have hNoe : IsNoetherian O (NablaT O N lam) := inferInstance
  have hArt : IsArtinian O (NablaT O N lam ⧸ tensSub (deltaIn O N lam)) := by
    haveI := finite_quotient_of_pow_smul_mem O (NablaT O N lam) (l : O) (∑ τ, ex τ) (tensSub (deltaIn O N lam)) hfin
      (tensor_reduction_holds O ι _ (deltaIn O N lam) (l : O) ex hexO)
    exact isArtinian_of_finite
  have he' : ∀ τ w (x : NablaT O N lam), e τ w • x = atFactor τ (pr τ w) x := by
    intro τ w x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [smul_comm, map_smul, he τ w u (pr τ w (u τ)) rfl, factor_action_on_tensor_product_holds]
    | add a b ha hb => rw [smul_add, map_add, ha, hb]
  have hIN2 : ∀ τ ∈ T2, ∀ w, depthAt N k j lam τ w ≤ ((i τ : ℕ) : ℤ) →
      ∀ x : dualWeyl O N N (res N (lam τ)),
        (l : O) ^ cFloor l N k t h lam j q xm xp ecl i τ • pr τ w x ∈ deltaIn O N lam τ := by
    intro τ hτ w hw x
    obtain ⟨hrows, hanti, hblock, hspread, hcloud, hlows, habove, hle, htop⟩ := hshape τ hτ
    have hA := application_window hD l k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ) hl ht
    rw [hrows] at hA
    have hE := hA hanti hblock hspread hh hcloud hlows habove hle htop (ecl τ) (hecl τ hτ) (i τ) w hw
    exact pow_smul_weighted_component_mem_weyl O l N (res N (lam τ)) w _ hu hE x x.2
  have hmain := theorem_w_central_of_simple_quotients hSS hIso O A G Γ K jK ι (fun τ => dualWeyl O N N (res N (lam τ)))
    (deltaIn O N lam) T S (l : O) ϖ n₀ (Fin N → ℕ) pr e Λ L hwt (depthAt N k j lam)
    (fun τ => (i τ : ℤ)) T2 ex (cFloor l N k t h lam j q xm xp ecl i) hNoe hArt hdvd hstab he' hHS hHN
    hclass hhw hIN1 hexO hIN2
  exact ⟨hmain, Nat.sInf_le hmain⟩

open Formalism.RankGapBounds.ChebyshevFactorialBounds in
theorem block_ideal_at_of_top_theorem (hTop : TheoremWTop) : BlockIdealAt := by
  intro hD ι _ _ D l O _ _ _ A _ _ G _ Γ K jK lam _ _ T _ _ _ _ S ϖ n₀ e Λ L _ _ _ _ _ hwt hP hT hmaxB hJ
  have hl : l.Prime := hT.1
  have h1 := (hTop hD O A G Γ K jK ι l D.Nr D.k D.t D.h lam D.T2 D.j D.q D.xlo D.xhi
    (fun τ => D.ecl τ l) (fun τ => D.ex τ l) (fun τ => D.depth τ l) T S ϖ n₀ e Λ L hwt hT).2
  have h2 : (D.J l : ℝ) ≤ ((∑ τ, cTau D.T2 (fun τ => D.ex τ l)
      (cFloor l D.Nr D.k D.t D.h lam D.j D.q D.xlo D.xhi (fun τ => D.ecl τ l)
        (fun τ => D.depth τ l)) τ : ℕ) : ℝ) := by
    exact_mod_cast hJ.trans h1
  refine h2.trans ?_
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro τ _
  refine le_trans (le_of_eq ?_) (tau_term_le_correction_bound D hP l hl τ)
  congr 1
  unfold cTau
  by_cases hτ : τ ∈ D.T2
  · rw [if_pos hτ, if_pos hτ]
    unfold cFloor
    simp only [hmaxB τ hτ]
  · rw [if_neg hτ, if_neg hτ]


theorem weight_theorem_top : TheoremWTop := theorem_w_top_of_simple_quotients simple_subquotient_of_power_holds subquotient_iso_holds

theorem block_ideal_at : BlockIdealAt := block_ideal_at_of_top_theorem weight_theorem_top


theorem exponent_le_of_integral_inclusion_holds : ExpLeOfInclZ := by
  intro r ν μ l e ⟨m, hm, h⟩ x hx
  refine ⟨(m : ℤ), fun hd => hm (Int.natCast_dvd_natCast.mp hd), ?_⟩
  have h1 := h x hx.1
  push_cast at h1
  exact h1

theorem exact_exponents_fit_holds : ExactExponentsFit := by
  intro l N k lam hl hN hk
  exact ⟨LA.exact_z_specialization N N le_rfl _ hN l hl,
    fun μ => exponent_le_of_integral_inclusion_holds k _ μ l _ (LA.exact_z_specialization k k le_rfl _ hk l hl)⟩

theorem top_inclusion_monotone_holds : TopInclMono := by
  intro O _ A _ _ G _ Γ K jK ι l N lam _ _ T _ _ _ _ S J J' hJ h y
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJ
  obtain ⟨x, hx, s, hxs⟩ := h y
  refine ⟨(algebraMap O T (l : O)) ^ d • x, ?_, s, ?_⟩
  · show (((algebraMap O T (l : O)) ^ d • x : Forms O Γ jK (NablaT O N lam)) : G → NablaT O N lam) ∈
      formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))
    rw [← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx
  · rw [← LocalizedModule.smul'_mk, hxs, smul_smul, ← pow_add, add_comm]

theorem weight_theorem_top_coarse : TheoremWTopCoarse := by
  intro hD O _ _ _ A _ _ G _ Γ K jK ι _ _ l N k t h lam T2 j q xm xp ecl ex i _ _ T _ _ _ _ S ϖ n₀ e Λ L
    _ _ _ _ _ hwt hT
  have hl : l.Prime := hT.1
  refine top_inclusion_monotone_holds O A G Γ K jK ι l N lam T S _ _ ?_
    (weight_theorem_top hD O A G Γ K jK ι l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e Λ L hwt hT).1
  apply Finset.sum_le_sum
  intro τ _
  unfold cTau
  split_ifs
  · exact min_le_min le_rfl (Nat.floor_le_floor
      (c_prime_le_coarse_holds l k (j τ) t (q τ) h N (ecl τ) _ _ _ _ hl.two_le (Nat.cast_nonneg _)))
  · exact le_rfl

open Formalism.RankGapBounds.ChebyshevFactorialBounds in
theorem block_ideal_bound_derived : BlockIdealBound5Derived := by
  intro hD ι _ _ D hP h l hl hE hlJ h2 h3 h4
  obtain ⟨O, _, _, _, A, _, _, G, _, Γ, K, jK, lam, _, _, T, _, _, _, _, S, ϖ, n₀, e, Λ, L, _, _, _, _, _,
    hwt, hT, hB, hJ⟩ := h l hl hE hlJ h2 h3 h4
  exact block_ideal_at hD ι D l O A G Γ K jK lam T S ϖ n₀ e Λ L hwt hP hT hB hJ

theorem depth_as_weight_sum_holds : DepthAsU := by
  intro N c lam w
  unfold depth2 res varpi UN
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · ring
  · ring


end Formalism.CohomologicalDescent.DepthNonnegative
end
end
