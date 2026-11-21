import Mathlib
import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DegreeProportionalWords

open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompareIterDegree

open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords





theorem l1_add_le {A : Type} (a b : A →₀ ℂ) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  have e : ∀ c : A →₀ ℂ, c.support ⊆ a.support ∪ b.support →
      l1 c = ∑ ν ∈ a.support ∪ b.support, ‖c ν‖ := fun c hc =>
    sum_subset hc fun ν _ hν => by simp [Finsupp.notMem_support_iff.1 hν]
  rw [e _ Finsupp.support_add, e a subset_union_left, e b subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun ν _ => norm_add_le _ _

theorem comb_eq {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (j : A → V) (μ : A) (a : A →₀ ℂ) :
    comb j μ a = Finsupp.linearCombination ℂ (fun ν => j (μ + ν)) a := rfl



theorem fdeg_ratio_abs {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (hinj : Function.Injective μ) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, |(μ s + t - μ c) / (μ s - μ c)| := by
  set μ' : Fin n → ℝ := μ + Pi.single s t with hμ'
  have hμ'a : ∀ a, μ' a = μ a + if a = s then t else 0 := by
    intro a; simp [hμ', Pi.single_apply]
  set r : Fin n → ℝ := fun c => |(μ s + t - μ c) / (μ s - μ c)| with hr
  have hfac : ∀ a b : Fin n, a < b →
      |μ' a - μ' b| / |μ a - μ b| = (if a = s then r b else 1) * (if b = s then r a else 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    by_cases has : a = s
    · subst has
      have hbs : b ≠ a := fun h => hne h.symm
      rw [hμ'a, hμ'a, if_pos rfl, if_neg hbs, if_pos rfl, if_neg hbs]
      simp [hr, abs_div]
    · by_cases hbs : b = s
      · subst hbs
        rw [hμ'a, hμ'a, if_neg has, if_pos rfl, if_neg has, if_pos rfl]
        simp only [hr, one_mul, add_zero, abs_div]
        rw [abs_sub_comm (μ a) (μ b + t), abs_sub_comm (μ a) (μ b)]
      · rw [hμ'a, hμ'a, if_neg has, if_neg hbs, if_neg has, if_neg hbs]
        have h0 : μ a - μ b ≠ 0 := sub_ne_zero.2 (fun h => hne (hinj h))
        simp only [add_zero, mul_one]
        exact div_self (abs_ne_zero.2 h0)
  have hden : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => ?_
    have hab : a < b := (mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hden, ← prod_div_distrib]
  simp_rw [← prod_div_distrib]
  rw [prod_congr rfl (fun a _ => prod_congr rfl (fun b hb => hfac a b (mem_filter.1 hb).2))]
  simp_rw [prod_mul_distrib]
  have h1 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if a = s then r b else 1)) = ∏ b ∈ univ.filter (fun b : Fin n => s < b), r b := by
    rw [prod_eq_single s]
    · simp
    · intro a _ has; simp [has]
    · intro h; exact absurd (mem_univ s) h
  have h2 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if b = s then r a else 1)) = ∏ a ∈ univ.filter (fun a : Fin n => a < s), r a := by
    rw [prod_filter]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_ite_eq']
    simp
  rw [h1, h2, ← prod_filter_mul_prod_filter_not (univ.erase s) (fun c => s < c)]
  congr 1
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega

theorem fac_nonneg {d t : ℝ} (hd : 1 ≤ |d|) (ht : |t| ≤ 1) : 0 ≤ (d + t) / d := by
  rw [abs_le] at ht
  rcases le_abs.1 hd with h | h
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg_of_nonpos (by linarith) (by linarith)

theorem fdeg_ratio {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (ht : |t| ≤ 1)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |μ a - μ b|) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c) := by
  have hinj : Function.Injective μ := fun a b hab => by
    by_contra hne
    have := hgap a b hne
    rw [hab, sub_self, abs_zero] at this
    linarith
  rw [fdeg_ratio_abs μ s t hinj]
  refine prod_congr rfl fun c hc => abs_of_nonneg ?_
  rw [add_sub_right_comm]
  exact fac_nonneg (hgap s c (ne_of_mem_erase hc).symm) ht


theorem sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ - Pi.single s 1 = μ + Pi.single s (-1) := by
  rw [Pi.single_neg, sub_eq_add_neg]



theorem chain_bound {α : Type} [DecidableEq α] (F : Finset α → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (I : Finset α)
    (hpos : ∀ J ⊆ I, 0 < F J)
    (hstep : ∀ J s, s ∉ J → insert s J ⊆ I → lo ≤ F (insert s J) / F J ∧ F (insert s J) / F J ≤ hi) :
    lo ^ I.card ≤ F I / F ∅ ∧ F I / F ∅ ≤ hi ^ I.card := by
  have h0 := hpos ∅ (empty_subset _)
  induction I using Finset.induction_on with
  | empty => simp [h0.ne']
  | insert s J hs ih =>
    have hJ := hpos J (subset_insert _ _)
    obtain ⟨i1, i2⟩ := ih (fun K hK => hpos K (hK.trans (subset_insert _ _)))
      (fun K u hu hK => hstep K u hu (hK.trans (subset_insert _ _)))
    obtain ⟨j1, j2⟩ := hstep J s hs subset_rfl
    have e : F (insert s J) / F ∅ = F J / F ∅ * (F (insert s J) / F J) := by field_simp
    rw [card_insert_of_notMem hs, pow_succ, pow_succ, e]
    exact ⟨mul_le_mul i1 j1 hlo (div_pos hJ h0).le,
      mul_le_mul i2 j2 (hlo.trans j1) ((div_pos hJ h0).le.trans i2)⟩



theorem inj_of_gapTwo {n : ℕ} {μ : Fin n → ℝ} (h : GapTwo μ) : Function.Injective μ := fun a b hab => by
  by_contra hne
  have := h a b hne
  rw [hab, sub_self, abs_zero] at this
  linarith

theorem inj_add_of_gapTwo {n : ℕ} {μ e : Fin n → ℝ} (h : GapTwo μ) (he : ∀ a b, |e a - e b| ≤ 1) :
    Function.Injective (μ + e) := fun a b hab => by
  by_contra hne
  have h1 := h a b hne
  have h2 := he b a
  rw [show μ a - μ b = e b - e a by simp only [Pi.add_apply] at hab; linarith] at h1
  linarith




theorem round_gap {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (g : ℝ → ℤ) (hm : Monotone g)
    (h2 : ∀ x, g (x + 2) = g x + 2) (h0 : g 0 = 0) :
    GapTwo (fun c => -(g (μ s - μ c) : ℝ)) ∧ ∀ c, c ≠ s → 0 < (μ s - μ c) * g (μ s - μ c) := by
  have key : ∀ x y : ℝ, x + 2 ≤ y → (g x : ℝ) + 2 ≤ g y := fun x y hxy => by
    have := hm hxy
    rw [h2] at this
    exact_mod_cast this
  refine ⟨fun a b hab => ?_, fun c hc => ?_⟩
  · rcases le_abs.1 (hg a b hab) with h | h
    · have := key (μ s - μ a) (μ s - μ b) (by linarith)
      exact le_abs.2 (Or.inl (by linarith))
    · have := key (μ s - μ b) (μ s - μ a) (by linarith)
      exact le_abs.2 (Or.inr (by linarith))
  · rcases le_abs.1 (hg s c hc.symm) with h | h
    · have := key 0 (μ s - μ c) (by linarith)
      rw [h0] at this
      exact mul_pos (by linarith) (by push_cast at this; linarith)
    · have := key (μ s - μ c) 0 (by linarith)
      rw [h0] at this
      exact mul_pos_of_neg_of_neg (by linarith) (by push_cast at this; linarith)

theorem fac_le {x y t : ℝ} (hxy : 0 < x * y) (h : t * y ≤ t * x) : (x + t) / x ≤ (y + t) / y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy.ne'
  have hy : y ≠ 0 := right_ne_zero_of_mul hxy.ne'
  have : (y + t) / y - (x + t) / x = (t * x - t * y) / (x * y) := by field_simp; ring
  have h2 := div_nonneg (sub_nonneg.2 h) hxy.le
  linarith

theorem real_step (h : DegStepBound) {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (t : ℝ)
    (ht : t = 1 ∨ t = -1) :
    1 / (n : ℝ) ≤ fdegHC (μ + Pi.single s t) / fdegHC μ ∧ fdegHC (μ + Pi.single s t) / fdegHC μ ≤ n := by
  have ht1 : |t| ≤ 1 := by rcases ht with rfl | rfl <;> simp
  rw [fdeg_ratio μ s t ht1 fun a b hab => le_trans one_le_two (hg a b hab)]
  have main : ∀ g : ℝ → ℤ, Monotone g → (∀ x, g (x + 2) = g x + 2) → g 0 = 0 →
      ((∀ x, t * g x ≤ t * x) → ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c) ≤ n) ∧
      ((∀ x, t * x ≤ t * g x) → 1 / (n : ℝ) ≤ ∏ c ∈ univ.erase s, (μ s + t - μ c) / (μ s - μ c)) := by
    intro g hm h2 h0
    obtain ⟨hg', hsg⟩ := round_gap hg s g hm h2 h0
    have hb : 1 / (n : ℝ) ≤ ∏ c ∈ univ.erase s, ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) ∧
        ∏ c ∈ univ.erase s, ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) ≤ n := by
      have hinj : Function.Injective ((fun c => -(g (μ s - μ c) : ℝ)) + Pi.single s t) :=
        inj_add_of_gapTwo hg' fun a b => by
          simp only [Pi.single_apply]; split_ifs <;> simp [ht1]
      have := h n _ s (inj_of_gapTwo hg') fun a b =>
        ⟨-g (μ s - μ a) - -g (μ s - μ b), by push_cast; rfl⟩
      rcases ht with rfl | rfl
      · simpa [h0, add_comm] using this.1 hinj
      · rw [sub_single] at this
        simpa [h0, add_comm, sub_eq_add_neg] using this.2 hinj
    have hn1 : ∀ c ∈ univ.erase s, 0 ≤ (μ s + t - μ c) / (μ s - μ c) := fun c hc => by
      rw [add_sub_right_comm]
      exact fac_nonneg (le_trans one_le_two (hg s c (ne_of_mem_erase hc).symm)) ht1
    have hn2 : ∀ c ∈ univ.erase s, 0 ≤ ((g (μ s - μ c) : ℝ) + t) / g (μ s - μ c) := fun c hc => by
      have := hg' s c (ne_of_mem_erase hc).symm
      simp only [sub_self, h0, Int.cast_zero, neg_zero, zero_sub, neg_neg] at this
      exact fac_nonneg (le_trans one_le_two this) ht1
    refine ⟨fun hx => le_trans (prod_le_prod hn1 fun c hc => ?_) hb.2,
      fun hx => le_trans hb.1 (prod_le_prod hn2 fun c hc => ?_)⟩
    · rw [add_sub_right_comm]
      exact fac_le (hsg c (ne_of_mem_erase hc)) (hx _)
    · rw [add_sub_right_comm]
      exact fac_le (by rw [mul_comm]; exact hsg c (ne_of_mem_erase hc)) (hx _)
  have hf := main (fun x => ⌊x⌋) Int.floor_mono (fun x => Int.floor_add_ofNat x 2) Int.floor_zero
  have hc := main (fun x => ⌈x⌉) Int.ceil_mono (fun x => Int.ceil_add_ofNat x 2) Int.ceil_zero
  rcases ht with rfl | rfl
  · exact ⟨hc.2 fun x => by simpa using Int.le_ceil x, hf.1 fun x => by simpa using Int.floor_le x⟩
  · exact ⟨hf.2 fun x => by simpa using Int.floor_le x, hc.1 fun x => by simpa using Int.le_ceil x⟩







end GlobalTheory.CompareIterDegree
