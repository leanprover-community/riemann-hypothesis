import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DegreeProportionalWords
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside

section
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
end
end

section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FamilyDegreeRatio

theorem gap_lam {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    (H : Num k r lam u b bv ga h q0) (a c : Fin (2 * r + k + 1)) (hac : a < c) :
    100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hh, -, hq1, hq2, -⟩ := H
  by_cases hc : c.val + 1 < k
  · linarith [hga a c hac hc]
  by_cases ha : a.val + 1 < k
  ·
    have hp : k - 1 < 2 * r + k + 1 := by omega
    have hq : k < 2 * r + k + 1 := by omega
    have hpq : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, hp⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, hq⟩ := by
      have h1 : ¬ (k < k - 1) := by omega
      have h2 : (k - (k - 1)) % 2 = 1 := by omega
      simp [PI.BesselPeriodGGP.eps48, h1, h2]
    have hgpq := hh _ _ hpq
    have ⟨p1, p2⟩ := hnd ⟨k - 1, hp⟩ (by show k ≤ k - 1 + 1; omega)
    have ⟨q1, q2⟩ := hnd ⟨k, hq⟩ (by show k ≤ k + 1; omega)
    have habs : |lam ⟨k - 1, hp⟩ - lam ⟨k, hq⟩| ≤ bv := abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 := (hcl a ha).1
    have h2 := (hnd c (by omega)).2
    linarith
  ·
    have hac' : a.val < c.val := hac
    have hd : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have had : a < ⟨a.val + 1, hd⟩ := by rw [Fin.lt_def]; simp
    have hdc : (⟨a.val + 1, hd⟩ : Fin (2 * r + k + 1)) ≤ c := by rw [Fin.le_iff_val_le_val]; simp; omega
    have hne : PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r ⟨a.val + 1, hd⟩ := by
      have h1 : ¬ (a.val < k - 1) := by omega
      have h2 : ¬ (a.val + 1 < k - 1) := by omega
      rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
    have hg := hh _ _ hne
    have hlt := hanti had
    have hle := hanti.antitone hdc
    rw [abs_of_pos (by linarith)] at hg
    linarith

theorem abs_coord_le_of_lOneNorm_le {n : ℕ} {ν : Fin n → ℤ} {q : ℕ} (hν : n1 ν ≤ q) (a : Fin n) : |(ν a : ℝ)| ≤ q := by
  have h1 : (ν a).natAbs ≤ n1 ν :=
    Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h2]
  exact_mod_cast h1.trans hν

theorem degree_ratios : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) ∧ (∀ I : Finset (Fin (2 * r + k + 1)), Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν + eZ I) a : ℝ)) ≤ ((2 * r + k + 1) : ℝ) ^ I.card * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ))) ∧ ∀ s, Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) / Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) = ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| / |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))| := by
  intro k r lam u b bv ga h q0 H ν hν
  have hgl := fun a c (hac : a < c) => gap_lam H a c hac
  have hνb := fun a => abs_le.mp (abs_coord_le_of_lOneNorm_le hν a)
  have hint := H.2.1.2
  have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hgap : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    have := hgl a c hac
    have := hνb a
    have := hνb c
    linarith
  have hanti : StrictAnti (fun a => lam a + (ν a : ℝ)) := fun a c hac => by
    have := hgap a c hac
    simp only
    linarith
  have hinj := hanti.injective
  have hZ : ∀ a c, ∃ m : ℤ, (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) = (m : ℝ) := by
    intro a c
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨m2, hm2⟩ := hint c
    exact ⟨m1 - m2 + ν a - ν c, by push_cast; linarith⟩
  have hpos : 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := Formalism.QuantumDeterminants.formal_degree_pos_holds _ _ hinj
  refine ⟨hpos, ?_, ?_⟩
  · intro I
    have hb := (Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound (2 * r + k + 1) (fun a => lam a + (ν a : ℝ)) I hanti hZ hgap).2
    have hfun : (fun a => lam a + (((ν + eZ I) a : ℤ) : ℝ)) =
        (fun a => (lam a + (ν a : ℝ)) + if a ∈ I then 1 else 0) := by
      funext a
      simp only [Pi.add_apply, eZ]
      split_ifs <;> push_cast <;> ring
    rw [hfun]
    rw [div_le_iff₀ hpos] at hb
    push_cast at hb
    exact hb
  · intro s
    have hfun : (fun a => lam a + (((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) + Pi.single s (-1 : ℝ) := by
      funext a
      by_cases has : a = s
      · subst has
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
        ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne has, sub_zero, add_zero]
    rw [hfun, GlobalTheory.CompareIterDegree.fdeg_ratio_abs _ s (-1) hinj]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [abs_div]
    congr 2

end GlobalTheory.FamilyDegreeRatio
end
