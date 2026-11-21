import Formalism.FrobeniusBaseCase.Statement

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

def ratVal (l : ℕ) [Fact l.Prime] : AddValuation ℚ (WithTop ℝ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else ((padicValRat l x : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have h := padicValRat.min_le_padicValRat_add (p := l) hxy
      rcases le_total (padicValRat l x) (padicValRat l y) with h1 | h1
      · rw [min_eq_left h1] at h
        refine le_trans (min_le_left _ _) ?_
        exact_mod_cast h
      · rw [min_eq_right h1] at h
        refine le_trans (min_le_right _ _) ?_
        exact_mod_cast h)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, mul_eq_zero, or_self, if_false]
      rw [padicValRat.mul hx hy]
      push_cast
      rfl)

theorem ratVal_apply (l : ℕ) [Fact l.Prime] {x : ℚ} (hx : x ≠ 0) :
    ratVal l x = ((padicValRat l x : ℝ) : WithTop ℝ) := by
  simp [ratVal, hx]

theorem ratVal_l (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ) = 1 := by
  rw [ratVal_apply l (by exact_mod_cast hl.out.ne_zero)]
  simp [padicValRat.self hl.out.one_lt]

theorem ratVal_l_inv (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  have h0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [ratVal_apply l (inv_ne_zero h0), padicValRat.inv, padicValRat.self hl.out.one_lt]
  simp

def exData (l i : ℕ) (hl : l.Prime) (hl3 : 3 ≤ l) (hi : Odd i) : Data ℚ Unit (Fin 2) :=
  haveI : Fact l.Prime := ⟨hl⟩
  { v := ratVal l
    l := l
    l_prime := hl
    l_ge := hl3
    v_l := ratVal_l l
    i := i
    i_odd := hi
    good := fun _ => True
    lev := fun c => c.val
    pure_good := fun _ _ => trivial
    ι := fun _ => 0
    ι_inj := fun _ _ _ => rfl
    ι_lev := fun _ => rfl
    al := fun c j b => if c = 0 ∧ j = 2 ∧ b = 1 then (l : ℚ)⁻¹ else 0
    g := fun c b => if c = 0 ∧ b = 1 then 1 else 0
    lam := fun _ _ => 0
    al_all := by
      intro c j b
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-((2 : ℕ) : ℝ)) ≤ -1)
      · simp
    al_good := by
      intro c _ j b _
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-(((2 : ℕ) : ℝ) - 1)) ≤ -1)
      · simp
    al_one := by
      intro c _ b
      simp
    al_two := by
      intro c _ b
      by_cases h : c = 0 ∧ b = 1
      · simp [h]
      · have : ¬ (c = 0 ∧ 2 = 2 ∧ b = 1) := by tauto
        simp [h]
    g_int := by
      intro c b
      split_ifs <;> simp
    lam_int := by
      intro c b
      simp
    g_supp := by
      intro c _ b hb
      by_cases h : c = 0 ∧ b = 1
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd rfl hb
      · simp [h] }

theorem coeff_frob_smul {k : Type*} [Field k] {Z : Type*} (N : ℕ) (hN : 1 ≤ N)
    (f : MvPowerSeries Z k) (A : Z →₀ ℕ) : coeff (N • A) (frob N f) = (coeff A f) ^ N := by
  have h1 : ∀ d, N ∣ (N • A) d := fun d => by simp
  have h2 : (N • A).mapRange (· / N) (Nat.zero_div N) = A := by
    ext d
    simp [Nat.mul_div_cancel_left _ hN]
  show (if ∀ d, N ∣ (N • A) d then
    (coeff ((N • A).mapRange (· / N) (Nat.zero_div N)) f) ^ N else 0) = _
  rw [if_pos h1, h2]


theorem Data.base_case_k_one_holds {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C]
    (D : Data k Z C) : D.FrobeniusBaseCaseIdentity := by
  intro hi
  have hK : D.K = 1 := by simp [Data.K, Kn, hi]
  have hzero : ∀ w : ℝ, D.Wt w (0 : MvPowerSeries Z k) := by
    intro w A
    simp
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hK] at hc
    have : D.lev c = 0 := by omega
    rw [this]
    show D.Wt D.top (D.zvec c - D.zvec c)
    rw [sub_self]
    exact hzero _
  · intro c hc
    rw [hK] at hc
    have : D.zvec c = 0 := by
      unfold Data.zvec
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      rintro rfl
      rw [D.ι_lev] at hc
      omega
    rw [this]
    exact hzero _

end

end Formalism.BaseCaseIdentities
