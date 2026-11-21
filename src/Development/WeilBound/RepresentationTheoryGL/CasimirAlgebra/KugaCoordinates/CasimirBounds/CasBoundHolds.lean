import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeData

section
open Finset Matrix

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem pm_apply' (σ : Equiv.Perm Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ σ) := rfl

theorem pm_pm (σ τ : Equiv.Perm Q) (f : TV n ℂ Q) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) (pm τ f) = pm (σ * τ) f := rfl

theorem dot_pm_swap (a c : Q) (u v : TV n ℂ Q) :
    star u ⬝ᵥ (pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) v =
      star ((pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) u) ⬝ᵥ v := by
  let e : (Q → Fin n) ≃ (Q → Fin n) :=
    { toFun := fun I => I ∘ Equiv.swap a c, invFun := fun I => I ∘ Equiv.swap a c,
      left_inv := fun I => by funext x; simp, right_inv := fun I => by funext x; simp }
  simp only [dotProduct, Pi.star_apply, pm_apply']
  refine Fintype.sum_equiv e _ _ fun I => ?_
  have : (I ∘ Equiv.swap a c) ∘ Equiv.swap a c = I := by funext x; simp
  simp [e, this]

theorem re_swapSum_le' (f : TV n ℂ Q) (B : Finset Q) (p : Q)
    (hp : p ∉ B) (hf : ∀ q ∈ B, ∀ q' ∈ B, q ≠ q' → pm (Equiv.swap q q') f = -f) :
    (∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f).re ≤ (star f ⬝ᵥ f).re := by
  set Y : Module.End ℂ (TV n ℂ Q) := ∑ q ∈ B, pm (Equiv.swap p q) with hY
  have hYf : Y f = ∑ q ∈ B, pm (Equiv.swap p q) f := by simp [hY, LinearMap.sum_apply]
  have hsa : ∀ u v : TV n ℂ Q, star u ⬝ᵥ Y v = star (Y u) ⬝ᵥ v := by
    intro u v
    simp only [hY, LinearMap.sum_apply, dotProduct_sum, star_sum, sum_dotProduct, dot_pm_swap]
  have hq : ∀ q ∈ B, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (Y f) =
      f - Y f + pm (Equiv.swap p q) f := by
    intro q hqB
    have hpq : p ≠ q := fun h => hp (h ▸ hqB)
    rw [hYf, ← Finset.add_sum_erase B _ hqB, map_add, map_sum, pm_pm, Equiv.swap_mul_self]
    have : ∀ q' ∈ B.erase q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (pm (Equiv.swap p q') f) =
        -(pm (Equiv.swap p q') f) := by
      intro q' hq'
      obtain ⟨hne, hq'B⟩ := Finset.mem_erase.mp hq'
      have hpq' : p ≠ q' := fun h => hp (h ▸ hq'B)
      have hperm : Equiv.swap p q * Equiv.swap p q' = Equiv.swap p q' * Equiv.swap q q' := by
        ext x
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
        split_ifs <;> simp_all
      rw [pm_pm, hperm, ← pm_pm, hf q hqB q' hq'B (Ne.symm hne), map_neg]
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    have h1 : (pm 1 : Module.End ℂ (TV n ℂ Q)) f = f := rfl
    rw [h1]
    abel
  have hYY : Y (Y f) = (B.card : ℂ) • f - (B.card : ℂ) • Y f + Y f := by
    conv_lhs => rw [hY, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_const, ← hYf]
    simp [Nat.cast_smul_eq_nsmul]
  set g := f - Y f with hg
  have hYg : Y g = -((B.card : ℂ) • g) := by
    rw [hg, map_sub, hYY, smul_sub]
    abel
  have hgg : star g ⬝ᵥ g = (1 + (B.card : ℂ)) * (star f ⬝ᵥ g) := by
    conv_lhs => rw [hg]
    rw [star_sub, sub_dotProduct, ← hsa, ← hg, hYg, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  have hnn : 0 ≤ (star g ⬝ᵥ g).re := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_nonneg fun I _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (g I).re, sq_nonneg (g I).im]
  have hre : (star g ⬝ᵥ g).re = (1 + (B.card : ℝ)) * (star f ⬝ᵥ g).re := by
    rw [hgg]
    simp [Complex.mul_re]
  have hpos : 0 ≤ (star f ⬝ᵥ g).re := by
    have h1 : (0 : ℝ) < 1 + (B.card : ℝ) := by positivity
    nlinarith
  have hfg : star f ⬝ᵥ g = star f ⬝ᵥ f - ∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f := by
    rw [hg, dotProduct_sub, hYf, dotProduct_sum]
  rw [hfg, Complex.sub_re] at hpos
  linarith

end

end PositivityTheory.Rg.Cz
end

section
open Finset

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem eAt_applyC (p : Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I = if I p = a then f (Function.update I p c) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem tE_zero_apply (S : Finset Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) f I =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I := by
  simp [tE, lift, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply]

theorem sum4 {α β : Type} (s : Finset α) (t : Finset β) (F : Fin n → Fin n → α → β → ℂ) :
    ∑ a, ∑ c, ∑ p ∈ s, ∑ q ∈ t, F a c p q = ∑ p ∈ s, ∑ q ∈ t, ∑ a, ∑ c, F a c p q := by
  calc _ = ∑ a, ∑ p ∈ s, ∑ c, ∑ q ∈ t, F a c p q := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ c, ∑ q ∈ t, F a c p q := Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ q ∈ t, ∑ c, F a c p q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm

theorem pair_apply (p q : Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    ∑ a, ∑ c, (eAt p a c : Module.End ℂ (TV n ℂ Q)) ((eAt q c a : Module.End ℂ (TV n ℂ Q)) f) I =
      if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q) := by
  simp only [eAt_applyC]
  rw [Finset.sum_eq_single (I p)]
  · by_cases hpq : p = q
    · subst hpq
      simp [Function.update_idem, Finset.card_univ]
    · have hqp : q ≠ p := Ne.symm hpq
      simp only [if_true, Function.update_of_ne hqp, hpq, if_false]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      congr 1
      funext x
      by_cases hx : x = q
      · subst hx
        simp [Equiv.swap_apply_right]
      · by_cases hx' : x = p
        · subst hx'
          simp [Function.update_apply, hx, Equiv.swap_apply_left]
        · simp [Function.update_apply, hx, hx', Equiv.swap_apply_of_ne_of_ne hx' hx]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem tE_zero_eq_sum_eAt (S : Finset Q) (a c : Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) := by
  apply LinearMap.ext
  intro f
  funext I
  rw [tE_zero_apply]
  simp [LinearMap.sum_apply, Finset.sum_apply]

theorem cas_expand' (S : Finset Q) :
    (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ Q)) =
      ((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
        ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) := by
  simp_rw [tE_zero_eq_sum_eAt, Finset.sum_mul_sum]
  apply LinearMap.ext
  intro f
  funext I
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Module.End.one_apply]
  rw [sum4]
  simp_rw [pair_apply]
  have hpm : ∀ p q : Q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ Equiv.swap p q) := by
    intro p q
    simp [pm]
  simp_rw [hpm]
  have hsplit : ∀ p ∈ S, (∑ q ∈ S, if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q)) =
      (n : ℂ) * f I + ∑ q ∈ S.erase p, f (I ∘ Equiv.swap p q) := by
    intro p hp
    rw [← Finset.add_sum_erase S _ hp]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_neg (Finset.ne_of_mem_erase hq).symm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  ring

end

end PositivityTheory.Rg.Cz
end

section
open Finset

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

theorem count_rhs :
    (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) =
      ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) + 2 * (b p : ℕ) + 1 - n) := by
  rw [← Finset.sum_fiberwise S b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => ((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)]
  · rw [Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

theorem count_up (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => col q = col p ∧ b p < b q).card : ℝ) = n - 1 - (b p : ℕ) := by
  have hc : (S.filter fun q => col q = col p ∧ b p < b q).card = (Finset.Ioi (b p)).card := by
    apply Finset.card_bij (fun q _ => b q)
    · intro q hq
      simp only [Finset.mem_filter] at hq
      exact Finset.mem_Ioi.mpr hq.2.2
    · intro q₁ h₁ q₂ h₂ h
      simp only [Finset.mem_filter] at h₁ h₂
      exact hT.1 q₁ q₂ (h₁.2.1.trans h₂.2.1.symm) h
    · intro i hi
      rw [Finset.mem_Ioi] at hi
      obtain ⟨q, hq1, hq2⟩ := hT.2 p i hi
      refine ⟨q, ?_, hq2⟩
      simp only [Finset.mem_filter]
      refine ⟨(hS q p hq1).2 hp, hq1, ?_⟩
      rw [hq2]
      exact hi
  rw [hc, Fin.card_Ioi]
  have h : (b p : ℕ) + 1 ≤ n := (b p).isLt
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (b p : ℕ) ≤ n)]
  push_cast
  ring

theorem count_eqb (hT : IsTab col b) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => b q = b p).card : ℝ) =
      1 + ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]
  have h1 : (S.filter fun q => b q = b p).filter (fun q => col q = col p) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact hT.1 q p h3 h2
    · rintro rfl
      exact ⟨⟨hp, rfl⟩, rfl⟩
  have h2 : (S.filter fun q => b q = b p).filter (fun q => ¬ col q = col p) =
      S.filter (fun q => col q ≠ col p ∧ b q = b p) := by
    ext q
    simp only [Finset.mem_filter]
    tauto
  have h3 := Finset.card_filter_add_card_filter_not (s := S.filter fun q => b q = b p)
    (fun q => col q = col p)
  beta_reduce at h3
  rw [h1, h2, Finset.card_singleton] at h3
  rw [← h3]
  push_cast
  ring

theorem count_same (hT : IsTab col b) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) =
      2 * ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ b p < b q then (1 : ℝ) else 0) := by
  have hpt : ∀ p q : Q, (if col q = col p ∧ q ≠ p then (1 : ℝ) else 0) =
      (if col q = col p ∧ b p < b q then 1 else 0) + (if col p = col q ∧ b q < b p then 1 else 0) := by
    intro p q
    by_cases hc : col q = col p
    · by_cases hq : q = p
      · subst hq; simp
      · have hb : b q ≠ b p := fun hb => hq (hT.1 q p hc hb)
        rcases lt_or_gt_of_ne hb with h | h
        · simp [hc, hq, h, not_lt.mpr h.le]
        · simp [hc, hq, h, not_lt.mpr h.le]
    · have hc' : col p ≠ col q := fun h => hc h.symm
      simp [hc, hc']
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun p q => if col p = col q ∧ b q < b p then (1 : ℝ) else 0)]
  ring

end

end PositivityTheory.Rg.Cz
end

section
open Finset

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

private theorem isWH_coeff_one_polynomial (hT : IsTab col b) (N : ℝ) (c : C) (x : Q)
    (hx : ∃ y ∈ S, col y = c ∧ b y = b x) :
    ∑ y ∈ S.filter (fun y => col y = c), (if b y = b x then N else 0) = N := by
  obtain ⟨y, hyS, hyc, hyb⟩ := hx
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_filter]
  have e : (S.filter fun z => col z = c ∧ b z = b x) = {y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hzc, hzb⟩
      exact hT.1 z y (hzc.trans hyc.symm) (hzb.trans hyb.symm)
    · rintro rfl
      exact ⟨hyS, hyc, hyb⟩
  rw [e, Finset.card_singleton, one_smul]

private theorem sum_filter_col_le_sum_ite_of_bound (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S))
    (R : Q → Q → ℝ) (N : ℝ) (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N)
    (c d : C) (hcd : c ≠ d) :
    ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), R p q ≤
      ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d),
        (if b q = b p then N else 0) := by
  by_cases h : ∀ p ∈ S, col p = c → ∃ q ∈ S, col q = d ∧ b q = b p
  · refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [isWH_coeff_one_polynomial hT N d p (h p hp.1 hp.2)]
    exact hcross p hp.1 d (by rw [hp.2]; exact Ne.symm hcd)
  · push_neg at h
    obtain ⟨p0, hp0S, hp0c, hp0⟩ := h
    have h' : ∀ q ∈ S, col q = d → ∃ p ∈ S, col p = c ∧ b p = b q := by
      intro q hqS hqd
      rcases lt_trichotomy (b p0) (b q) with hl | he | hg
      · obtain ⟨p, hpc, hpb⟩ := hT.2 p0 (b q) hl
        exact ⟨p, (hS p p0 hpc).2 hp0S, hpc.trans hp0c, hpb⟩
      · exact absurd he.symm (hp0 q hqS hqd)
      · obtain ⟨q', hq'c, hq'b⟩ := hT.2 q (b p0) hg
        exact absurd hq'b (hp0 q' ((hS q' q hq'c).2 hqS) (hq'c.trans hqd))
    rw [Finset.sum_comm, Finset.sum_comm (s := S.filter (fun p => col p = c))]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_filter] at hq
    have e : ∑ p ∈ S.filter (fun p => col p = c), (if b q = b p then N else 0) = N :=
      (Finset.sum_congr rfl fun p _ => if_congr eq_comm rfl rfl).trans
        (isWH_coeff_one_polynomial hT N c q (h' q hq.1 hq.2))
    rw [e, Finset.sum_congr rfl fun p _ => hsymm p q]
    exact hcross q hq.1 c (by rw [hq.2]; exact hcd)

private theorem sum_sum_ite_col_ne_eq_sum_by_col (F : Q → Q → ℝ) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then F p q else 0) =
      ∑ c ∈ S.image col, ∑ d ∈ S.image col, (if d ≠ c then
        ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), F p q else 0) := by
  symm
  calc ∑ c ∈ S.image col, ∑ d ∈ S.image col, (if d ≠ c then
        ∑ p ∈ S.filter (fun p => col p = c), ∑ q ∈ S.filter (fun q => col q = d), F p q else 0)
      = ∑ c ∈ S.image col, ∑ d ∈ S.image col, ∑ p ∈ S.filter (fun p => col p = c),
          ∑ q ∈ S.filter (fun q => col q = d), (if col q ≠ col p then F p q else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        split_ifs with h
        · refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
          rw [Finset.mem_filter] at hp hq
          rw [if_pos (by rw [hp.2, hq.2]; exact h)]
        · symm
          refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
          rw [Finset.mem_filter] at hp hq
          rw [if_neg (by rw [hp.2, hq.2]; exact h)]
    _ = ∑ c ∈ S.image col, ∑ p ∈ S.filter (fun p => col p = c), ∑ d ∈ S.image col,
          ∑ q ∈ S.filter (fun q => col q = d), (if col q ≠ col p then F p q else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then F p q else 0) := by
        rw [Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem col hp)]
        refine Finset.sum_congr rfl fun p _ => ?_
        exact Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem col hq) _

theorem count_cross (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (R : Q → Q → ℝ) (N : ℝ)
    (hsymm : ∀ p q, R p q = R q p)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p then R p q else 0) ≤
      ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) := by
  rw [sum_sum_ite_col_ne_eq_sum_by_col (S := S) (col := col) R]
  have hR : ∀ p q, (if col q ≠ col p ∧ b q = b p then N else 0) =
      (if col q ≠ col p then (if b q = b p then N else 0) else 0) := by
    intro p q
    by_cases h1 : col q ≠ col p <;> by_cases h2 : b q = b p <;> simp [h1, h2]
  simp_rw [hR]
  have e2 := sum_sum_ite_col_ne_eq_sum_by_col (S := S) (col := col) (fun p q => if b q = b p then N else 0)
  beta_reduce at e2
  rw [e2]
  refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
  split_ifs with h
  · exact sum_filter_col_le_sum_ite_of_bound hT hS R N hsymm hcross c d (Ne.symm h)
  · exact le_rfl

theorem cas_count (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S))
    (R : Q → Q → ℝ) (N : ℝ) (hsymm : ∀ p q, R p q = R q p)
    (hsame : ∀ p q, col p = col q → p ≠ q → R p q = -N)
    (hcross : ∀ p ∈ S, ∀ c, c ≠ col p → ∑ q ∈ S.filter (fun q => col q = c), R p q ≤ N) :
    ((n * S.card : ℕ) : ℝ) * N + ∑ p ∈ S, ∑ q ∈ S.erase p, R p q ≤
      (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) * N := by
  rw [count_rhs, Finset.sum_mul]
  have hsplit : ∀ p, ∑ q ∈ S.erase p, R p q =
      (∑ q ∈ S, (if col q = col p ∧ q ≠ p then (1:ℝ) else 0)) * (-N) +
        ∑ q ∈ S, (if col q ≠ col p then R p q else 0) := by
    intro p
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    rw [← Finset.filter_ne' S p, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q = p
    · subst hq
      simp
    · by_cases hc : col q = col p
      · simp [hq, hc, hsame p q hc.symm (Ne.symm hq)]
      · simp [hq, hc]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, count_same hT]
  have hup : ∑ p ∈ S, ∑ q ∈ S, (if col q = col p ∧ b p < b q then (1:ℝ) else 0) =
      ∑ p ∈ S, ((n:ℝ) - 1 - (b p : ℕ)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_boole]
    exact count_up hT hS p hp
  have heq : ∑ p ∈ S, ∑ q ∈ S, (if col q ≠ col p ∧ b q = b p then N else 0) =
      ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) - 1) * N := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [count_eqb hT p hp, add_sub_cancel_left, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  have hc := count_cross hT hS R N hsymm hcross
  rw [heq] at hc
  rw [hup]
  have hcard : ((n * S.card : ℕ) : ℝ) = ∑ p ∈ S, (n : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hcard]
  have e3 : ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) + 2 * (b p : ℕ) + 1 - n) * N =
      (∑ p ∈ S, (n:ℝ)) * N + (2 * ∑ p ∈ S, ((n:ℝ) - 1 - (b p : ℕ))) * (-N) +
        ∑ p ∈ S, (((S.filter fun q => b q = b p).card : ℝ) - 1) * N := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e3]
  linarith

end

end PositivityTheory.Rg.Cz
end

section
open Matrix

namespace PositivityTheory.Rg.Cz

theorem casBound_holds : CasBound := by
  intro n Q _ _ C _ col b S hT hS f hf
  rw [cas_expand']
  have key : (star f ⬝ᵥ ((((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
      ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f)).re =
      ((n * S.card : ℕ) : ℝ) * (star f ⬝ᵥ f).re +
        ∑ p ∈ S, ∑ q ∈ S.erase p, (star f ⬝ᵥ pm (Equiv.swap p q) f).re := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
      dotProduct_add, dotProduct_smul, dotProduct_sum, Complex.add_re, Complex.re_sum, smul_eq_mul]
    simp
  rw [key]
  refine cas_count hT hS (fun p q => (star f ⬝ᵥ pm (Equiv.swap p q) f).re) _ ?_ ?_ ?_
  · intro p q
    simp only [Equiv.swap_comm]
  · intro p q hpq hne
    simp [hf p q hpq hne]
  · intro p _ c hc
    have h1 := re_swapSum_le' f (S.filter fun q => col q = c) p
      (by simp only [Finset.mem_filter, not_and]; exact fun _ h => hc h.symm)
      (by
        intro q hq q' hq' hne
        simp only [Finset.mem_filter] at hq hq'
        exact hf q q' (hq.2.trans hq'.2.symm) hne)
    simpa only [Complex.re_sum] using h1

end PositivityTheory.Rg.Cz
end
