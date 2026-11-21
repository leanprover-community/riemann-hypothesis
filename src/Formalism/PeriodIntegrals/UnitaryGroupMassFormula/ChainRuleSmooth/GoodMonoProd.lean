import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.Curves

section
open Matrix
open scoped ContDiff

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => (splits xs).map (fun p => (x :: p.1, p.2)) ++ (splits xs).map (fun p => (p.1, x :: p.2))

theorem mem_splits {α : Type*} : ∀ (l : List α) (p : List α × List α), p ∈ splits l →
    p.1.Sublist l ∧ p.2.Sublist l
  | [], p, h => by
      simp only [splits, List.mem_singleton] at h
      subst h
      exact ⟨List.Sublist.slnil, List.Sublist.slnil⟩
  | x :: xs, p, h => by
      simp only [splits, List.mem_append, List.mem_map] at h
      rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have := mem_splits xs q hq
        exact ⟨this.1.cons_cons x, this.2.cons x⟩
      · have := mem_splits xs q hq
        exact ⟨this.1.cons x, this.2.cons_cons x⟩

theorem norm_sum_map_le {α F : Type*} [SeminormedAddCommGroup F] (l : List α) (f : α → F) :
    ‖(l.map f).sum‖ ≤ (l.map (fun p => ‖f p‖)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

theorem mul_sum_map {α : Type*} (l : List α) (c : ℝ) (f : α → ℝ) :
    c * (l.map f).sum = (l.map (fun p => c * f p)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem sum_bound {α β : Type*} (l : List α) (S : Set β) (w : β → ℝ) (φ : α → β → ℝ)
    (h : ∀ p ∈ l, ∃ C, ∀ g ∈ S, φ p g ≤ C * w g) :
    ∃ C, ∀ g ∈ S, (l.map (fun p => φ p g)).sum ≤ C * w g := by
  induction l with
  | nil => exact ⟨0, fun g _ => by simp⟩
  | cons a l ih =>
    obtain ⟨C₁, h₁⟩ := h a (by simp)
    obtain ⟨C₂, h₂⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨C₁ + C₂, fun g hg => ?_⟩
    simp only [List.map_cons, List.sum_cons]
    have e1 := h₁ g hg
    have e2 := h₂ g hg
    nlinarith

theorem term_bound {N A Bc m n a b C₁ C₂ : ℝ} {D : ℕ} (hN : 1 ≤ N) (hB : 0 ≤ Bc) (hmn : m ≤ n)
    (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ C₁ * N ^ D) (hb : N ^ (A - Bc * m) * b ≤ C₂) :
    N ^ (A - D - Bc * n) * (a * b) ≤ max C₁ 0 * max C₂ 0 := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have ha' : a ≤ max C₁ 0 * N ^ (D : ℝ) := by
    rw [Real.rpow_natCast]
    exact ha.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN0.le _))
  have hx : N ^ (A - D - Bc * n) * N ^ (D : ℝ) = N ^ (A - Bc * m) * N ^ (-(Bc * (n - m))) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have h3 : N ^ (-(Bc * (n - m))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hE : 0 ≤ N ^ (A - D - Bc * n) := Real.rpow_nonneg hN0.le _
  have hP : 0 ≤ N ^ (A - Bc * m) * b := mul_nonneg (Real.rpow_nonneg hN0.le _) hb0
  calc N ^ (A - D - Bc * n) * (a * b)
      ≤ N ^ (A - D - Bc * n) * ((max C₁ 0 * N ^ (D : ℝ)) * b) := by
        apply mul_le_mul_of_nonneg_left _ hE
        exact mul_le_mul_of_nonneg_right ha' hb0
    _ = max C₁ 0 * ((N ^ (A - Bc * m) * b) * N ^ (-(Bc * (n - m)))) := by
        calc N ^ (A - D - Bc * n) * ((max C₁ 0 * N ^ (D : ℝ)) * b)
            = max C₁ 0 * ((N ^ (A - D - Bc * n) * N ^ (D : ℝ)) * b) := by ring
          _ = _ := by rw [hx]; ring
    _ ≤ max C₁ 0 * (max C₂ 0 * 1) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact mul_le_mul (hb.trans (le_max_left _ _)) h3 (Real.rpow_nonneg hN0.le _) (le_max_right _ _)
    _ = max C₁ 0 * max C₂ 0 := by ring

section sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def apO (ops : List (Bool × B.Mat k r)) (f : B.Mat k r → E) : B.Mat k r → E :=
  ops.foldl (fun f o => act o f) f

@[simp] theorem apO_nil (f : B.Mat k r → E) : apO [] f = f := rfl

@[simp] theorem apO_cons (o : Bool × B.Mat k r) (os : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    apO (o :: os) f = apO os (act o f) := rfl

theorem apO_append (l₁ l₂ : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    apO (l₁ ++ l₂) f = apO l₂ (apO l₁ f) := List.foldl_append

def LieW (ops : List (Bool × B.Mat k r)) : Prop := ∀ o ∈ ops, B.inLie k r o.2

theorem LieW.head {o : Bool × B.Mat k r} {os : List (Bool × B.Mat k r)} (h : LieW (o :: os)) :
    B.inLie k r o.2 := h o (by simp)

theorem LieW.tail {o : Bool × B.Mat k r} {os : List (Bool × B.Mat k r)} (h : LieW (o :: os)) :
    LieW os := fun o' h' => h o' (List.mem_cons_of_mem _ h')

theorem apO_local : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ f₁ f₂ : B.Mat k r → E,
    (∀ g ∈ B.GV k r, f₁ g = f₂ g) → ∀ g ∈ B.GV k r, apO ops f₁ g = apO ops f₂ g
  | [], _, _, _, h, g, hg => h g hg
  | o :: os, hl, f₁, f₂, h, g, hg =>
      apO_local os hl.tail _ _ (fun g' hg' => act_local o hl.head f₁ f₂ h g' hg') g hg

theorem apO_add : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ f₁ f₂ : B.Mat k r → E,
    B.CkOn (⊤ : ℕ∞) (B.GV k r) f₁ → B.CkOn (⊤ : ℕ∞) (B.GV k r) f₂ →
    ∀ g ∈ B.GV k r, apO ops (fun x => f₁ x + f₂ x) g = apO ops f₁ g + apO ops f₂ g
  | [], _, _, _, _, _, _, _ => rfl
  | o :: os, hl, f₁, f₂, h₁, h₂, g, hg => by
      simp only [apO_cons]
      rw [apO_local os hl.tail (act o (fun x => f₁ x + f₂ x)) (fun x => act o f₁ x + act o f₂ x)
        (fun g' hg' => act_add o hl.head f₁ f₂ h₁ h₂ g' hg') g hg]
      exact apO_add os hl.tail _ _ (act_ck f₁ h₁ o hl.head) (act_ck f₂ h₂ o hl.head) g hg

theorem leib : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ (Q : B.Mat k r → ℂ), ContDiff ℝ ∞ Q →
    ∀ (H : B.Mat k r → E), B.CkOn (⊤ : ℕ∞) (B.GV k r) H → ∀ g ∈ B.GV k r,
    apO ops (fun x => Q x • H x) g = ((splits ops).map (fun p => apO p.1 Q g • apO p.2 H g)).sum
  | [], _, Q, _, H, _, g, _ => by simp [splits]
  | o :: os, hl, Q, hQ, H, hH, g, hg => by
      simp only [apO_cons]
      rw [apO_local os hl.tail _ (fun x => act o Q x • H x + Q x • act o H x)
        (fun g' hg' => act_leib o hl.head Q hQ H hH g' hg') g hg]
      rw [apO_add os hl.tail _ _ (smul_ck _ (act_smooth_contDiff Q hQ o) H hH)
        (smul_ck Q hQ _ (act_ck H hH o hl.head)) g hg]
      rw [leib os hl.tail (act o Q) (act_smooth_contDiff Q hQ o) H hH g hg,
        leib os hl.tail Q hQ (act o H) (act_ck H hH o hl.head) g hg]
      simp [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def]

def opsW (u v : List (B.Mat k r)) : List (Bool × B.Mat k r) :=
  v.reverse.map (fun X => (false, X)) ++ u.reverse.map (fun X => (true, X))

theorem opsW_length (u v : List (B.Mat k r)) : (opsW u v).length = u.length + v.length := by
  simp [opsW, Nat.add_comm]

theorem apO_R (v : List (B.Mat k r)) (f : B.Mat k r → E) :
    apO (v.reverse.map (fun X => (false, X))) f = B.Rw v f := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    rw [List.reverse_cons, List.map_append, apO_append, ih]
    rfl

theorem dLR_eq (u v : List (B.Mat k r)) (f : B.Mat k r → E) : B.dLR u v f = apO (opsW u v) f := by
  rw [opsW, apO_append, apO_R]
  induction u with
  | nil => rfl
  | cons x u ih =>
    rw [List.reverse_cons, List.map_append, apO_append, ← ih]
    rfl

theorem sub_opsW (u v : List (B.Mat k r)) (l : List (Bool × B.Mat k r)) (h : l.Sublist (opsW u v)) :
    ∃ u' v', l = opsW u' v' ∧ (∀ X ∈ u', X ∈ u) ∧ (∀ X ∈ v', X ∈ v) := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 h
  obtain ⟨a, ha, rfl⟩ := List.sublist_map_iff.1 h₁
  obtain ⟨b, hb, rfl⟩ := List.sublist_map_iff.1 h₂
  refine ⟨b.reverse, a.reverse, by simp [opsW], fun X hX => ?_, fun X hX => ?_⟩
  · exact List.mem_reverse.1 (hb.subset (List.mem_reverse.1 hX))
  · exact List.mem_reverse.1 (ha.subset (List.mem_reverse.1 hX))

def Good (D : ℕ) (Q : B.Mat k r → ℂ) : Prop :=
  ContDiff ℝ ∞ Q ∧ ∀ ops : List (Bool × B.Mat k r), LieW ops →
    ∃ C, ∀ g ∈ B.GV k r, ‖apO ops Q g‖ ≤ C * B.gN g ^ D

theorem loss_bound_nonneg (r : ℕ) : 0 ≤ C2.B0 r := by
  unfold C2.B0; positivity

theorem main (A : ℝ) (D : ℕ) (Q : B.Mat k r → ℂ) (hQ : Good D Q) (F : B.Mat k r → E)
    (hF : C2.CCsc k r A F) : C2.CCsc k r (A - D) (fun g => Q g • F g) := by
  refine ⟨smul_ck Q hQ.1 F hF.1, fun u v hu hv => ?_⟩
  have hl : LieW (opsW u v) := by
    intro o ho
    simp only [opsW, List.mem_append, List.mem_map, List.mem_reverse] at ho
    rcases ho with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hv X hX).1
    · exact (hu X hX).1
  have hterm : ∀ p ∈ splits (opsW u v), ∃ C, ∀ g ∈ B.GV k r,
      B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖apO p.1 Q g • apO p.2 F g‖ ≤
        C * (fun _ => (1 : ℝ)) g := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_splits _ p hp
    obtain ⟨C₁, hC₁⟩ := hQ.2 p.1 (fun o ho => hl o (h1.subset ho))
    obtain ⟨u', v', hp2, hu', hv'⟩ := sub_opsW u v p.2 h2
    obtain ⟨C₂, hC₂⟩ := hF.2 u' v' (fun X hX => hu X (hu' X hX)) (fun X hX => hv X (hv' X hX))
    refine ⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩
    have hlen : ((u'.length : ℝ) + v'.length) ≤ (u.length : ℝ) + v.length := by
      have := h2.length_le
      rw [hp2, opsW_length, opsW_length] at this
      exact_mod_cast this
    rw [norm_smul, mul_one]
    have hb := hC₂ g hg
    rw [dLR_eq, ← hp2] at hb
    exact term_bound (one_le_gN g hg) (loss_bound_nonneg r) hlen (norm_nonneg _) (norm_nonneg _) (hC₁ g hg) hb
  obtain ⟨C, hC⟩ := sum_bound _ (B.GV k r) (fun _ => (1 : ℝ))
    (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) => B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) *
      ‖apO p.1 Q g • apO p.2 F g‖) hterm
  refine ⟨C, fun g hg => ?_⟩
  rw [dLR_eq, leib (opsW u v) hl Q hQ.1 F hF.1 g hg]
  have hN := Real.rpow_nonneg (gN_pos g hg).le (A - D - C2.B0 r * ((u.length : ℝ) + v.length))
  calc _ ≤ B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) *
          ((splits (opsW u v)).map (fun p => ‖apO p.1 Q g • apO p.2 F g‖)).sum :=
        mul_le_mul_of_nonneg_left (norm_sum_map_le _ _) hN
    _ = ((splits (opsW u v)).map (fun p => B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) *
          ‖apO p.1 Q g • apO p.2 F g‖)).sum := mul_sum_map _ _ _
    _ ≤ C * 1 := hC g hg
    _ = C := mul_one C

end sup

end CCRuleCW
end
end

section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

section sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem good_congr {D : ℕ} {Q₁ Q₂ : B.Mat k r → ℂ} (h : ∀ g, Q₁ g = Q₂ g) (h₁ : Good D Q₁) : Good D Q₂ := by
  have : Q₁ = Q₂ := funext h
  exact this ▸ h₁

theorem good_mono {a b : ℕ} (hab : a ≤ b) (Q : B.Mat k r → ℂ) (h : Good a Q) : Good b Q := by
  refine ⟨h.1, fun ops hl => ?_⟩
  obtain ⟨C, hC⟩ := h.2 ops hl
  refine ⟨max C 0, fun g hg => (hC g hg).trans ?_⟩
  have h1 := one_le_gN g hg
  calc C * B.gN g ^ a ≤ max C 0 * B.gN g ^ a :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
    _ ≤ max C 0 * B.gN g ^ b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hab) (le_max_right _ _)

theorem good_add {D : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good D Q₁) (h₂ : Good D Q₂) :
    Good D (fun g => Q₁ g + Q₂ g) := by
  refine ⟨h₁.1.add h₂.1, fun ops hl => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.2 ops hl
  obtain ⟨C₂, hC₂⟩ := h₂.2 ops hl
  refine ⟨C₁ + C₂, fun g hg => ?_⟩
  rw [apO_add ops hl Q₁ Q₂ (smooth_ck Q₁ h₁.1) (smooth_ck Q₂ h₂.1) g hg]
  have e1 := hC₁ g hg
  have e2 := hC₂ g hg
  calc _ ≤ ‖apO ops Q₁ g‖ + ‖apO ops Q₂ g‖ := norm_add_le _ _
    _ ≤ C₁ * B.gN g ^ D + C₂ * B.gN g ^ D := add_le_add e1 e2
    _ = (C₁ + C₂) * B.gN g ^ D := by ring

theorem good_mul {a b : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good a Q₁) (h₂ : Good b Q₂) :
    Good (a + b) (fun g => Q₁ g * Q₂ g) := by
  refine ⟨h₁.1.mul h₂.1, fun ops hl => ?_⟩
  have hterm : ∀ p ∈ splits ops, ∃ C, ∀ g ∈ B.GV k r,
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖ ≤ C * B.gN g ^ (a + b) := by
    intro p hp
    obtain ⟨s1, s2⟩ := mem_splits _ p hp
    obtain ⟨C₁, hC₁⟩ := h₁.2 p.1 (fun o ho => hl o (s1.subset ho))
    obtain ⟨C₂, hC₂⟩ := h₂.2 p.2 (fun o ho => hl o (s2.subset ho))
    refine ⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩
    rw [norm_smul, pow_add]
    have hN : 0 ≤ B.gN g := (gN_pos g hg).le
    have e1 : ‖apO p.1 Q₁ g‖ ≤ max C₁ 0 * B.gN g ^ a :=
      (hC₁ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    have e2 : ‖apO p.2 Q₂ g‖ ≤ max C₂ 0 * B.gN g ^ b :=
      (hC₂ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    calc _ ≤ (max C₁ 0 * B.gN g ^ a) * (max C₂ 0 * B.gN g ^ b) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (pow_nonneg hN _))
      _ = _ := by ring
  obtain ⟨C, hC⟩ := sum_bound _ (B.GV k r) (fun g => B.gN g ^ (a + b))
    (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) =>
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖) hterm
  refine ⟨C, fun g hg => ?_⟩
  have e : (fun g => Q₁ g * Q₂ g) = (fun g => Q₁ g • Q₂ g) := rfl
  rw [e, leib ops hl Q₁ h₁.1 Q₂ (smooth_ck Q₂ h₂.1) g hg]
  exact (norm_sum_map_le _ _).trans (hC g hg)

theorem apO_const : ∀ (ops : List (Bool × B.Mat k r)) (c : ℂ),
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ apO ops (fun _ : B.Mat k r => c) = fun _ => c'
  | [], c => ⟨c, le_rfl, rfl⟩
  | o :: os, c => by
    have h0 : act o (fun _ : B.Mat k r => c) = fun _ => (0 : ℂ) := by
      funext g
      rw [act_eq]
      simp
    obtain ⟨c', h1, h2⟩ := apO_const os 0
    refine ⟨c', h1.trans (by simp), ?_⟩
    simp only [apO_cons, h0, h2]

theorem good_const (c : ℂ) : Good 0 (fun _ : B.Mat k r => c) := by
  refine ⟨contDiff_const, fun ops _ => ?_⟩
  obtain ⟨c', h1, h2⟩ := apO_const ops c
  exact ⟨‖c‖, fun g _ => by rw [h2, pow_zero, mul_one]; exact h1⟩

def dirL (o : Bool × B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := dir o
      map_add' := fun a b => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.add_mul a b X
        · show -(X * (a + b)) = -(X * a) + -(X * b)
          rw [Matrix.mul_add, neg_add]
      map_smul' := fun c a => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.smul_mul c a X
        · show -(X * (c • a)) = c • -(X * a)
          rw [Matrix.mul_smul, smul_neg] }

theorem apO_clm : ∀ (ops : List (Bool × B.Mat k r)) (ℓ : B.Mat k r →L[ℝ] ℂ),
    ∃ ℓ' : B.Mat k r →L[ℝ] ℂ, apO ops ⇑ℓ = ⇑ℓ'
  | [], ℓ => ⟨ℓ, rfl⟩
  | o :: os, ℓ => by
    have h : act o ⇑ℓ = ⇑(ℓ.comp (dirL o)) := by
      funext g
      rw [act_eq]
      exact (ℓ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (curve_hasDerivAt o g) (curve_zero o g).symm).deriv
    obtain ⟨ℓ', h'⟩ := apO_clm os (ℓ.comp (dirL o))
    exact ⟨ℓ', by simp only [apO_cons, h, h']⟩

theorem sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g :=
  (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun i j => entry_le_gN g i j

theorem good_clm (ℓ : B.Mat k r →L[ℝ] ℂ) : Good 1 ⇑ℓ := by
  refine ⟨ℓ.contDiff, fun ops _ => ?_⟩
  obtain ⟨ℓ', h⟩ := apO_clm ops ℓ
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : B.Mat k r, ‖ℓ' x‖ ≤ M * ‖x‖ := by
    exact ℓ'.bound
  refine ⟨M, fun g _ => ?_⟩
  rw [h, pow_one]
  exact (hM g).trans (mul_le_mul_of_nonneg_left (sup_le_gN g) hM0.le)

def coordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def ccoordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => conj (g p.1 p.2)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp [Matrix.smul_apply, Complex.real_smul] }

def xv (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun p => g p.1 p.2) (fun p => conj (g p.1 p.2))

theorem good_var (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    Good 1 (fun g : B.Mat k r => xv g i) := by
  rcases i with p | p
  · exact good_congr (fun g => rfl) (good_clm (coordL p))
  · exact good_congr (fun g => rfl) (good_clm (ccoordL p))

theorem good_pow (Q : B.Mat k r → ℂ) (h : Good 1 Q) : ∀ m : ℕ, Good m (fun g => Q g ^ m)
  | 0 => good_congr (fun g => (pow_zero (Q g)).symm) (good_const 1)
  | m + 1 => good_congr (fun g => (pow_succ (Q g) m).symm) (good_mul _ _ (good_pow Q h m) h)

theorem good_mono_prod (d : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℕ)
    (s : Finset ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))) :
    Good (∑ i ∈ s, d i) (fun g : B.Mat k r => ∏ i ∈ s, xv g i ^ d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_const (k := k) (r := r) 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact good_congr (fun g => by rw [Finset.prod_insert ha])
      (good_mul _ _ (good_pow _ (good_var a) (d a)) ih)

theorem good_poly (q : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)
    (D : ℕ) (hq : q.totalDegree ≤ D) :
    Good D (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) := by
  have e : (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) =
      ∑ d ∈ q.support, fun g : B.Mat k r => q.coeff d * ∏ i ∈ d.support, xv g i ^ d i := by
    funext g
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ (Good D) (fun a b ha hb => good_add a b ha hb)
    (good_mono (Nat.zero_le D) _ (good_const 0)) ?_
  intro d hd
  have hdeg : (∑ i ∈ d.support, d i) ≤ D := (MvPolynomial.le_totalDegree hd).trans hq
  exact good_mono (by simpa using hdeg) _ (good_mul _ _ (good_const (q.coeff d)) (good_mono_prod d d.support))


end sup

end CCRuleCW
end
end
