import Mathlib
import Lemmata.MiscLemmasC.Imports

section
set_option linter.style.haveILetI false

noncomputable section

open Finset

namespace Formalism.IndefR.Fin.Four

variable {W : Type*} [AddCommGroup W]

def smulSub (k : ℕ) (H : AddSubgroup W) : AddSubgroup W := H.map (nsmulAddMonoidHom k)

theorem mem_smulSub {k : ℕ} {H : AddSubgroup W} {x : W} : x ∈ smulSub k H ↔ ∃ u ∈ H, k • u = x := by
  simp [smulSub, AddSubgroup.mem_map]

theorem smulSub_mul_le (k j : ℕ) (H : AddSubgroup W) : smulSub (k * j) H ≤ smulSub k H := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_smulSub.1 hx
  exact mem_smulSub.2 ⟨j • u, H.nsmul_mem hu j, by rw [smul_smul]⟩

abbrev Qt (k : ℕ) (H : AddSubgroup W) : Type _ := ↥H ⧸ (smulSub k H).addSubgroupOf H

def IsInv (k : ℕ) (H : AddSubgroup W) (g : W → ℂ) : Prop := ∀ t ∈ H, ∀ u ∈ H, g (t + k • u) = g t

def avg (k : ℕ) (H : AddSubgroup W) (g : W → ℂ) : ℂ :=
  (Nat.card (Qt k H) : ℂ)⁻¹ * ∑ᶠ q : Qt k H, g ((q.out : H) : W)

theorem out_mk (k : ℕ) (H : AddSubgroup W) (x : H) :
    ∃ u ∈ H, ((((QuotientAddGroup.mk x : Qt k H)).out : H) : W) + k • u = (x : W) := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : Qt k H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h
  refine ⟨u, hu, ?_⟩
  rw [hux]
  push_cast
  abel

theorem IsInv.mk_eq {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) {x y : H}
    (hxy : (QuotientAddGroup.mk x : Qt k H) = QuotientAddGroup.mk y) : g x = g y := by
  have h := QuotientAddGroup.eq.1 hxy
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h
  have : (y : W) = x + k • u := by rw [hux]; push_cast; abel
  rw [this, hg _ x.2 u hu]

theorem IsInv.out_mk {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (x : H) :
    g (((QuotientAddGroup.mk x : Qt k H).out : H) : W) = g x :=
  hg.mk_eq (QuotientAddGroup.out_eq' _)

theorem IsInv.mul {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (j : ℕ) : IsInv (k * j) H g := by
  intro t ht u hu
  rw [← smul_smul]
  exact hg t ht _ (H.nsmul_mem hu j)

theorem avg_eq_sum (k : ℕ) (H : AddSubgroup W) [Fintype (Qt k H)] (g : W → ℂ) :
    avg k H g = (Fintype.card (Qt k H) : ℂ)⁻¹ * ∑ q : Qt k H, g ((q.out : H) : W) := by
  rw [avg, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]

theorem avg_comp_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by
  first | exact Bl.SecondBlockLemmaD.goal1 .. | (apply Bl.SecondBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaD.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaD.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaD.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaD.goal1 <;> first | assumption | infer_instance)

theorem avg_mul (k j : ℕ) (H : AddSubgroup W) [Finite (Qt k H)] [Finite (Qt (k * j) H)] (g : W → ℂ)
    (hg : IsInv k H g) : avg (k * j) H g = avg k H g := by
  classical
  let _ := Fintype.ofFinite (Qt k H)
  let _ := Fintype.ofFinite (Qt (k * j) H)
  let π : Qt (k * j) H →+ Qt k H :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id H) (by
      intro x hx
      simp only [AddSubgroup.mem_comap, AddMonoidHom.id_apply, AddSubgroup.mem_addSubgroupOf] at hx ⊢
      exact smulSub_mul_le k j H hx)
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x => exact ⟨QuotientAddGroup.mk x, rfl⟩
  have key : ∀ q : Qt (k * j) H, g ((q.out : H) : W) = g (((π q).out : H) : W) := by
    intro q
    have : π q = QuotientAddGroup.mk q.out := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [this, hg.out_mk]
  rw [avg_eq_sum, avg_eq_sum]
  simp_rw [key]
  exact avg_comp_surj π hπ (fun b => g ((b.out : H) : W))

open Classical in

def integ (H : AddSubgroup W) (g : W → ℂ) : ℂ :=
  if h : ∃ k, 0 < k ∧ IsInv k H g then avg h.choose H g else 0

section Integ

variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin

theorem integ_eq {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) : integ H g = avg k H g := by
  have h : ∃ k, 0 < k ∧ IsInv k H g := ⟨k, hk, hg⟩
  rw [integ, dif_pos h]
  obtain ⟨hk0, hg0⟩ := h.choose_spec
  haveI := hfin _ hk0
  haveI := hfin _ hk
  haveI := hfin _ (Nat.mul_pos hk0 hk)
  haveI := hfin _ (Nat.mul_pos hk hk0)
  rw [← avg_mul h.choose k H g hg0, ← avg_mul k h.choose H g hg, Nat.mul_comm]

omit hfin in
theorem IsInv.congr {k : ℕ} {g g' : W → ℂ} (hg : IsInv k H g) (h : ∀ t ∈ H, g t = g' t) : IsInv k H g' := by
  intro t ht u hu
  rw [← h _ ht, ← h _ (H.add_mem ht (H.nsmul_mem hu k)), hg t ht u hu]

omit hfin in
theorem avg_congr (k : ℕ) {g g' : W → ℂ} (h : ∀ t ∈ H, g t = g' t) : avg k H g = avg k H g' := by
  rw [avg, avg]
  congr 1
  exact finsum_congr fun q => h _ (q.out : H).2

theorem integ_congr {g g' : W → ℂ} (h : ∀ t ∈ H, g t = g' t) : integ H g = integ H g' := by
  by_cases hg : ∃ k, 0 < k ∧ IsInv k H g
  · obtain ⟨k, hk, hgk⟩ := hg
    rw [integ_eq hfin hk hgk, integ_eq hfin hk (hgk.congr h), avg_congr k h]
  · have hg' : ¬ ∃ k, 0 < k ∧ IsInv k H g' := by
      rintro ⟨k, hk, hgk⟩
      exact hg ⟨k, hk, hgk.congr fun t ht => (h t ht).symm⟩
    rw [integ, dif_neg hg, integ, dif_neg hg']

omit hfin in
theorem IsInv.add {k k' : ℕ} {g g' : W → ℂ} (hg : IsInv k H g) (hg' : IsInv k' H g') :
    IsInv (k * k') H (fun t => g t + g' t) := by
  have h1 := hg.mul k'
  have h2 := hg'.mul k
  rw [Nat.mul_comm] at h2
  intro t ht u hu
  simp only [h1 t ht u hu, h2 t ht u hu]

omit hfin in
theorem IsInv.cmul {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) (c : ℂ) : IsInv k H (fun t => c * g t) := by
  intro t ht u hu
  simp only [hg t ht u hu]

theorem integ_cmul {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) (c : ℂ) :
    integ H (fun t => c * g t) = c * integ H g := by
  classical
  rw [integ_eq hfin hk (hg.cmul c), integ_eq hfin hk hg]
  haveI := hfin _ hk
  letI := Fintype.ofFinite (Qt k H)
  rw [avg_eq_sum, avg_eq_sum, ← Finset.mul_sum]
  ring

omit hfin in
theorem IsInv.shift {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    IsInv k H (fun t => g (t + v)) := by
  intro t ht u hu
  simp only
  rw [add_right_comm, hg _ (H.add_mem ht hv) u hu]

theorem integ_shift {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    integ H (fun t => g (t + v)) = integ H g := by
  classical
  rw [integ_eq hfin hk (hg.shift hv), integ_eq hfin hk hg]
  haveI := hfin _ hk
  letI := Fintype.ofFinite (Qt k H)
  rw [avg_eq_sum, avg_eq_sum]
  congr 1
  let m : Qt k H := QuotientAddGroup.mk (⟨v, hv⟩ : H)
  have key : ∀ q : Qt k H, g (((q.out : H) : W) + v) = g ((((q + m).out : H) : W)) := by
    intro q
    have h1 : q + m = QuotientAddGroup.mk (q.out + ⟨v, hv⟩) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [h1, hg.out_mk]
    rfl
  simp_rw [key]
  exact Fintype.sum_equiv (Equiv.addRight m) _ _ (fun q => rfl)

theorem integ_one : integ H (fun _ => (1 : ℂ)) = 1 := by
  classical
  have hinv : IsInv 1 H (fun _ => (1 : ℂ)) := fun _ _ _ _ => rfl
  rw [integ_eq hfin Nat.one_pos hinv]
  haveI := hfin _ Nat.one_pos
  letI := Fintype.ofFinite (Qt 1 H)
  rw [avg_eq_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : (Fintype.card (Qt 1 H) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact inv_mul_cancel₀ this

theorem integ_twist {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) {ζ : ℂ}
    (hζ : ζ ≠ 1) (htw : ∀ t ∈ H, g (t + v) = ζ * g t) : integ H g = 0 := by
  have h1 := integ_shift hfin hk hg hv
  rw [integ_congr hfin htw, integ_cmul hfin hk hg] at h1
  have : (ζ - 1) * integ H g = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hζ
  · exact h

theorem integ_cmul' (g : W → ℂ) (c : ℂ) : integ H (fun t => c * g t) = c * integ H g := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    have h0 : IsInv 1 H (fun _ : W => (0 : ℂ)) := fun _ _ _ _ => rfl
    rw [integ_eq hfin Nat.one_pos h0]
    simp [avg]
  by_cases hg : ∃ k, 0 < k ∧ IsInv k H g
  · obtain ⟨k, hk, hgk⟩ := hg
    exact integ_cmul hfin hk hgk c
  · have hn : ¬ ∃ k, 0 < k ∧ IsInv k H (fun t => c * g t) := by
      rintro ⟨k, hk, hgk⟩
      refine hg ⟨k, hk, ?_⟩
      refine (hgk.cmul c⁻¹).congr fun t _ => ?_
      simp [hc]
    rw [integ, dif_neg hn, integ, dif_neg hg, mul_zero]

theorem integ_zero_of {g : W → ℂ} (h : ∀ t ∈ H, g t = 0) : integ H g = 0 := by
  have h1 : integ H g = integ H (fun t => (0 : ℂ) * (fun _ => (1 : ℂ)) t) :=
    integ_congr hfin fun t ht => by simp [h t ht]
  rw [h1, integ_cmul' hfin, zero_mul]

end Integ

end Formalism.IndefR.Fin.Four

end
end

section
set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

def IsSB (L X : AddSubgroup W) (Φ : W → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → t ∈ X) ∧ ∃ k : ℕ, 0 < k ∧ (∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → k • t ∈ L

section Defs

variable (ρ : W → Module.End ℂ V) (χ : W → W → ℂ) (L X Y : AddSubgroup W) (f₀ : V)

def coef (Φ : W → ℂ) (a y : W) : ℂ := integ (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)

def term (Φ : W → ℂ) (a y : W) : V := coef χ L X Φ a y • ρ (-a) (ρ y f₀)

abbrev QX : Type _ := W ⧸ (L ⊓ X)

abbrev QY : Type _ := W ⧸ (L ⊓ Y)

open Classical in

def tfun (Φ : W → ℂ) : V :=
  ∑ᶠ q : QX L X × QY L Y, if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0

end Defs

section Chi

variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)

include hχl hχ0 in
theorem chi_zero_left (y : W) : χ 0 y = 1 := by
  have h := hχl 0 0 y
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 0 y) (by rw [mul_one, ← h])

include hχr hχ0 in
theorem chi_zero_right (t : W) : χ t 0 = 1 := by
  have h := hχr t 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 t 0) (by rw [mul_one, ← h])

include hχl hχ0 in
theorem chi_neg_left (t y : W) : χ (-t) y = (χ t y)⁻¹ := by
  have h : χ t y * χ (-t) y = 1 := by
    rw [← hχl, add_neg_cancel, chi_zero_left hχl hχ0]
  exact eq_inv_of_mul_eq_one_right h

include hχl hχ0 in
theorem chi_nsmul_left (k : ℕ) (t y : W) : χ (k • t) y = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_left hχl hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]

include hχr hχ0 in
theorem chi_nsmul_right (k : ℕ) (t y : W) : χ t (k • y) = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_right hχr hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]

end Chi

section Rep

variable {L X Y : AddSubgroup W}

theorem QX_out (a : W) : ∃ l ∈ L ⊓ X, (QuotientAddGroup.mk a : QX L X).out = a + l := by
  refine ⟨-a + (QuotientAddGroup.mk a : QX L X).out, ?_, (add_neg_cancel_left a _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk a : QX L X).out : QX L X) = QuotientAddGroup.mk a :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm

theorem QY_out (y : W) : ∃ μ ∈ L ⊓ Y, (QuotientAddGroup.mk y : QY L Y).out = y + μ := by
  refine ⟨-y + (QuotientAddGroup.mk y : QY L Y).out, ?_, (add_neg_cancel_left y _).symm⟩
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk y : QY L Y).out : QY L Y) = QuotientAddGroup.mk y :=
    QuotientAddGroup.out_eq' _
  exact QuotientAddGroup.eq.mp h.symm

end Rep

section Coef

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y) (hχ0 : ∀ t y, χ t y ≠ 0)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X)))

include hχl hχ0 hfinX in
theorem coef_add_left (Φ : W → ℂ) (a y : W) {l : W} (hl : l ∈ L ⊓ X) :
    coef χ L X Φ (a + l) y = χ l y * coef χ L X Φ a y := by
  have hc := hχ0 l y
  have hH : ∀ t, Φ (a + l + t) * (χ t y)⁻¹ = χ l y * (Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
    intro t
    have e : (χ t y)⁻¹ = χ l y * (χ (t + l) y)⁻¹ := by
      rw [hχl, mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]
    rw [e, add_comm t l, ← add_assoc]
    ring
  have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) ↔
      IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
    intro k
    unfold IsInv
    simp only [hH]
    constructor
    · intro h t ht u hu
      have := h (t - l) (sub_mem ht hl) u hu
      rw [sub_add_cancel, show t - l + k • u + l = t + k • u by abel] at this
      exact mul_left_cancel₀ hc this
    · intro h t ht u hu
      rw [show t + k • u + l = (t + l) + k • u by abel, h (t + l) (add_mem ht hl) u hu]
  unfold coef
  by_cases h0 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)
  · obtain ⟨k, hk, hinv⟩ := h0
    have hinv1 := (hiff k).mpr hinv
    have hinvs : IsInv k (L ⊓ X) (fun t => Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
      intro t ht u hu
      beta_reduce
      rw [show t + k • u + l = (t + l) + k • u by abel]
      exact hinv (t + l) (add_mem ht hl) u hu
    rw [integ_eq hfinX hk hinv1, ← integ_shift hfinX hk hinv hl, integ_eq hfinX hk hinvs]
    unfold avg
    haveI := hfinX k hk
    simp only [hH]
    rw [← mul_finsum]
    ring
  · have h1 : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) :=
      fun ⟨k, hk, hi⟩ => h0 ⟨k, hk, (hiff k).mp hi⟩
    unfold integ
    rw [dif_neg h1, dif_neg h0, mul_zero]

include hfinX in
theorem coef_add_right (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (Φ : W → ℂ) (a y : W) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    coef χ L X Φ a (y + μ) = coef χ L X Φ a y := by
  unfold coef
  apply integ_congr hfinX
  intro t ht
  rw [hχr, hLL t ht μ hμ, mul_one]

include hfinX in
theorem coef_eq_zero (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) {a : W} (ha : a ∉ X) (y : W) :
    coef χ L X Φ a y = 0 := by
  have h0 : ∀ t ∈ L ⊓ X, Φ (a + t) * (χ t y)⁻¹ = (fun _ : W => (0 : ℂ)) t := by
    intro t ht
    have hz : Φ (a + t) = 0 := by
      by_contra hne
      exact ha (by simpa using X.sub_mem (hΦ _ hne) (AddSubgroup.mem_inf.mp ht).2)
    simp [hz]
  unfold coef
  rw [integ_congr hfinX h0]
  unfold integ
  split_ifs with h
  · simp [avg]
  · rfl

include hχl hχ0 hfinX in
theorem term_add_left (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x)) (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀)
    (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) (a : W) {y : W} (hy : y ∈ Y) {l : W} (hl : l ∈ L ⊓ X) :
    term ρ χ L X f₀ Φ (a + l) y = term ρ χ L X f₀ Φ a y := by
  by_cases ha : a ∈ X
  · have hl' := AddSubgroup.mem_inf.mp hl
    have hnl : -l ∈ L ⊓ X := neg_mem hl
    have key : ρ (-l) (ρ y f₀) = (χ l y)⁻¹ • ρ y f₀ := by
      have h1 := congrArg (fun T => T f₀) (hXY (-l) (neg_mem hl'.2) y hy)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1
      rw [h1, hfX (-l) hnl, chi_neg_left hχl hχ0]
    unfold term
    rw [coef_add_left hχl hχ0 hfinX Φ a y hl, neg_add, hX (-a) (neg_mem ha) (-l) (neg_mem hl'.2),
      Module.End.mul_apply, key, map_smul, smul_smul, mul_comm (χ l y), mul_assoc, mul_inv_cancel₀ (hχ0 l y), mul_one]
  · have hal : a + l ∉ X := fun h => ha (by simpa using X.sub_mem h (AddSubgroup.mem_inf.mp hl).2)
    unfold term
    rw [coef_eq_zero hfinX Φ hΦ ha, coef_eq_zero hfinX Φ hΦ hal, zero_smul, zero_smul]

include hfinX in
theorem term_add_right (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
    (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀) (Φ : W → ℂ) (a : W) {y : W} (hy : y ∈ Y) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    term ρ χ L X f₀ Φ a (y + μ) = term ρ χ L X f₀ Φ a y := by
  unfold term
  rw [coef_add_right hfinX hχr hLL Φ a y hμ, hY y hy μ (AddSubgroup.mem_inf.mp hμ).2, Module.End.mul_apply,
    hfY μ hμ]

end Coef

end Formalism.IndefR.Fin.Four

end
end

section
set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

section SB

variable {L X : AddSubgroup W}

theorem isSB_zero : IsSB L X (0 : W → ℂ) :=
  ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ => rfl, fun t h => absurd rfl h⟩

theorem IsSB.add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') : IsSB L X (Φ + Φ') := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨hs', k', hk', hi', hl'⟩ := h'
  have hor : ∀ t, (Φ + Φ') t ≠ 0 → Φ t ≠ 0 ∨ Φ' t ≠ 0 := by
    intro t ht
    by_contra hc
    push_neg at hc
    apply ht
    simp [hc.1, hc.2]
  refine ⟨fun t ht => (hor t ht).elim (hs t) (hs' t), k * k', Nat.mul_pos hk hk', fun u hu t => ?_,
    fun t ht => ?_⟩
  · have h1 : (k * k') • u = k • (k' • u) := (smul_smul k k' u).symm
    have h2 : (k * k') • u = k' • (k • u) := by rw [mul_comm]; exact (smul_smul k' k u).symm
    simp only [Pi.add_apply]
    congr 1
    · rw [h1]; exact hi _ ((L ⊓ X).nsmul_mem hu k') t
    · rw [h2]; exact hi' _ ((L ⊓ X).nsmul_mem hu k) t
  · rcases hor t ht with h0 | h0
    · rw [mul_comm, ← smul_smul]; exact L.nsmul_mem (hl t h0) k'
    · rw [← smul_smul]; exact L.nsmul_mem (hl' t h0) k

theorem IsSB.smul {Φ : W → ℂ} (h : IsSB L X Φ) (c : ℂ) : IsSB L X (c • Φ) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by simp [h0])
  exact ⟨fun t ht => hs t (hne t ht), k, hk, fun u hu t => by simp [hi u hu t],
    fun t ht => hl t (hne t ht)⟩

theorem IsSB.trans (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) {Φ : W → ℂ} (h : IsSB L X Φ) {x : W}
    (hx : x ∈ X) : IsSB L X (fun t => Φ (t + x)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k2, hk2, hx2⟩ := hoX x hx
  refine ⟨fun t ht => ?_, k * k2, Nat.mul_pos hk hk2, fun u hu t => ?_, fun t ht => ?_⟩
  · have h1 := hs _ ht
    simpa using X.sub_mem h1 hx
  · show Φ (t + (k * k2) • u + x) = Φ (t + x)
    rw [← smul_smul, add_right_comm]
    exact hi _ ((L ⊓ X).nsmul_mem hu k2) _
  · have h1 := hl _ ht
    have h2 : (k * k2) • t = k2 • (k • (t + x)) - k • (k2 • x) := by
      simp only [smul_add, smul_smul]
      rw [mul_comm k2 k]
      abel
    rw [h2]
    exact L.sub_mem (L.nsmul_mem h1 k2) (L.nsmul_mem hx2 k)

theorem IsSB.modul {Y : AddSubgroup W} {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
    {Φ : W → ℂ} (h : IsSB L X Φ) {y : W} (hy : y ∈ Y) : IsSB L X (fun t => χ t y * Φ t) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k3, hk3, hy3⟩ := hoY y hy
  have h0 : ∀ b, χ 0 b = 1 := by
    intro b
    have h1 := hχl 0 0 b
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
  have h0' : ∀ a, χ a 0 = 1 := by
    intro a
    have h1 := hχr a 0 0
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
  have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨fun t ht => hs t (fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])),
    k * k3, Nat.mul_pos hk hk3, fun u hu t => ?_, fun t ht => ?_⟩
  · show χ (t + (k * k3) • u) y * Φ (t + (k * k3) • u) = χ t y * Φ t
    have hΦ : Φ (t + (k * k3) • u) = Φ t := by
      rw [← smul_smul]; exact hi _ ((L ⊓ X).nsmul_mem hu k3) t
    have hχu : χ ((k * k3) • u) y = 1 := by
      rw [hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]
    rw [hΦ, hχl, hχu, mul_one]
  · have hΦt : Φ t ≠ 0 := fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])
    rw [mul_comm, ← smul_smul]
    exact L.nsmul_mem (hl t hΦt) k3

open Classical in
theorem isSB_ind : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩
  · by_contra h
    apply ht
    simp [h]
  · simp only [one_smul, L.add_mem_cancel_right hu.1, X.add_mem_cancel_right hu.2]
  · rw [one_smul]
    by_contra h
    apply ht
    simp [h]

theorem finite_nsmul_out (H : AddSubgroup W) {k : ℕ} [Finite (Qt k H)]
    (htf : ∀ t : W, k • t = 0 → t = 0) : {q : W ⧸ H | k • q.out ∈ H}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun q : W ⧸ H => if hq : k • q.out ∈ H then
      (QuotientAddGroup.mk (⟨k • q.out, hq⟩ : H) : Qt k H) else 0) (Set.toFinite _) ?_
  intro q hq q' hq' heq
  have hq1 : k • q.out ∈ H := hq
  have hq2 : k • q'.out ∈ H := hq'
  simp only [dif_pos hq1, dif_pos hq2] at heq
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at heq
  simp only [smulSub, AddSubgroup.mem_map] at heq
  obtain ⟨h, hh, hh'⟩ := heq
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hh'
  have hkey : k • (-q.out + q'.out - h) = 0 := by
    rw [smul_sub, smul_add, smul_neg, hh']
    abel
  have h3 := htf _ hkey
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
  have h4 : -q.out + q'.out = h := sub_eq_zero.1 h3
  rw [h4]
  exact hh

end SB

section Main

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)

include hχl hχr hχ0 hLL hoY in
theorem coef_inv {Φ : W → ℂ} (h : IsSB L X Φ) (a : W) {y : W} (hy : y ∈ Y) :
    ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k3, hk3, hy3⟩ := hoY y hy
  have h0 : ∀ b, χ 0 b = 1 := by
    intro b
    have h1 := hχl 0 0 b
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
  have h0' : ∀ a, χ a 0 = 1 := by
    intro a
    have h1 := hχr a 0 0
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
  have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨k * k3, Nat.mul_pos hk hk3, fun t _ u hu => ?_⟩
  show Φ (a + (t + (k * k3) • u)) * (χ (t + (k * k3) • u) y)⁻¹ = Φ (a + t) * (χ t y)⁻¹
  have hΦ : Φ (a + t + (k * k3) • u) = Φ (a + t) := by
    rw [← smul_smul]; exact hi _ ((L ⊓ X).nsmul_mem hu k3) (a + t)
  have hχu : χ ((k * k3) • u) y = 1 := by
    rw [hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]
  rw [← add_assoc, hΦ, hχl, hχu, mul_one]

include hχl hχr hχ0 hLL hoY hfinX in
theorem coef_add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') (a : W) {y : W} (hy : y ∈ Y) :
    coef χ L X (Φ + Φ') a y = coef χ L X Φ a y + coef χ L X Φ' a y := by
  have inv_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), IsInv k H g → IsInv (k * m) H g := by
    intro H g k m h t ht u hu
    rw [← smul_smul]
    exact h t ht _ (H.nsmul_mem hu m)
  have avg_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), Finite (Qt k H) → Finite (Qt (k * m) H) →
      IsInv k H g → avg (k * m) H g = avg k H g := by
    intro H g k m hfk hfkm hg
    classical
    haveI := Fintype.ofFinite (Qt k H)
    haveI := Fintype.ofFinite (Qt (k * m) H)
    have hle : (smulSub (k * m) H).addSubgroupOf H ≤ (smulSub k H).addSubgroupOf H := by
      intro h hh
      rw [AddSubgroup.mem_addSubgroupOf] at hh ⊢
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at hh ⊢
      obtain ⟨v, hv, hv'⟩ := hh
      exact ⟨m • v, H.nsmul_mem hv m, by rw [← hv', smul_smul]⟩
    let π : Qt (k * m) H →+ Qt k H := QuotientAddGroup.map _ _ (AddMonoidHom.id H) (fun x hx => hle hx)
    have hπ : ∀ x : H, π (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := fun x => rfl
    have hsurj : Function.Surjective π := by
      intro r
      refine ⟨QuotientAddGroup.mk r.out, ?_⟩
      rw [hπ, QuotientAddGroup.out_eq']
    have hval : ∀ q : Qt (k * m) H, g ((q.out : H) : W) = g (((π q).out : H) : W) := by
      intro q
      have hq : π q = QuotientAddGroup.mk q.out := by rw [← hπ, QuotientAddGroup.out_eq']
      have h1 := (QuotientAddGroup.out_eq' (π q)).trans hq
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1
      obtain ⟨v, hv, hv'⟩ := h1
      have h2 : ((q.out : H) : W) = ((π q).out : H) + k • v := by
        rw [hv']
        push_cast
        abel
      rw [h2]
      exact hg _ ((π q).out).2 v hv
    obtain ⟨N, hN⟩ : ∃ N, N = (Finset.univ.filter fun q : Qt (k * m) H => π q = 0).card := ⟨_, rfl⟩
    have hfib : ∀ r : Qt k H, (Finset.univ.filter fun q : Qt (k * m) H => π q = r).card = N := by
      intro r
      rw [hN]
      exact AddMonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 0)
    have hN0 : N ≠ 0 := by
      rw [hN]
      exact (Finset.card_pos.2 ⟨0, by simp⟩).ne'
    have hsum : ∑ q : Qt (k * m) H, g ((q.out : H) : W) = N * ∑ r : Qt k H, g ((r.out : H) : W) := by
      rw [Fintype.sum_congr _ _ hval, Finset.sum_comp (fun r : Qt k H => g ((r.out : H) : W)) π,
        Finset.image_univ_of_surjective hsurj]
      simp_rw [hfib]
      rw [← Finset.smul_sum, nsmul_eq_mul]
    have hcard : Fintype.card (Qt (k * m) H) = N * Fintype.card (Qt k H) := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      simp_rw [hfib]
      simp [mul_comm]
    unfold avg
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hsum, hcard]
    have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    push_cast
    field_simp
  obtain ⟨k1, hk1, hi1⟩ := coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h a hy
  obtain ⟨k2, hk2, hi2⟩ := coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h' a hy
  unfold coef
  obtain ⟨g1, hg1⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g : W → ℂ, g = fun t => Φ' (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  rw [← hg1] at hi1
  rw [← hg2] at hi2
  rw [← hg1, ← hg2]
  have hsum : (fun t => (Φ + Φ') (a + t) * (χ t y)⁻¹) = fun t => g1 t + g2 t := by
    funext t; rw [hg1, hg2]; simp [add_mul]
  rw [hsum]
  have hi3 : IsInv (k1 * k2) (L ⊓ X) (fun t => g1 t + g2 t) := by
    intro t ht u hu
    have e1 := inv_mul _ _ k1 k2 hi1 t ht u hu
    have e2 := inv_mul _ _ k2 k1 hi2 t ht u hu
    rw [mul_comm k2 k1] at e2
    show g1 (t + (k1 * k2) • u) + g2 (t + (k1 * k2) • u) = g1 t + g2 t
    rw [e1, e2]
  have hex1 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g1 := ⟨k1, hk1, hi1⟩
  have hex2 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g2 := ⟨k2, hk2, hi2⟩
  have hex3 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => g1 t + g2 t) := ⟨k1 * k2, Nat.mul_pos hk1 hk2, hi3⟩
  unfold integ
  rw [dif_pos hex1, dif_pos hex2, dif_pos hex3]
  have hK1 := hex1.choose_spec.1
  have hI1 := hex1.choose_spec.2
  have hK2 := hex2.choose_spec.1
  have hI2 := hex2.choose_spec.2
  have hK3 := hex3.choose_spec.1
  have hI3 := hex3.choose_spec.2
  have hpos : 0 < hex1.choose * (hex2.choose * hex3.choose) := by positivity
  have f1 := avg_mul _ _ hex1.choose (hex2.choose * hex3.choose) (hfinX _ hK1) (hfinX _ hpos) hI1
  have f2 := avg_mul _ _ hex2.choose (hex1.choose * hex3.choose) (hfinX _ hK2)
    (hfinX _ (by positivity)) hI2
  have f3 := avg_mul _ _ hex3.choose (hex1.choose * hex2.choose) (hfinX _ hK3)
    (hfinX _ (by positivity)) hI3
  have e2 : hex2.choose * (hex1.choose * hex3.choose) = hex1.choose * (hex2.choose * hex3.choose) := by ring
  have e3 : hex3.choose * (hex1.choose * hex2.choose) = hex1.choose * (hex2.choose * hex3.choose) := by ring
  rw [e2] at f2
  rw [e3] at f3
  rw [← f1, ← f2, ← f3]
  haveI := hfinX _ hpos
  simp only [avg]
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]

include hfinX in
theorem coef_smul (Φ : W → ℂ) (c : ℂ) (a y : W) : coef χ L X (c • Φ) a y = c * coef χ L X Φ a y := by
  unfold coef
  obtain ⟨g, hg⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  have hg' : (fun t => (c • Φ) (a + t) * (χ t y)⁻¹) = fun t => c * g t := by
    funext t; simp [hg, mul_assoc]
  rw [hg', ← hg]
  unfold integ
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    split_ifs with h1
    · unfold avg; simp
    · rfl
  · have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => c * g t) ↔ IsInv k (L ⊓ X) g := by
      intro k
      unfold IsInv
      constructor
      · intro h t ht u hu; exact mul_left_cancel₀ hc (h t ht u hu)
      · intro h t ht u hu; show c * g (t + k • u) = c * g t; rw [h t ht u hu]
    have hpred : (fun k => 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t)) =
        (fun k => 0 < k ∧ IsInv k (L ⊓ X) g) :=
      funext fun k => propext (and_congr_right' (hiff k))
    have key : ∀ (p q : ℕ → Prop) (hp : ∃ k, p k) (hq : ∃ k, q k), p = q → hp.choose = hq.choose := by
      intro p q hp hq h; subst h; rfl
    by_cases hex : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g
    · have hex' : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t) := by rw [hpred]; exact hex
      rw [dif_pos hex', dif_pos hex, key _ _ hex' hex hpred]
      haveI := hfinX _ hex.choose_spec.1
      unfold avg
      rw [← mul_finsum _ c]
      ring
    · have hex' : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t) := by rw [hpred]; exact hex
      rw [dif_neg hex', dif_neg hex, mul_zero]

include hχl hχr hχ0 hLL hdY hoY hfinX in

theorem coef_ne_zero {Φ : W → ℂ} (h : IsSB L X Φ) {k : ℕ} (hk : 0 < k) (hi : ∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t)
    {a y : W} (hy : y ∈ Y) (hc : coef χ L X Φ a y ≠ 0) : (∃ t ∈ L ⊓ X, Φ (a + t) ≠ 0) ∧ k • y ∈ L := by
  unfold coef at hc
  obtain ⟨G, hG⟩ : ∃ G : W → ℂ, G = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  rw [← hG] at hc
  unfold integ at hc
  by_cases hex : ∃ K, 0 < K ∧ IsInv K (L ⊓ X) G
  swap
  · rw [dif_neg hex] at hc; exact absurd rfl hc
  rw [dif_pos hex] at hc
  have hK := hex.choose_spec.1
  have hI := hex.choose_spec.2
  haveI := hfinX _ hK
  classical
  haveI := Fintype.ofFinite (Qt hex.choose (L ⊓ X))
  unfold avg at hc
  rw [finsum_eq_sum_of_fintype] at hc
  have hS : ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) ≠ 0 := by
    intro h0; apply hc; rw [h0, mul_zero]
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    apply hS
    refine Finset.sum_eq_zero fun q _ => ?_
    simp only [hG]
    rw [hno _ (q.out).2, zero_mul]
  · have h0 : ∀ b, χ 0 b = 1 := by
      intro b
      have h1 := hχl 0 0 b
      rw [add_zero] at h1
      exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
    have h0' : ∀ a, χ a 0 = 1 := by
      intro a
      have h1 := hχr a 0 0
      rw [add_zero] at h1
      exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
    have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
      intro n a b
      induction n with
      | zero => rw [zero_smul, pow_zero, h0]
      | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
    have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
      intro n a b
      induction n with
      | zero => rw [zero_smul, pow_zero, h0']
      | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
    apply hdY (k • y) (Y.nsmul_mem hy k)
    intro x hx
    have hGshift : ∀ t, G (t + k • x) = (χ x (k • y))⁻¹ * G t := by
      intro t
      simp only [hG]
      rw [← add_assoc, hi x hx (a + t), hχl, hpow, ← hpow', mul_inv]
      ring
    obtain ⟨z, hz⟩ : ∃ z : ↥(L ⊓ X), (z : W) = k • x := ⟨⟨k • x, (L ⊓ X).nsmul_mem hx k⟩, rfl⟩
    have hshift : ∀ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) =
        G (((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) : W) := by
      intro q
      have hq : (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))) =
          QuotientAddGroup.mk (q.out + z) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      have h1 := (QuotientAddGroup.out_eq' (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))).trans hq
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1
      obtain ⟨v, hv, hv'⟩ := h1
      have h2 : ((q.out : ↥(L ⊓ X)) : W) + k • x =
          ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) + hex.choose • v := by
        rw [hv', ← hz]
        push_cast
        first
          | exact (add_neg_cancel_left _ _).symm
          | simp
          | abel
      rw [h2]
      exact hI _ ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out).2 v hv
    have hshift_sum : ∑ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) =
        ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) := by
      rw [Fintype.sum_congr _ _ hshift]
      exact Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))
        (fun q => G ((q.out : ↥(L ⊓ X)) : W))
    have hmul : (χ x (k • y))⁻¹ * ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) =
        ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) := by
      rw [Finset.mul_sum]
      simp_rw [← hGshift]
      exact hshift_sum
    have h1 := mul_right_cancel₀ hS (hmul.trans (one_mul _).symm)
    exact inv_eq_one.1 h1

include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem term_support_finite {Φ : W → ℂ} (h : IsSB L X Φ) :
    (Function.support fun q : QX L X × QY L Y =>
      if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0).Finite := by
  obtain ⟨hs, k, hk, hi, hl⟩ := id h
  haveI := hfinX k hk
  haveI := hfinY k hk
  have hS1 := finite_nsmul_out (L ⊓ X) (htf k hk)
  have hS2 := finite_nsmul_out (L ⊓ Y) (htf k hk)
  refine (hS1.prod hS2).subset ?_
  rintro ⟨q1, q2⟩ hq
  rw [Function.mem_support] at hq
  split_ifs at hq with hy
  · have hc : coef χ L X Φ q1.out q2.out ≠ 0 := fun h0 => hq (by simp [term, h0])
    obtain ⟨⟨t, ht, hΦ⟩, hky⟩ := coef_ne_zero (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) h hk hi hy hc
    refine ⟨?_, ?_⟩
    · show k • q1.out ∈ L ⊓ X
      have hX : q1.out + t ∈ X := hs _ hΦ
      have hL' : k • (q1.out + t) ∈ L := hl _ hΦ
      have hx : q1.out ∈ X := by simpa using X.sub_mem hX ht.2
      refine ⟨?_, X.nsmul_mem hx k⟩
      have h5 : k • q1.out = k • (q1.out + t) - k • t := by rw [smul_add]; abel
      rw [h5]
      exact L.sub_mem hL' (L.nsmul_mem ht.1 k)
    · exact ⟨hky, Y.nsmul_mem hy k⟩
  · exact absurd rfl hq

end Main

end Formalism.IndefR.Fin.Four

end
end

section
noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

section FinsumAux

variable {α M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem finsum_add' {f g : α → M} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i := by
  exact finsum_add_distrib hf hg

theorem map_finsum' (φ : M →ₗ[ℂ] M') {f : α → M} (hf : (Function.support f).Finite) :
    φ (∑ᶠ i, f i) = ∑ᶠ i, φ (f i) := by
  exact map_finsum φ hf

theorem smul_finsum' (c : ℂ) {f : α → M} (hf : (Function.support f).Finite) :
    c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  exact map_finsum (DistribMulAction.toAddMonoidHom M c) hf

end FinsumAux

section Main

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)

include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') :
    tfun ρ χ L X Y f₀ (Φ + Φ') = tfun ρ χ L X Y f₀ Φ + tfun ρ χ L X Y f₀ Φ' := by
  unfold tfun
  rw [← finsum_add' (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)
    (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h')]
  refine finsum_congr fun q => ?_
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy, term, coef_add hχl hχr hχ0 hLL hfinX hoY h h' _ hy, add_smul]
  · simp only [if_neg hy, add_zero]

include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_smul {Φ : W → ℂ} (h : IsSB L X Φ) (c : ℂ) : tfun ρ χ L X Y f₀ (c • Φ) = c • tfun ρ χ L X Y f₀ Φ := by
  unfold tfun
  rw [smul_finsum' c (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine finsum_congr fun q => ?_
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy, term, coef_smul hfinX, smul_smul]
  · simp only [if_neg hy, smul_zero]

include hX hXY hfX hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_trans {Φ : W → ℂ} (h : IsSB L X Φ) {x : W} (hx : x ∈ X) :
    tfun ρ χ L X Y f₀ (fun t => Φ (t + x)) = ρ x (tfun ρ χ L X Y f₀ Φ) := by
  have hs := h.1
  unfold tfun
  rw [map_finsum' _ (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine Eq.trans ?_ (finsum_comp_equiv
    (Equiv.prodCongr (Equiv.addRight (QuotientAddGroup.mk x : QX L X)) (Equiv.refl (QY L Y))))
  refine finsum_congr fun q => ?_
  show _ = ρ x (if q.2.out ∈ Y then
    term ρ χ L X f₀ Φ (q.1 + (QuotientAddGroup.mk x : QX L X)).out q.2.out else 0)
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy]
    obtain ⟨l, hl, hout⟩ := QX_out (L := L) (X := X) (q.1.out + x)
    have hq : q.1 + (QuotientAddGroup.mk x : QX L X) = QuotientAddGroup.mk (q.1.out + x) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    rw [hq, hout, term_add_left hχl hχ0 hfinX hX hXY hfX Φ hs _ hy hl]
    unfold term
    have hc : coef χ L X (fun t => Φ (t + x)) q.1.out q.2.out = coef χ L X Φ (q.1.out + x) q.2.out := by
      unfold coef
      congr 1
      funext t
      rw [add_right_comm]
    rw [hc, map_smul]
    by_cases ha : q.1.out + x ∈ X
    · have hρ : ρ x (ρ (-(q.1.out + x)) (ρ q.2.out f₀)) = ρ (-q.1.out) (ρ q.2.out f₀) := by
        rw [← Module.End.mul_apply, ← hX _ hx _ (X.neg_mem ha), show x + -(q.1.out + x) = -q.1.out by abel]
      rw [hρ]
    · simp [coef_eq_zero hfinX Φ hs ha]
  · simp only [if_neg hy, map_zero]

include hY hXY hfY hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_modul {Φ : W → ℂ} (h : IsSB L X Φ) {y₀ : W} (hy₀ : y₀ ∈ Y) :
    tfun ρ χ L X Y f₀ (fun t => χ t y₀ * Φ t) = ρ y₀ (tfun ρ χ L X Y f₀ Φ) := by
  have hs := h.1
  unfold tfun
  rw [map_finsum' _ (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine Eq.trans ?_ (finsum_comp_equiv
    (Equiv.prodCongr (Equiv.refl (QX L X)) (Equiv.addRight (QuotientAddGroup.mk (-y₀) : QY L Y))))
  refine finsum_congr fun q => ?_
  show _ = ρ y₀ (if (q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y)).out ∈ Y then
    term ρ χ L X f₀ Φ q.1.out (q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y)).out else 0)
  obtain ⟨μ, hμ, hout⟩ := QY_out (L := L) (Y := Y) (q.2.out + -y₀)
  have hq : q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y) = QuotientAddGroup.mk (q.2.out + -y₀) := by
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  rw [hq, hout]
  have hμY := (AddSubgroup.mem_inf.1 hμ).2
  by_cases hy : q.2.out ∈ Y
  · have hy1 : q.2.out + -y₀ ∈ Y := Y.add_mem hy (Y.neg_mem hy₀)
    rw [if_pos hy, if_pos (Y.add_mem hy1 hμY), term_add_right hfinX hχr hLL hY hfY Φ _ hy1 hμ]
    unfold term
    have hc : coef χ L X (fun t => χ t y₀ * Φ t) q.1.out q.2.out =
        χ q.1.out y₀ * coef χ L X Φ q.1.out (q.2.out + -y₀) := by
      unfold coef
      rw [← integ_cmul' hfinX]
      congr 1
      funext t
      have e1 : χ t q.2.out = χ t (q.2.out + -y₀) * χ t y₀ := by rw [← hχr, neg_add_cancel_right]
      show χ (q.1.out + t) y₀ * Φ (q.1.out + t) * (χ t q.2.out)⁻¹ = _
      rw [hχl, e1, mul_inv]
      linear_combination (χ q.1.out y₀ * Φ (q.1.out + t) * (χ t (q.2.out + -y₀))⁻¹) *
        mul_inv_cancel₀ (hχ0 t y₀)
    rw [hc]
    by_cases ha : q.1.out ∈ X
    · have hc2 := congrArg (fun T : Module.End ℂ V => T (ρ (q.2.out + -y₀) f₀)) (hXY _ (X.neg_mem ha) y₀ hy₀)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at hc2
      have hρy : ρ y₀ (ρ (q.2.out + -y₀) f₀) = ρ q.2.out f₀ := by
        rw [← Module.End.mul_apply, ← hY _ hy₀ _ hy1, show y₀ + (q.2.out + -y₀) = q.2.out by abel]
      have hswap : ρ y₀ (ρ (-q.1.out) (ρ (q.2.out + -y₀) f₀)) = χ q.1.out y₀ • ρ (-q.1.out) (ρ q.2.out f₀) := by
        have h3 : ρ y₀ (ρ (-q.1.out) (ρ (q.2.out + -y₀) f₀)) =
            (χ (-q.1.out) y₀)⁻¹ • ρ (-q.1.out) (ρ y₀ (ρ (q.2.out + -y₀) f₀)) := by
          rw [hc2, smul_smul, inv_mul_cancel₀ (hχ0 _ _), one_smul]
        rw [h3, hρy, chi_neg_left hχl hχ0, inv_inv]
      rw [map_smul, hswap, smul_smul, mul_comm]
    · simp [coef_eq_zero hfinX Φ hs ha]
  · have hy' : q.2.out + -y₀ + μ ∉ Y := fun h' => hy (by
      have := Y.add_mem (Y.sub_mem h' hμY) hy₀
      simpa using this)
    rw [if_neg hy, if_neg hy', map_zero]

include hX hY hXY hfX hfY hχl hχr hχ0 hLL hdY hoY hfinX in
open Classical in
theorem tfun_vac : tfun ρ χ L X Y f₀ (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
  have hsupp := (isSB_ind (L := L) (X := X)).1
  have hval : ∀ a ∈ L ⊓ X, ∀ y ∈ L ⊓ Y,
      term ρ χ L X f₀ (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) a y = f₀ := by
    intro a ha y hy
    have e1 := term_add_left hχl hχ0 hfinX hX hXY hfX _ hsupp 0 (AddSubgroup.mem_inf.1 hy).2 ha
    have e2 := term_add_right hfinX hχr hLL hY hfY (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) 0
      Y.zero_mem hy
    rw [zero_add] at e1 e2
    rw [e1, e2]
    have hc : coef χ L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) 0 0 = 1 := by
      have hpt : ∀ t ∈ L ⊓ X, (if 0 + t ∈ L ∧ 0 + t ∈ X then (1 : ℂ) else 0) * (χ t 0)⁻¹ = 1 := by
        intro t ht
        rw [zero_add, if_pos (AddSubgroup.mem_inf.1 ht), chi_zero_right hχr hχ0, inv_one, mul_one]
      unfold coef
      exact (integ_congr hfinX (g' := fun _ => (1 : ℂ)) hpt).trans (integ_one hfinX)
    rw [term, hc, one_smul, neg_zero, hfX 0 (L ⊓ X).zero_mem, hfX 0 (L ⊓ X).zero_mem]
  unfold tfun
  have h0X : (0 : QX L X).out ∈ L ⊓ X := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
  have h0Y : (0 : QY L Y).out ∈ L ⊓ Y := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
  rw [finsum_eq_single _ ((0 : QX L X), (0 : QY L Y))]
  · show (if (0 : QY L Y).out ∈ Y then _ else _) = f₀
    rw [if_pos (AddSubgroup.mem_inf.1 h0Y).2]
    exact hval _ h0X _ h0Y
  · rintro ⟨q1, q2⟩ hq
    by_cases hy : q2.out ∈ Y
    · show (if q2.out ∈ Y then _ else _) = 0
      rw [if_pos hy, term]
      suffices hc : coef χ L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) q1.out q2.out = 0 by
        rw [hc, zero_smul]
      by_cases h1 : q1 = 0
      · have hq2 : q2 ≠ 0 := fun h2 => hq (by rw [h1, h2])
        have h1X : q1.out ∈ L ⊓ X :=
          (QuotientAddGroup.eq_zero_iff _).1 ((QuotientAddGroup.out_eq' q1).trans h1)
        have hyL : q2.out ∉ L := fun hL => hq2 ((QuotientAddGroup.out_eq' q2).symm.trans
          ((QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_inf.2 ⟨hL, hy⟩)))
        have hne : ¬ ∀ x ∈ L ⊓ X, χ x q2.out = 1 := fun hall => hyL (hdY _ hy hall)
        push_neg at hne
        obtain ⟨u, hu, hχu⟩ := hne
        obtain ⟨m, hm, hmy⟩ := hoY _ hy
        unfold coef
        rw [integ_congr hfinX (g' := fun t => (χ t q2.out)⁻¹) fun t ht => by
          show (if q1.out + t ∈ L ∧ q1.out + t ∈ X then (1 : ℂ) else 0) * _ = _
          rw [if_pos (AddSubgroup.mem_inf.1 ((L ⊓ X).add_mem h1X ht)), one_mul]]
        refine integ_twist hfinX hm (fun t _ u' hu' => ?_) hu (ζ := (χ u q2.out)⁻¹) (by rwa [Ne, inv_eq_one]) ?_
        · rw [hχl, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0,
            hLL _ hu' _ (AddSubgroup.mem_inf.2 ⟨hmy, Y.nsmul_mem hy m⟩), mul_one]
        · intro t _
          rw [hχl, mul_inv, mul_comm]
      · have h1X : q1.out ∉ L ⊓ X := fun hm => h1 ((QuotientAddGroup.out_eq' q1).symm.trans
          ((QuotientAddGroup.eq_zero_iff _).2 hm))
        unfold coef
        refine integ_zero_of hfinX fun t ht => ?_
        show (if q1.out + t ∈ L ∧ q1.out + t ∈ X then (1 : ℂ) else 0) * _ = 0
        rw [if_neg, zero_mul]
        intro hh
        exact h1X (by simpa using (L ⊓ X).sub_mem (AddSubgroup.mem_inf.2 hh) ht)
    · show (if q2.out ∈ Y then _ else _) = 0
      rw [if_neg hy]

include hX hY hXY hfX hfY hχl hχr hχ0 hLL hdY hoX hoY hfinX hfinY htf in
open Classical in

theorem exists_model : ∃ T : (W → ℂ) →ₗ[ℂ] V,
    (∀ Φ, IsSB L X Φ → T Φ = tfun ρ χ L X Y f₀ Φ) ∧
    (∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧
    (∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ)) ∧
    T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
  let S : Submodule ℂ (W → ℂ) :=
    { carrier := {Φ | IsSB L X Φ}
      add_mem' := fun h h' => IsSB.add h h'
      zero_mem' := isSB_zero
      smul_mem' := fun c _ h => IsSB.smul h c }
  let tL : S →ₗ[ℂ] V :=
    { toFun := fun Φ => tfun ρ χ L X Y f₀ Φ.1
      map_add' := fun Φ Φ' => tfun_add (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY)
        (hfinX := hfinX) (hfinY := hfinY) (htf := htf) (hoY := hoY) Φ.2 Φ'.2
      map_smul' := fun c Φ => tfun_smul (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY)
        (hfinX := hfinX) (hfinY := hfinY) (htf := htf) (hoY := hoY) Φ.2 c }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend tL
  have hTe : ∀ Φ, IsSB L X Φ → T Φ = tfun ρ χ L X Y f₀ Φ := fun Φ h => LinearMap.congr_fun hT ⟨Φ, h⟩
  refine ⟨T, hTe, fun Φ h x hx => ?_, fun Φ h y hy => ?_, ?_⟩
  · rw [hTe _ (h.trans hoX hx), hTe _ h]
    exact tfun_trans (hX := hX) (hXY := hXY) (hfX := hfX) (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) (hfinY := hfinY) (htf := htf) h hx
  · rw [hTe _ (h.modul hχl hχr hχ0 hLL hoY hy), hTe _ h]
    exact tfun_modul (hY := hY) (hXY := hXY) (hfY := hfY) (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) (hfinY := hfinY) (htf := htf) h hy
  · rw [hTe _ isSB_ind]
    exact tfun_vac (hX := hX) (hY := hY) (hXY := hXY) (hfX := hfX) (hfY := hfY) (hχl := hχl) (hχr := hχr)
      (hχ0 := hχ0) (hLL := hLL) (hdY := hdY) (hoY := hoY) (hfinX := hfinX)

end Main

end Formalism.IndefR.Fin.Four

end
end
