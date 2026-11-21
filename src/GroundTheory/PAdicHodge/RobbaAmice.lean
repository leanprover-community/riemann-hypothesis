import Mathlib
import GroundTheory.PAdicHodge.RobbaDivision
import GroundTheory.PAdicHodge.RobbaUnitApprox
import GroundTheory.PAdicHodge.RobbaMittagLeffler

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a : ℤ → K} {ρ : ℝ}

theorem dominant_zero_of_gaussNorm_sub_one_lt (hρ : 0 < ρ) {u : ℤ → K} (hu : ConvergesAt u ρ)
    (h1 : gaussNorm (u - Pi.single 0 1) ρ < 1) :
    u ≠ 0 ∧ lowIndex u ρ = 0 ∧ highIndex u ρ = 0 := by
  have hv : ConvergesAt (u - Pi.single 0 1) ρ := hu.sub hρ (convergesAt_single 0 1 ρ)
  have hw : ∀ m : ℤ, ‖(u - (Pi.single 0 (1 : K) : ℤ → K)) m‖ * ρ ^ m < 1 := fun m =>
    (hv.le_gaussNorm m).trans_lt h1
  have hu0 : ‖u 0‖ = 1 := by
    have := hw 0
    simp only [Pi.sub_apply, Pi.single_eq_same, zpow_zero, mul_one] at this
    have e : u 0 = 1 + (u 0 - 1) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact this.ne'),
      norm_one, max_eq_left this.le]
  have hne : u ≠ 0 := fun h => by rw [h] at hu0; simp at hu0
  have hweight : ∀ m, m ≠ 0 → ‖u m‖ * ρ ^ m < ‖u 0‖ * ρ ^ (0 : ℤ) := by
    intro m hm
    have := hw m
    simp only [Pi.sub_apply, Pi.single_eq_of_ne hm, sub_zero] at this
    rw [hu0, zpow_zero, mul_one]; exact this
  have hg : gaussNorm u ρ = 1 := by
    refine le_antisymm (gaussNorm_le fun m => ?_) ?_
    · by_cases hm : m = 0
      · subst hm; rw [hu0, zpow_zero, mul_one]
      · have := hweight m hm; rw [hu0, zpow_zero, mul_one] at this; exact this.le
    · have := hu.le_gaussNorm 0; rwa [hu0, zpow_zero, mul_one] at this
  have hdom : domSet u ρ = {0} := by
    ext m
    simp only [domSet, Set.mem_setOf_eq, hg, Set.mem_singleton_iff]
    constructor
    · intro h; by_contra hm; have := hweight m hm; rw [hu0, zpow_zero, mul_one] at this; linarith
    · rintro rfl; rw [hu0, zpow_zero, mul_one]
  exact ⟨hne, by rw [lowIndex, hdom, csInf_singleton], by rw [highIndex, hdom, csSup_singleton]⟩

theorem dominant_of_perturb {P₀ P : ℤ → K} {N : ℤ} {F : ℝ} (hρ : 0 < ρ)
    (hN : ‖P₀ N‖ * ρ ^ N = F) (hF : 0 < F) (hdom : ∀ i, ‖P₀ i‖ * ρ ^ i ≤ F)
    (hδ : ∀ i, ‖(P - P₀) i‖ * ρ ^ i < F) :
    ‖P N‖ * ρ ^ N = F ∧ ∀ i, ‖P i‖ * ρ ^ i ≤ F := by
  have hρN : 0 < ρ ^ N := zpow_pos hρ N
  constructor
  · have e : P N = P₀ N + (P - P₀) N := by simp
    have h1 : ‖(P - P₀) N‖ < ‖P₀ N‖ := by
      rw [← mul_lt_mul_iff_of_pos_right hρN, hN]; exact hδ N
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le, hN]
  · intro i
    have e : P i = P₀ i + (P - P₀) i := by simp
    rw [e]
    calc ‖P₀ i + (P - P₀) i‖ * ρ ^ i ≤ max ‖P₀ i‖ ‖(P - P₀) i‖ * ρ ^ i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
      _ = max (‖P₀ i‖ * ρ ^ i) (‖(P - P₀) i‖ * ρ ^ i) := max_mul_of_nonneg _ _ (by positivity)
      _ ≤ F := max_le (hdom i) (hδ i).le

end Laurent

namespace Laurent

section Preparation

variable {τ₁ τ₂ : ℝ} {L H : ℤ}

def DivHyp (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) : Prop :=
  0 < τ₁ ∧ τ₁ ≤ τ₂ ∧ L ≤ H ∧ (∀ n, n < L ∨ H < n → P n = 0) ∧ P L ≠ 0 ∧ P H ≠ 0 ∧
    (∀ i, ‖P i‖ * τ₁ ^ i ≤ ‖P L‖ * τ₁ ^ L) ∧ (∀ i, ‖P i‖ * τ₂ ^ i ≤ ‖P H‖ * τ₂ ^ H) ∧
    ConvergesAt h τ₁ ∧ ConvergesAt h τ₂

def DivSpec (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) (qr : (ℤ → K) × (ℤ → K)) : Prop :=
  ConvergesAt qr.1 τ₁ ∧ ConvergesAt qr.1 τ₂ ∧ (∀ n, n < L ∨ H < n → qr.2 n = 0) ∧
    h = cmul qr.1 P + qr.2 ∧
    gaussNorm qr.1 τ₁ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) ∧
    gaussNorm qr.1 τ₂ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) ∧
    gaussNorm qr.2 τ₁ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) *
      gaussNorm P τ₁ ∧
    gaussNorm qr.2 τ₂ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) *
      gaussNorm P τ₂

theorem exists_divSpec (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) :
    ∃ qr : (ℤ → K) × (ℤ → K), DivHyp τ₁ τ₂ L H P h → DivSpec τ₁ τ₂ L H P h qr := by
  by_cases hh : DivHyp τ₁ τ₂ L H P h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hh
    obtain ⟨q, r, hq⟩ := weierstrass_division h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨(q, r), fun _ => hq⟩
  · exact ⟨(0, 0), fun h => absurd h hh⟩

def wdiv (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) : (ℤ → K) × (ℤ → K) :=
  Classical.choose (exists_divSpec τ₁ τ₂ L H P h)

theorem wdiv_spec {P h : ℤ → K} (hh : DivHyp τ₁ τ₂ L H P h) :
    DivSpec τ₁ τ₂ L H P h (wdiv τ₁ τ₂ L H P h) :=
  Classical.choose_spec (exists_divSpec τ₁ τ₂ L H P h) hh

def prepSeq (τ₁ τ₂ : ℝ) (L H : ℤ) (f : ℤ → K) : ℕ → (ℤ → K) × (ℤ → K)
  | 0 => (trunc f (Set.Icc L H), Pi.single 0 1)
  | k + 1 =>
    ((prepSeq τ₁ τ₂ L H f k).1 + (wdiv τ₁ τ₂ L H (prepSeq τ₁ τ₂ L H f k).1
        (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2)).2,
      (prepSeq τ₁ τ₂ L H f k).2 + (wdiv τ₁ τ₂ L H (prepSeq τ₁ τ₂ L H f k).1
        (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2)).1)

end Preparation

end Laurent

namespace Laurent

section PrepInvariant

variable {τ₁ τ₂ : ℝ} {L H : ℤ} {f : ℤ → K} {F₁ F₂ lam : ℝ}

def PrepInv (τ₁ τ₂ : ℝ) (L H : ℤ) (f : ℤ → K) (F₁ F₂ lam : ℝ) (k : ℕ) : Prop :=
  (∀ n, n < L ∨ H < n → (prepSeq τ₁ τ₂ L H f k).1 n = 0) ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).1 - trunc f (Set.Icc L H)) τ₁ ≤ lam * F₁ ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).1 - trunc f (Set.Icc L H)) τ₂ ≤ lam * F₂ ∧
  ConvergesAt (prepSeq τ₁ τ₂ L H f k).2 τ₁ ∧ ConvergesAt (prepSeq τ₁ τ₂ L H f k).2 τ₂ ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).2 - Pi.single 0 1) τ₁ ≤ lam ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).2 - Pi.single 0 1) τ₂ ≤ lam ∧
  gaussNorm (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2) τ₁ ≤
    lam ^ (k + 1) * F₁ ∧
  gaussNorm (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2) τ₂ ≤
    lam ^ (k + 1) * F₂

variable (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hLH : L ≤ H) (h₁ : ConvergesAt f τ₁)
  (h₂ : ConvergesAt f τ₂) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
  (hL : ‖f L‖ * τ₁ ^ L = F₁) (hL' : ∀ i, ‖f i‖ * τ₁ ^ i ≤ F₁)
  (hH : ‖f H‖ * τ₂ ^ H = F₂) (hH' : ∀ i, ‖f i‖ * τ₂ ^ i ≤ F₂)
  (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
  (he₁ : gaussNorm (f - trunc f (Set.Icc L H)) τ₁ ≤ lam * F₁)
  (he₂ : gaussNorm (f - trunc f (Set.Icc L H)) τ₂ ≤ lam * F₂)
include hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂

theorem prepInv_zero : PrepInv τ₁ τ₂ L H f F₁ F₂ lam 0 := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  refine ⟨fun n hn => ?_, ?_, ?_, convergesAt_single 0 1 τ₁, convergesAt_single 0 1 τ₂, ?_, ?_,
    ?_, ?_⟩
  · have : n ∉ Set.Icc L H := fun hm => by simp only [Set.mem_Icc] at hm; omega
    simp [prepSeq, trunc, Set.indicator_of_notMem this]
  · simp only [prepSeq, sub_self, gaussNorm_zero]; positivity
  · simp only [prepSeq, sub_self, gaussNorm_zero]; positivity
  · simp only [prepSeq, sub_self, gaussNorm_zero]; exact hlam0
  · simp only [prepSeq, sub_self, gaussNorm_zero]; exact hlam0
  · simp only [prepSeq, cmul_single_zero_one, zero_add, pow_one]; exact he₁
  · simp only [prepSeq, cmul_single_zero_one, zero_add, pow_one]; exact he₂

set_option maxHeartbeats 1000000 in

theorem prepInv_succ {k : ℕ} (hk : PrepInv τ₁ τ₂ L H f F₁ F₂ lam k) :
    PrepInv τ₁ τ₂ L H f F₁ F₂ lam (k + 1) ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).1 - (prepSeq τ₁ τ₂ L H f k).1) τ₁ ≤
      lam ^ (k + 1) * F₁ ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).1 - (prepSeq τ₁ τ₂ L H f k).1) τ₂ ≤
      lam ^ (k + 1) * F₂ ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).2 - (prepSeq τ₁ τ₂ L H f k).2) τ₁ ≤ lam ^ (k + 1) ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).2 - (prepSeq τ₁ τ₂ L H f k).2) τ₂ ≤ lam ^ (k + 1) := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  obtain ⟨hs, hb1, hb2, hu1, hu2, hv1, hv2, hd1, hd2⟩ := hk
  set P := (prepSeq τ₁ τ₂ L H f k).1 with hPdef
  set u := (prepSeq τ₁ τ₂ L H f k).2 with hudef
  set P₀ := trunc f (Set.Icc L H)
  set e := f - cmul P u with hedef
  have hP₀s : ∀ n, n < L ∨ H < n → P₀ n = 0 := fun n hn => by
    have : n ∉ Set.Icc L H := fun hm => by simp only [Set.mem_Icc] at hm; omega
    simp [P₀, trunc, Set.indicator_of_notMem this]
  have hδs : ∀ n, n < L ∨ H < n → (P - P₀) n = 0 := fun n hn => by
    simp [hs n hn, hP₀s n hn]
  have hP₀L : P₀ L = f L := by simp [P₀, trunc, Set.indicator_of_mem (show L ∈ Set.Icc L H from ⟨le_rfl, hLH⟩)]
  have hP₀H : P₀ H = f H := by simp [P₀, trunc, Set.indicator_of_mem (show H ∈ Set.Icc L H from ⟨hLH, le_rfl⟩)]

  have hdom1 := dominant_of_perturb (P₀ := P₀) (P := P) (N := L) hτ₁ (by rw [hP₀L]; exact hL) hF₁
    (fun i => ((mul_le_mul_of_nonneg_right (norm_trunc_le _ i) (by positivity))).trans (hL' i))
    (fun i => ((convergesAt_of_support hδs τ₁).le_gaussNorm i).trans_lt
      (hb1.trans_lt (by nlinarith)))
  have hdom2 := dominant_of_perturb (P₀ := P₀) (P := P) (N := H) hτ₂ (by rw [hP₀H]; exact hH) hF₂
    (fun i => ((mul_le_mul_of_nonneg_right (norm_trunc_le _ i) (by positivity))).trans (hH' i))
    (fun i => ((convergesAt_of_support hδs τ₂).le_gaussNorm i).trans_lt
      (hb2.trans_lt (by nlinarith)))
  have hPL : P L ≠ 0 := fun h0 => by
    have := hdom1.1; rw [h0, norm_zero, zero_mul] at this; linarith
  have hPH : P H ≠ 0 := fun h0 => by
    have := hdom2.1; rw [h0, norm_zero, zero_mul] at this; linarith
  have hin : ∀ i, ‖P i‖ * τ₁ ^ i ≤ ‖P L‖ * τ₁ ^ L := fun i => by rw [hdom1.1]; exact hdom1.2 i
  have hout : ∀ i, ‖P i‖ * τ₂ ^ i ≤ ‖P H‖ * τ₂ ^ H := fun i => by rw [hdom2.1]; exact hdom2.2 i
  have hG1 : gaussNorm P τ₁ = F₁ := by rw [gaussNorm_eq_of_dominant hs hin, hdom1.1]
  have hG2 : gaussNorm P τ₂ = F₂ := by rw [gaussNorm_eq_of_dominant hs hout, hdom2.1]
  have hPc : ∀ ρ, ConvergesAt P ρ := convergesAt_of_support hs
  have he1 : ConvergesAt e τ₁ := h₁.sub hτ₁ ((hPc τ₁).cmul hτ₁ hu1)
  have he2 : ConvergesAt e τ₂ := h₂.sub hτ₂ ((hPc τ₂).cmul hτ₂ hu2)
  have hhyp : DivHyp τ₁ τ₂ L H P e := ⟨hτ₁, hτ, hLH, hs, hPL, hPH, hin, hout, he1, he2⟩
  obtain ⟨hq1, hq2, hrs, hediv, hqb1, hqb2, hrb1, hrb2⟩ := wdiv_spec hhyp
  set q := (wdiv τ₁ τ₂ L H P e).1
  set r := (wdiv τ₁ τ₂ L H P e).2
  rw [hG1, hG2] at hqb1 hqb2 hrb1 hrb2
  set M := max (gaussNorm e τ₁ / F₁) (gaussNorm e τ₂ / F₂) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (div_nonneg (gaussNorm_nonneg hτ₁) hF₁.le)
  have hMk : M ≤ lam ^ (k + 1) := max_le ((div_le_iff₀ hF₁).2 hd1) ((div_le_iff₀ hF₂).2 hd2)
  have hpow : lam ^ (k + 1) ≤ lam := pow_le_of_le_one hlam0 hlam1.le (by omega)
  have hMlam : M ≤ lam := hMk.trans hpow
  have hrc : ∀ ρ, ConvergesAt r ρ := convergesAt_of_support hrs
  have hnext : prepSeq τ₁ τ₂ L H f (k + 1) = (P + r, u + q) := rfl

  have hδ1 := convergesAt_single 0 (1 : K) τ₁
  have herr : f - cmul (P + r) (u + q) = -(cmul r ((u - Pi.single 0 1) + q)) := by
    have e1 : cmul (P + r) (u + q) = cmul P u + cmul P q + cmul r (u + q) := by
      rw [add_cmul hτ₁ (hPc τ₁) (hrc τ₁) (hu1.add hτ₁ hq1), cmul_add hτ₁ (hPc τ₁) hu1 hq1]
    have e2 : cmul r ((u - Pi.single 0 1) + q) = cmul r (u + q) - r := by
      rw [show (u - Pi.single 0 1) + q = (u + q) + -Pi.single 0 1 by abel,
        cmul_add hτ₁ (hrc τ₁) (hu1.add hτ₁ hq1) hδ1.neg, cmul_neg, cmul_single_zero_one]
      abel
    have e3 : e = cmul P q + r := by rw [hediv, cmul_comm]
    rw [e1, e2]
    have : f = e + cmul P u := by rw [hedef]; abel
    rw [this, e3]; abel
  have hw1 : ConvergesAt ((u - Pi.single 0 1) + q) τ₁ := (hu1.sub hτ₁ hδ1).add hτ₁ hq1
  have hw2 : ConvergesAt ((u - Pi.single 0 1) + q) τ₂ :=
    (hu2.sub hτ₂ (convergesAt_single 0 1 τ₂)).add hτ₂ hq2
  have hwb1 : gaussNorm ((u - Pi.single 0 1) + q) τ₁ ≤ lam :=
    (gaussNorm_add_le hτ₁ (hu1.sub hτ₁ hδ1) hq1).trans (max_le hv1 (hqb1.trans hMlam))
  have hwb2 : gaussNorm ((u - Pi.single 0 1) + q) τ₂ ≤ lam :=
    (gaussNorm_add_le hτ₂ (hu2.sub hτ₂ (convergesAt_single 0 1 τ₂)) hq2).trans
      (max_le hv2 (hqb2.trans hMlam))
  have hrb1' : gaussNorm r τ₁ ≤ lam ^ (k + 1) * F₁ := hrb1.trans (by nlinarith)
  have hrb2' : gaussNorm r τ₂ ≤ lam ^ (k + 1) * F₂ := hrb2.trans (by nlinarith)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro n hn; rw [hnext]; simp [hs n hn, hrs n hn]
  · rw [hnext, show P + r - P₀ = (P - P₀) + r by abel]
    exact (gaussNorm_add_le hτ₁ (convergesAt_of_support hδs τ₁) (hrc τ₁)).trans
      (max_le hb1 (hrb1'.trans (by nlinarith)))
  · rw [hnext, show P + r - P₀ = (P - P₀) + r by abel]
    exact (gaussNorm_add_le hτ₂ (convergesAt_of_support hδs τ₂) (hrc τ₂)).trans
      (max_le hb2 (hrb2'.trans (by nlinarith)))
  · rw [hnext]; exact hu1.add hτ₁ hq1
  · rw [hnext]; exact hu2.add hτ₂ hq2
  · rw [hnext, show u + q - Pi.single 0 1 = (u - Pi.single 0 1) + q by abel]; exact hwb1
  · rw [hnext, show u + q - Pi.single 0 1 = (u - Pi.single 0 1) + q by abel]; exact hwb2
  · rw [hnext]
    show gaussNorm (f - cmul (P + r) (u + q)) τ₁ ≤ lam ^ (k + 1 + 1) * F₁
    rw [herr, gaussNorm_neg]
    calc gaussNorm (cmul r ((u - Pi.single 0 1) + q)) τ₁
        ≤ gaussNorm r τ₁ * gaussNorm ((u - Pi.single 0 1) + q) τ₁ :=
          gaussNorm_cmul_le hτ₁ (hrc τ₁) hw1
      _ ≤ (lam ^ (k + 1) * F₁) * lam :=
          mul_le_mul hrb1' hwb1 (gaussNorm_nonneg hτ₁) (by positivity)
      _ = lam ^ (k + 1 + 1) * F₁ := by ring
  · rw [hnext]
    show gaussNorm (f - cmul (P + r) (u + q)) τ₂ ≤ lam ^ (k + 1 + 1) * F₂
    rw [herr, gaussNorm_neg]
    calc gaussNorm (cmul r ((u - Pi.single 0 1) + q)) τ₂
        ≤ gaussNorm r τ₂ * gaussNorm ((u - Pi.single 0 1) + q) τ₂ :=
          gaussNorm_cmul_le hτ₂ (hrc τ₂) hw2
      _ ≤ (lam ^ (k + 1) * F₂) * lam :=
          mul_le_mul hrb2' hwb2 (gaussNorm_nonneg hτ₂) (by positivity)
      _ = lam ^ (k + 1 + 1) * F₂ := by ring
  · rw [hnext, show P + r - P = r by abel]; exact hrb1'
  · rw [hnext, show P + r - P = r by abel]; exact hrb2'
  · rw [hnext, show u + q - u = q by abel]; exact hqb1.trans hMk
  · rw [hnext, show u + q - u = q by abel]; exact hqb2.trans hMk

theorem prepInv_all : ∀ k, PrepInv τ₁ τ₂ L H f F₁ F₂ lam k
  | 0 => prepInv_zero hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
  | k + 1 => (prepInv_succ hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
      (prepInv_all k)).1

end PrepInvariant

end Laurent

namespace Laurent

section PrepLimit

variable {τ₁ τ₂ : ℝ} {L H : ℤ} {f : ℤ → K} {F₁ F₂ lam : ℝ}

theorem tendsto_pow_succ_mul {lam F : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    Tendsto (fun k : ℕ => lam ^ (k + 1) * F) atTop (𝓝 0) := by
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp (tendsto_add_atTop_nat 1)).mul_const F
  simpa [Function.comp] using this

variable (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hLH : L ≤ H) (h₁ : ConvergesAt f τ₁)
  (h₂ : ConvergesAt f τ₂) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
  (hL : ‖f L‖ * τ₁ ^ L = F₁) (hL' : ∀ i, ‖f i‖ * τ₁ ^ i ≤ F₁)
  (hH : ‖f H‖ * τ₂ ^ H = F₂) (hH' : ∀ i, ‖f i‖ * τ₂ ^ i ≤ F₂)
  (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
  (he₁ : gaussNorm (f - trunc f (Set.Icc L H)) τ₁ ≤ lam * F₁)
  (he₂ : gaussNorm (f - trunc f (Set.Icc L H)) τ₂ ≤ lam * F₂)
include hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂

set_option maxHeartbeats 1000000 in
theorem prep_limit : ∃ P u : ℤ → K, (∀ n, n < L ∨ H < n → P n = 0) ∧ ConvergesAt u τ₁ ∧
    ConvergesAt u τ₂ ∧ gaussNorm (u - Pi.single 0 1) τ₁ < 1 ∧
    gaussNorm (u - Pi.single 0 1) τ₂ < 1 ∧ f = cmul P u := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have inv := prepInv_all hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
  have stp := fun k => (prepInv_succ hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
    (inv k)).2
  set Pk : ℕ → ℤ → K := fun k => (prepSeq τ₁ τ₂ L H f k).1 with hPk
  set uk : ℕ → ℤ → K := fun k => (prepSeq τ₁ τ₂ L H f k).2 with huk
  have hPks : ∀ k n, n < L ∨ H < n → Pk k n = 0 := fun k => (inv k).1
  have hPc : ∀ k ρ, ConvergesAt (Pk k) ρ := fun k => convergesAt_of_support (hPks k)
  have hdPc : ∀ j ρ, ConvergesAt (Pk (j + 1) - Pk j) ρ := fun j ρ =>
    convergesAt_of_support (A := L) (B := H)
      (fun n (hn : n < L ∨ H < n) => by simp [hPks (j + 1) n hn, hPks j n hn]) ρ
  have hCP1 : UCauchy Pk τ₁ := UCauchy.of_gaussNorm hτ₁ (fun j => hdPc j τ₁)
    (squeeze_zero (fun _ => gaussNorm_nonneg hτ₁) (fun j => (stp j).1)
      (tendsto_pow_succ_mul hlam0 hlam1))
  have hu1 : ∀ k, ConvergesAt (uk k) τ₁ := fun k => (inv k).2.2.2.1
  have hu2 : ∀ k, ConvergesAt (uk k) τ₂ := fun k => (inv k).2.2.2.2.1
  have hCu1 : UCauchy uk τ₁ := UCauchy.of_gaussNorm hτ₁ (fun j => (hu1 (j + 1)).sub hτ₁ (hu1 j))
    (squeeze_zero (fun _ => gaussNorm_nonneg hτ₁) (fun j => by simpa using (stp j).2.2.1)
      (by simpa using tendsto_pow_succ_mul (F := 1) hlam0 hlam1))
  have hCu2 : UCauchy uk τ₂ := UCauchy.of_gaussNorm hτ₂ (fun j => (hu2 (j + 1)).sub hτ₂ (hu2 j))
    (squeeze_zero (fun _ => gaussNorm_nonneg hτ₂) (fun j => by simpa using (stp j).2.2.2)
      (by simpa using tendsto_pow_succ_mul (F := 1) hlam0 hlam1))
  set P := limSeq Pk
  set u := limSeq uk
  have hPs : ∀ n, n < L ∨ H < n → P n = 0 := fun n hn =>
    tendsto_nhds_unique (hCP1.tendsto hτ₁ n) (by simp only [hPks _ n hn]; exact tendsto_const_nhds)
  have hPcv : ∀ ρ, ConvergesAt P ρ := convergesAt_of_support hPs
  have hkP : ∀ k ρ, ConvergesAt (Pk k - P) ρ := fun k ρ =>
    convergesAt_of_support (A := L) (B := H)
      (fun n (hn : n < L ∨ H < n) => by simp [hPks k n hn, hPs n hn]) ρ
  have huc1 : ConvergesAt u τ₁ := hCu1.convergesAt hτ₁ hu1
  have huc2 : ConvergesAt u τ₂ := hCu2.convergesAt hτ₂ hu2
  have hδ : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ := convergesAt_single 0 1
  have hε0 : 0 < (1 - lam) / 2 := by linarith
  have hunit : ∀ ρ, 0 < ρ → UCauchy uk ρ → ConvergesAt u ρ → (∀ k, ConvergesAt (uk k) ρ) →
      (∀ k, gaussNorm (uk k - Pi.single 0 1) ρ ≤ lam) → gaussNorm (u - Pi.single 0 1) ρ < 1 := by
    intro ρ hρ hC hc hck hb
    obtain ⟨K₀, hK₀⟩ := hC.gaussNorm_sub_le hρ hε0
    have e : u - Pi.single 0 1 = (u - uk K₀) + (uk K₀ - Pi.single 0 1) := by abel
    rw [e]
    refine (gaussNorm_add_le hρ (hc.sub hρ (hck K₀)) ((hck K₀).sub hρ (hδ ρ))).trans_lt ?_
    exact max_lt ((hK₀ K₀ le_rfl).trans_lt (by linarith)) ((hb K₀).trans_lt hlam1)
  refine ⟨P, u, hPs, huc1, huc2, hunit τ₁ hτ₁ hCu1 huc1 hu1 (fun k => (inv k).2.2.2.2.2.1),
    hunit τ₂ hτ₂ hCu2 huc2 hu2 (fun k => (inv k).2.2.2.2.2.2.1), ?_⟩

  set D := f - cmul P u with hD
  have hDc : ConvergesAt D τ₁ := h₁.sub hτ₁ ((hPcv τ₁).cmul hτ₁ huc1)
  have hsmall : ∀ ε > 0, gaussNorm D τ₁ ≤ ε := by
    intro ε hε
    set C := gaussNorm P τ₁
    have hC0 : 0 ≤ C := gaussNorm_nonneg hτ₁
    obtain ⟨K1, hK1⟩ := hCP1.gaussNorm_sub_le hτ₁ hε
    obtain ⟨K2, hK2⟩ := hCu1.gaussNorm_sub_le hτ₁ (show 0 < ε / (C + 1) by positivity)
    obtain ⟨K3, hK3⟩ := eventually_atTop.1
      ((tendsto_pow_succ_mul (F := F₁) hlam0 hlam1).eventually (ge_mem_nhds hε))
    set k := max K1 (max K2 K3)
    have hk1 : gaussNorm (P - Pk k) τ₁ ≤ ε := hK1 k (le_max_left _ _)
    have hk2 : gaussNorm (u - uk k) τ₁ ≤ ε / (C + 1) := hK2 k (le_max_of_le_right (le_max_left _ _))
    have hk3 : gaussNorm (f - cmul (Pk k) (uk k)) τ₁ ≤ ε :=
      ((inv k).2.2.2.2.2.2.2.1).trans (hK3 k (le_max_of_le_right (le_max_right _ _)))
    have hukb : gaussNorm (uk k) τ₁ ≤ 1 := by
      have e : uk k = (uk k - Pi.single 0 1) + Pi.single 0 1 := by abel
      rw [e]
      refine (gaussNorm_add_le hτ₁ ((hu1 k).sub hτ₁ (hδ τ₁)) (hδ τ₁)).trans (max_le ?_ ?_)
      · exact ((inv k).2.2.2.2.2.1).trans hlam1.le
      · rw [gaussNorm_single_zero_one hτ₁]
    have hexp : D = (f - cmul (Pk k) (uk k)) + (cmul (Pk k - P) (uk k) + cmul P (uk k - u)) := by
      have e1 : cmul (Pk k) (uk k) = cmul P (uk k) + cmul (Pk k - P) (uk k) := by
        rw [← add_cmul hτ₁ (hPcv τ₁) (hkP k τ₁) (hu1 k)]; congr 1; abel
      have e2 : cmul P (uk k) = cmul P u + cmul P (uk k - u) := by
        rw [← cmul_add hτ₁ (hPcv τ₁) huc1 ((hu1 k).sub hτ₁ huc1)]; congr 1; abel
      rw [hD, e1, e2]; abel
    rw [hexp]
    have hc1 : ConvergesAt (cmul (Pk k - P) (uk k)) τ₁ :=
      (hkP k τ₁).cmul hτ₁ (hu1 k)
    have hc2 : ConvergesAt (cmul P (uk k - u)) τ₁ := (hPcv τ₁).cmul hτ₁ ((hu1 k).sub hτ₁ huc1)
    refine (gaussNorm_add_le hτ₁ (h₁.sub hτ₁ ((hPc k τ₁).cmul hτ₁ (hu1 k))) (hc1.add hτ₁ hc2)).trans
      (max_le hk3 ((gaussNorm_add_le hτ₁ hc1 hc2).trans (max_le ?_ ?_)))
    · refine (gaussNorm_cmul_le hτ₁ (hkP k τ₁) (hu1 k)).trans ?_
      rw [gaussNorm_sub_comm]
      calc gaussNorm (P - Pk k) τ₁ * gaussNorm (uk k) τ₁ ≤ ε * 1 :=
            mul_le_mul hk1 hukb (gaussNorm_nonneg hτ₁) hε.le
        _ = ε := mul_one ε
    · refine (gaussNorm_cmul_le hτ₁ (hPcv τ₁) ((hu1 k).sub hτ₁ huc1)).trans ?_
      rw [gaussNorm_sub_comm]
      calc C * gaussNorm (u - uk k) τ₁ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hk2 hC0
        _ ≤ ε := by rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hD0 : gaussNorm D τ₁ = 0 := by
    refine le_antisymm ?_ (gaussNorm_nonneg hτ₁)
    by_contra hpos
    push_neg at hpos
    have := hsmall (gaussNorm D τ₁ / 2) (by positivity)
    linarith
  have := (gaussNorm_eq_zero_iff hτ₁ hDc).1 hD0
  exact (sub_eq_zero.1 this)

end PrepLimit

theorem gaussNorm_sub_trunc_lt {ρ : ℝ} {f : ℤ → K} {L H : ℤ} (hρ : 0 < ρ) (h : ConvergesAt f ρ)
    (hf : f ≠ 0) (hout : ∀ n, n ∉ Set.Icc L H → ‖f n‖ * ρ ^ n < gaussNorm f ρ) :
    gaussNorm (f - trunc f (Set.Icc L H)) ρ < gaussNorm f ρ := by
  have hF := gaussNorm_pos hρ h hf
  have hc : ConvergesAt (f - trunc f (Set.Icc L H)) ρ := h.sub hρ (h.trunc hρ _)
  by_cases h0 : f - trunc f (Set.Icc L H) = 0
  · rw [h0, gaussNorm_zero]; exact hF
  obtain ⟨n, hn⟩ := hc.exists_eq_gaussNorm hρ h0
  rw [← hn]
  by_cases hm : n ∈ Set.Icc L H
  · simp [trunc, Set.indicator_of_mem hm] ; exact hF
  · simp only [Pi.sub_apply, trunc, Set.indicator_of_notMem hm, sub_zero]; exact hout n hm

theorem weierstrass_preparation {τ₁ τ₂ : ℝ} {f : ℤ → K} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂)
    (h₁ : ConvergesAt f τ₁) (h₂ : ConvergesAt f τ₂) (hf : f ≠ 0) :
    ∃ P u : ℤ → K, (∀ n, n < lowIndex f τ₁ ∨ highIndex f τ₂ < n → P n = 0) ∧
      ConvergesAt u τ₁ ∧ ConvergesAt u τ₂ ∧ gaussNorm (u - Pi.single 0 1) τ₁ < 1 ∧
      gaussNorm (u - Pi.single 0 1) τ₂ < 1 ∧ f = cmul P u := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  set L := lowIndex f τ₁
  set H := highIndex f τ₂
  have hLH : L ≤ H :=
    (lowIndex_le_highIndex hτ₁ h₁ hf).trans (highIndex_mono hτ₁ hτ h₁ h₂ hf)
  have hF₁ := gaussNorm_pos hτ₁ h₁ hf
  have hF₂ := gaussNorm_pos hτ₂ h₂ hf
  have hlt₁ : gaussNorm (f - trunc f (Set.Icc L H)) τ₁ < gaussNorm f τ₁ :=
    gaussNorm_sub_trunc_lt hτ₁ h₁ hf fun n hn => by
      simp only [Set.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn | hn
      · exact weight_lt_of_lt_lowIndex hτ₁ h₁ hf hn
      · exact weight_lt_of_highIndex_lt hτ₁ h₁ hf
          (lt_of_le_of_lt (highIndex_mono hτ₁ hτ h₁ h₂ hf) hn)
  have hlt₂ : gaussNorm (f - trunc f (Set.Icc L H)) τ₂ < gaussNorm f τ₂ :=
    gaussNorm_sub_trunc_lt hτ₂ h₂ hf fun n hn => by
      simp only [Set.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn | hn
      · exact weight_lt_of_lt_lowIndex hτ₂ h₂ hf
          (lt_of_lt_of_le hn (lowIndex_mono hτ₁ hτ h₁ h₂ hf))
      · exact weight_lt_of_highIndex_lt hτ₂ h₂ hf hn
  set lam := max (gaussNorm (f - trunc f (Set.Icc L H)) τ₁ / gaussNorm f τ₁)
    (gaussNorm (f - trunc f (Set.Icc L H)) τ₂ / gaussNorm f τ₂)
  have hlam0 : 0 ≤ lam := le_max_of_le_left (div_nonneg (gaussNorm_nonneg hτ₁) hF₁.le)
  have hlam1 : lam < 1 := max_lt ((div_lt_one hF₁).2 hlt₁) ((div_lt_one hF₂).2 hlt₂)
  exact prep_limit hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ (lowIndex_mem hτ₁ h₁ hf) (h₁.le_gaussNorm)
    (highIndex_mem hτ₂ h₂ hf) (h₂.le_gaussNorm) hlam0 hlam1
    ((div_le_iff₀ hF₁).1 (le_max_left _ _)) ((div_le_iff₀ hF₂).1 (le_max_right _ _))

end Laurent

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Polynomial

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem exists_span_pair_eq_map {R : Type*} [CommRing R] (φ : K[X] →+* R)
    (h : ∀ x : R, x ≠ 0 → ∃ u p, IsUnit u ∧ x = u * φ p) (x y : R) :
    ∃ d : K[X], Ideal.span ({x, y} : Set R) = Ideal.span {φ d} := by
  have h' : ∀ x : R, ∃ p, Ideal.span {x} = Ideal.span {φ p} := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    · obtain ⟨u, p, hu, rfl⟩ := h x hx
      exact ⟨p, Ideal.span_singleton_mul_left_unit hu _⟩
  by_cases hx : x = 0
  · subst hx
    obtain ⟨p, hp⟩ := h' y
    rw [show ({0, y} : Set R) = insert 0 {y} from rfl, Ideal.span_insert_zero]
    exact ⟨p, hp⟩
  by_cases hy : y = 0
  · subst hy
    obtain ⟨p, hp⟩ := h' x
    rw [Set.pair_comm, show ({0, x} : Set R) = insert 0 {x} from rfl, Ideal.span_insert_zero]
    exact ⟨p, hp⟩
  obtain ⟨u, p, hu, rfl⟩ := h x hx
  obtain ⟨v, p', hv, rfl⟩ := h y hy
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span ({p, p'} : Set K[X]))).principal
  refine ⟨g, ?_⟩
  have e1 : Ideal.span ({u * φ p, v * φ p'} : Set R) = Ideal.map φ (Ideal.span {p, p'}) := by
    rw [Ideal.map_span, Set.image_pair, Ideal.span_insert, Ideal.span_insert,
      Ideal.span_singleton_mul_left_unit hu, Ideal.span_singleton_mul_left_unit hv]
  rw [e1, hg]
  change Ideal.map φ (Ideal.span {g}) = Ideal.span {φ g}
  rw [Ideal.map_span, Set.image_singleton]

namespace AnnulusRing

variable {I : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)]

def Tinv : AnnulusRing K I := ⟨Pi.single (-1) 1, fun ρ _ _ => convergesAt_single (-1) 1 ρ⟩

theorem T_mul_Tinv : (T : AnnulusRing K I) * Tinv = 1 := by
  ext n
  simp only [coeff_mul, T, Tinv, cmul_single_left, coeff_one, Pi.single_apply, one_mul]
  by_cases hn : n = 0
  · subst hn; simp
  · simp [hn, show n - 1 ≠ -1 by omega]

def unitT : (AnnulusRing K I)ˣ := ⟨T, Tinv, T_mul_Tinv, by rw [mul_comm]; exact T_mul_Tinv⟩

theorem coeff_T_pow (n : ℕ) : ((T : AnnulusRing K I) ^ n).coeff = Pi.single (n : ℤ) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, coeff_mul, ih, cmul_comm, show (T : AnnulusRing K I).coeff = Pi.single 1 1 from rfl,
      cmul_single_left]
    funext m
    simp only [Pi.single_apply, one_mul]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at *; omega)

theorem coeff_unitT_zpow (L : ℤ) :
    (((unitT : (AnnulusRing K I)ˣ) ^ L : (AnnulusRing K I)ˣ) : AnnulusRing K I).coeff =
      Pi.single L 1 := by
  have key : ∀ n : ℕ, (((unitT : (AnnulusRing K I)ˣ) ^ (n : ℤ) : (AnnulusRing K I)ˣ) :
      AnnulusRing K I).coeff = Pi.single (n : ℤ) 1 := fun n => by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]; exact coeff_T_pow n
  have keyinv : ∀ n : ℕ, (((unitT⁻¹ : (AnnulusRing K I)ˣ) ^ n : (AnnulusRing K I)ˣ) :
      AnnulusRing K I).coeff = Pi.single (-(n : ℤ)) 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Units.val_mul, coeff_mul, ih]
      change cmul (Pi.single (-(n : ℤ)) 1) (Pi.single (-1) 1) = _
      rw [cmul_single_left]
      funext m
      simp only [Pi.single_apply, one_mul]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; push_cast at *; omega)
  rcases Int.eq_nat_or_neg L with ⟨n, rfl | rfl⟩
  · exact key n
  · rw [zpow_neg, ← inv_zpow, zpow_natCast]; exact keyinv n

def _root_.GroundTheory.PAdicHodge.Laurent.polySeq (p : K[X]) : ℤ → K :=
  fun n => if 0 ≤ n then p.coeff n.toNat else 0

theorem coeff_aeval_alt (p : K[X]) : (aeval (T : AnnulusRing K I) p).coeff = polySeq p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq]
    funext n; simp only [Pi.add_apply, polySeq, coeff_add]; split_ifs <;> simp
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, coeff_smul,
      coeff_T_pow]
    funext m
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, polySeq,
      coeff_monomial]
    by_cases hm : m = (n : ℤ)
    · subst hm; simp
    · by_cases h0 : 0 ≤ m
      · simp [hm, h0, show n ≠ m.toNat by omega]
      · simp [hm, h0]

theorem eq_zpow_mul_aeval (P : AnnulusRing K I) {L H : ℤ}
    (hsupp : ∀ n, (n < L ∨ H < n) → P.coeff n = 0) :
    ∃ p : K[X], P = ((unitT ^ L : (AnnulusRing K I)ˣ) : AnnulusRing K I) * aeval T p := by
  refine ⟨∑ i ∈ Finset.range (H - L + 1).toNat, monomial i (P.coeff (L + i)), ?_⟩
  ext n
  rw [coeff_mul, coeff_unitT_zpow, coeff_aeval_alt, cmul_single_left]
  simp only [one_mul, polySeq, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
  by_cases h1 : 0 ≤ n - L
  · rw [if_pos h1]
    by_cases h2 : (n - L).toNat < (H - L + 1).toNat
    · rw [if_pos h2]; congr 1; omega
    · rw [if_neg h2]; exact hsupp n (Or.inr (by omega))
  · rw [if_neg h1]; exact hsupp n (Or.inl (by omega))

section Closed

variable {α β : ℝ} [Fact (∃ ρ ∈ Set.Icc α β, 0 < ρ)]

theorem exists_isUnit_mul_aeval (hα : 0 < α) (f : AnnulusRing K (Set.Icc α β)) (hf : f ≠ 0) :
    ∃ u : AnnulusRing K (Set.Icc α β), ∃ p : K[X], IsUnit u ∧ f = u * aeval T p := by
  obtain ⟨ρ₀, hρ₀, -⟩ := (Fact.out : ∃ ρ ∈ Set.Icc α β, 0 < ρ)
  have hαβ : α ≤ β := hρ₀.1.trans hρ₀.2
  have hβ : 0 < β := hα.trans_le hαβ
  have hf0 : f.coeff ≠ 0 := fun e => hf (AnnulusRing.ext e)
  obtain ⟨P, u, hPs, hu1, hu2, hb1, hb2, hfe⟩ := weierstrass_preparation hα hαβ
    (f.convergesAt ⟨le_rfl, hαβ⟩ hα) (f.convergesAt ⟨hαβ, le_rfl⟩ hβ) hf0
  let Pe : AnnulusRing K (Set.Icc α β) := ⟨P, fun ρ _ _ => convergesAt_of_support hPs ρ⟩
  let Ue : AnnulusRing K (Set.Icc α β) := ⟨u, fun ρ hρ _ => hu1.of_le_of_le hu2 hα hρ.1 hρ.2⟩
  have hfPU : f = Pe * Ue := AnnulusRing.ext hfe
  obtain ⟨hUne, hUl, -⟩ := dominant_zero_of_gaussNorm_sub_one_lt hα hu1 hb1
  obtain ⟨-, -, hUh⟩ := dominant_zero_of_gaussNorm_sub_one_lt hβ hu2 hb2
  have hU : IsUnit Ue := isUnit_of_lowIndex_eq_highIndex hα Ue
    (fun e => hUne (congrArg AnnulusRing.coeff e)) (hUl.trans hUh.symm)
  obtain ⟨p, hp⟩ := eq_zpow_mul_aeval Pe hPs
  refine ⟨((unitT ^ lowIndex f.coeff α : (AnnulusRing K (Set.Icc α β))ˣ) :
    AnnulusRing K (Set.Icc α β)) * Ue, p, (Units.isUnit _).mul hU, ?_⟩
  conv_lhs => rw [hfPU, hp]
  ring

theorem exists_span_eq_aeval (hα : 0 < α) (f g : AnnulusRing K (Set.Icc α β)) :
    ∃ d : K[X], Ideal.span ({f, g} : Set (AnnulusRing K (Set.Icc α β))) =
      Ideal.span {aeval (T : AnnulusRing K (Set.Icc α β)) d} :=
  exists_span_pair_eq_map (aeval (T : AnnulusRing K (Set.Icc α β))).toRingHom
    (fun x hx => exists_isUnit_mul_aeval hα x hx) f g

end Closed

end AnnulusRing

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

def IsUnitOn (a : ℤ → K) (α β : ℝ) : Prop :=
  (∀ ρ ∈ Set.Icc α β, ConvergesAt a ρ) ∧ a ≠ 0 ∧ lowIndex a α = highIndex a β

variable {a b : ℤ → K} {r s : ℝ}

theorem isUnitOn_iff [Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ)] (hr : 0 < r)
    (h : ∀ ρ ∈ Set.Icc r s, 0 < ρ → ConvergesAt a ρ) :
    IsUnitOn a r s ↔ IsUnit (⟨a, h⟩ : AnnulusRing K (Set.Icc r s)) := by
  constructor
  · rintro ⟨-, ha, he⟩
    exact AnnulusRing.isUnit_of_lowIndex_eq_highIndex hr _ (fun e => ha (congrArg AnnulusRing.coeff e)) he
  · intro hu
    refine ⟨fun ρ hρ => h ρ hρ (hr.trans_le hρ.1), fun e => ?_,
      AnnulusRing.lowIndex_eq_highIndex_of_isUnit hr hu⟩
    have : (⟨a, h⟩ : AnnulusRing K (Set.Icc r s)) = 0 := AnnulusRing.ext e
    rw [this] at hu
    exact not_isUnit_zero hu

theorem isUnitOn_of_cmul_eq_one (hr : 0 < r) (hrs : r ≤ s) (ha : ∀ ρ ∈ Set.Icc r s, ConvergesAt a ρ)
    (hb : ∀ ρ ∈ Set.Icc r s, ConvergesAt b ρ) (hab : cmul a b = Pi.single 0 1) :
    IsUnitOn a r s ∧ IsUnitOn b r s := by
  haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩
  have e : (⟨a, fun ρ hρ _ => ha ρ hρ⟩ : AnnulusRing K (Set.Icc r s)) * ⟨b, fun ρ hρ _ => hb ρ hρ⟩ = 1 :=
    AnnulusRing.ext hab
  exact ⟨(isUnitOn_iff hr _).2 ⟨⟨_, _, e, by rw [mul_comm]; exact e⟩, rfl⟩,
    (isUnitOn_iff hr _).2 ⟨⟨_, _, by rw [mul_comm]; exact e, e⟩, rfl⟩⟩

theorem IsUnitOn.cmul (hr : 0 < r) (hrs : r ≤ s) (ha : IsUnitOn a r s) (hb : IsUnitOn b r s) :
    IsUnitOn (Laurent.cmul a b) r s := by
  haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩
  have ha' := (isUnitOn_iff hr fun ρ hρ _ => ha.1 ρ hρ).1 ha
  have hb' := (isUnitOn_iff hr fun ρ hρ _ => hb.1 ρ hρ).1 hb
  exact (isUnitOn_iff hr fun ρ hρ h0 => (ha.1 ρ hρ).cmul h0 (hb.1 ρ hρ)).2 (ha'.mul hb')

theorem IsUnitOn.inv (hr : 0 < r) (hrs : r ≤ s) (ha : IsUnitOn a r s) :
    IsUnitOn (invDom a (lowIndex a r)) r s ∧
      Laurent.cmul a (invDom a (lowIndex a r)) = Pi.single 0 1 := by
  have hspec : ∀ ρ ∈ Set.Icc r s, ConvergesAt (invDom a (lowIndex a r)) ρ ∧
      Laurent.cmul a (invDom a (lowIndex a r)) = Pi.single 0 1 := fun ρ hρ =>
    invDom_spec (hr.trans_le hρ.1) (ha.1 ρ hρ) ha.2.1
      (unique_dominant_of_lowIndex_eq_highIndex hr ha.1 ha.2.1 ha.2.2 hρ)
  have h1 := (hspec r ⟨le_rfl, hrs⟩).2
  exact ⟨(isUnitOn_of_cmul_eq_one hr hrs ha.1 (fun ρ hρ => (hspec ρ hρ).1) h1).2, h1⟩

theorem isUnitOn_single_zero_one (hr : 0 < r) (hrs : r ≤ s) :
    IsUnitOn (Pi.single 0 (1 : K)) r s :=
  (isUnitOn_of_cmul_eq_one hr hrs (fun ρ _ => convergesAt_single 0 1 ρ)
    (fun ρ _ => convergesAt_single 0 1 ρ) (cmul_single_zero_one _)).1

theorem gaussNorm_eq_one_of_sub_lt_one {z : ℤ → K} {ρ : ℝ} (hρ : 0 < ρ) (hz : ConvergesAt z ρ)
    (h1 : gaussNorm (z - Pi.single 0 1) ρ < 1) : gaussNorm z ρ = 1 := by
  have hv : ConvergesAt (z - Pi.single 0 1) ρ := hz.sub hρ (convergesAt_single 0 1 ρ)
  have hw : ∀ m : ℤ, ‖(z - (Pi.single 0 (1 : K) : ℤ → K)) m‖ * ρ ^ m < 1 := fun m =>
    (hv.le_gaussNorm m).trans_lt h1
  have hz0 : ‖z 0‖ = 1 := by
    have := hw 0
    simp only [Pi.sub_apply, Pi.single_eq_same, zpow_zero, mul_one] at this
    have e : z 0 = 1 + (z 0 - 1) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact this.ne'),
      norm_one, max_eq_left this.le]
  refine le_antisymm (gaussNorm_le fun m => ?_) ?_
  · by_cases hm : m = 0
    · subst hm; rw [hz0, zpow_zero, mul_one]
    · have := hw m
      simp only [Pi.sub_apply, Pi.single_eq_of_ne hm, sub_zero] at this
      exact this.le
  · have := hz.le_gaussNorm 0; rwa [hz0, zpow_zero, mul_one] at this

theorem unique_dominant_of_perturb {ρ : ℝ} (hρ : 0 < ρ) {N : ℤ}
    (hN : ∀ m, m ≠ N → ‖a m‖ * ρ ^ m < ‖a N‖ * ρ ^ N) (hδ : ConvergesAt (b - a) ρ)
    (hsmall : gaussNorm (b - a) ρ < ‖a N‖ * ρ ^ N) :
    ‖b N‖ * ρ ^ N = ‖a N‖ * ρ ^ N ∧ ∀ m, m ≠ N → ‖b m‖ * ρ ^ m < ‖b N‖ * ρ ^ N := by
  have hρN : 0 < ρ ^ N := zpow_pos hρ N
  have hw : ∀ m, ‖(b - a) m‖ * ρ ^ m < ‖a N‖ * ρ ^ N := fun m =>
    (hδ.le_gaussNorm m).trans_lt hsmall
  have e1 : ‖b N‖ * ρ ^ N = ‖a N‖ * ρ ^ N := by
    have e : b N = a N + (b - a) N := by simp
    have h1 : ‖(b - a) N‖ < ‖a N‖ := by
      rw [← mul_lt_mul_iff_of_pos_right hρN]; exact hw N
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le]
  refine ⟨e1, fun m hm => ?_⟩
  rw [e1]
  have e : b m = a m + (b - a) m := by simp
  rw [e]
  calc ‖a m + (b - a) m‖ * ρ ^ m ≤ max ‖a m‖ ‖(b - a) m‖ * ρ ^ m :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
    _ = max (‖a m‖ * ρ ^ m) (‖(b - a) m‖ * ρ ^ m) := max_mul_of_nonneg _ _ (by positivity)
    _ < ‖a N‖ * ρ ^ N := max_lt (hN m hm) (hw m)

theorem low_high_of_unique_dominant {ρ : ℝ} (hρ : 0 < ρ) (h : ConvergesAt a ρ) {N : ℤ}
    (hN : ∀ m, m ≠ N → ‖a m‖ * ρ ^ m < ‖a N‖ * ρ ^ N) (ha : a N ≠ 0) :
    lowIndex a ρ = N ∧ highIndex a ρ = N := by
  have hg : gaussNorm a ρ = ‖a N‖ * ρ ^ N :=
    le_antisymm (gaussNorm_le fun m => by
      by_cases hm : m = N
      · subst hm; exact le_rfl
      · exact (hN m hm).le) (h.le_gaussNorm N)
  have hdom : domSet a ρ = {N} := by
    ext m
    simp only [domSet, Set.mem_setOf_eq, hg, Set.mem_singleton_iff]
    constructor
    · intro e; by_contra hm; exact (hN m hm).ne e
    · rintro rfl; rfl
  exact ⟨by rw [lowIndex, hdom, csInf_singleton], by rw [highIndex, hdom, csSup_singleton]⟩

section Step

theorem divisor_step {t₀ t₁ q' δ : ℝ} {n₀ : ℕ} (hr : 0 < r) (h0 : r ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1 : t₁ < 1) (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖)
    (hn₀ : q' ≤ t₁ ^ n₀) (hδ : 0 < δ) (hB : max ((t₀ / t₁) ^ n₀) δ < 1)
    {d d' v D w : ℤ → K} (hd : ∀ ρ, 0 < ρ → ConvergesAt d ρ)
    (hd' : ∀ ρ, 0 < ρ → ConvergesAt d' ρ) (hv : IsUnitOn v r t₁) (hvd : Laurent.cmul d v = d')
    (hD : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt D ρ) (hw : IsUnitOn w r t₁)
    (hDw : D = Laurent.cmul d w) :
    ∃ D' w' z : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt D' ρ) ∧
      (∀ s, r ≤ s → s < 1 → IsUnitOn w' r s) ∧ D' = Laurent.cmul d' w' ∧
      IsUnitOn z r t₁ ∧ D' = Laurent.cmul D z ∧
      ∀ ρ ∈ Set.Icc r t₀, gaussNorm (z - Pi.single 0 1) ρ ≤ max ((t₀ / t₁) ^ n₀) δ := by
  have hrt : r ≤ t₁ := h0.trans h01
  obtain ⟨hvi, hvvi⟩ := hv.inv hr hrt
  set vi := invDom v (lowIndex v r)
  set y := Laurent.cmul w vi with hydef
  have hy : IsUnitOn y r t₁ := hw.cmul hr hrt hvi
  obtain ⟨W, V, hWV, hWV1, happrox⟩ :=
    exists_unit_approx hr h0 h01 h1 hq' hbig hn₀ hy.1 hy.2.1 hy.2.2 hδ
  obtain ⟨hyi, hyyi⟩ := hy.inv hr hrt
  set yi := invDom y (lowIndex y r)
  have hWunit : ∀ s, r ≤ s → s < 1 → IsUnitOn W r s ∧ IsUnitOn V r s := fun s hs hs1 =>
    isUnitOn_of_cmul_eq_one hr hs (fun ρ hρ => (hWV ρ hρ.1 (hρ.2.trans_lt hs1)).1)
      (fun ρ hρ => (hWV ρ hρ.1 (hρ.2.trans_lt hs1)).2) hWV1
  have hWt := hWunit t₁ hrt h1
  refine ⟨Laurent.cmul d' W, W, Laurent.cmul yi W, fun ρ h1' h2' =>
    (hd' ρ (hr.trans_le h1')).cmul (hr.trans_le h1') (hWV ρ h1' h2').1,
    fun s hs hs1 => (hWunit s hs hs1).1, rfl, hyi.cmul hr hrt hWt.1, ?_, ?_⟩
  all_goals haveI : Fact (∃ ρ ∈ Set.Icc r t₁, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrt⟩, hr⟩⟩
  all_goals
    let I := Set.Icc r t₁
    let ed : AnnulusRing K I := ⟨d, fun ρ _ h => hd ρ h⟩
    let ed' : AnnulusRing K I := ⟨d', fun ρ _ h => hd' ρ h⟩
    let ev : AnnulusRing K I := ⟨v, fun ρ hρ _ => hv.1 ρ hρ⟩
    let evi : AnnulusRing K I := ⟨vi, fun ρ hρ _ => hvi.1 ρ hρ⟩
    let ew : AnnulusRing K I := ⟨w, fun ρ hρ _ => hw.1 ρ hρ⟩
    let eyi : AnnulusRing K I := ⟨yi, fun ρ hρ _ => hyi.1 ρ hρ⟩
    let eW : AnnulusRing K I := ⟨W, fun ρ hρ _ => hWt.1.1 ρ hρ⟩
    let eV : AnnulusRing K I := ⟨V, fun ρ hρ _ => hWt.2.1 ρ hρ⟩
    have k1 : ev * evi = 1 := AnnulusRing.ext hvvi
    have k2 : (ew * evi) * eyi = 1 := AnnulusRing.ext hyyi
    have k3 : eW * eV = 1 := AnnulusRing.ext hWV1
    have k4 : ed * ev = ed' := AnnulusRing.ext hvd
  ·
    have : ed' * eW = (ed * ew) * (eyi * eW) := by
      linear_combination (ed * eW * ew * eyi) * k1 - (ed * eW * ev) * k2 - eW * k4
    rw [hDw]
    exact congrArg AnnulusRing.coeff this
  · intro ρ hρ
    have hρ0 : 0 < ρ := hr.trans_le hρ.1
    have hρ1 : ρ ∈ Set.Icc r t₁ := ⟨hρ.1, hρ.2.trans h01⟩
    have hB' := happrox ρ hρ
    have hyV : ConvergesAt (Laurent.cmul y V) ρ := (hy.1 ρ hρ1).cmul hρ0 (hWt.2.1 ρ hρ1)
    have hz : ConvergesAt (Laurent.cmul yi W) ρ := (hyi.1 ρ hρ1).cmul hρ0 (hWt.1.1 ρ hρ1)
    have he : ConvergesAt (Laurent.cmul y V - Pi.single 0 1) ρ :=
      hyV.sub hρ0 (convergesAt_single 0 1 ρ)
    have hyV1 : gaussNorm (Laurent.cmul y V) ρ = 1 :=
      gaussNorm_eq_one_of_sub_lt_one hρ0 hyV (hB'.trans_lt hB)

    have r1 : (eyi * eW) * ((ew * evi) * eV) = 1 := by
      linear_combination (eW * eV) * k2 + k3
    have r2 : (eyi * eW) - 1 = -((eyi * eW) * ((ew * evi) * eV - 1)) := by
      linear_combination r1
    have c1 : Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V) = Pi.single 0 1 :=
      congrArg AnnulusRing.coeff r1
    have c2 : Laurent.cmul yi W - Pi.single 0 1 =
        -Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V - Pi.single 0 1) :=
      congrArg AnnulusRing.coeff r2
    have hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    have hz0 : Laurent.cmul yi W ≠ 0 := fun h0 => hne (by rw [← c1, h0, zero_cmul])
    have hyV0 : Laurent.cmul y V ≠ 0 := fun h0 => hne (by rw [← c1, h0, cmul_zero])
    have hz1 : gaussNorm (Laurent.cmul yi W) ρ = 1 := by
      have := gaussNorm_cmul hρ0 hz hyV hz0 hyV0
      rw [c1, gaussNorm_single_zero_one hρ0, hyV1, mul_one] at this
      exact this.symm
    rw [c2, gaussNorm_neg]
    calc gaussNorm (Laurent.cmul (Laurent.cmul yi W) (Laurent.cmul y V - Pi.single 0 1)) ρ
        ≤ gaussNorm (Laurent.cmul yi W) ρ * gaussNorm (Laurent.cmul y V - Pi.single 0 1) ρ :=
          gaussNorm_cmul_le hρ0 hz he
      _ ≤ _ := by rw [hz1, one_mul]; exact hB'

end Step

section Main

theorem cmul_sub_right {ρ : ℝ} (hρ : 0 < ρ) {x y z : ℤ → K} (hx : ConvergesAt x ρ)
    (hy : ConvergesAt y ρ) (hz : ConvergesAt z ρ) :
    Laurent.cmul x (y - z) = Laurent.cmul x y - Laurent.cmul x z := by
  rw [sub_eq_add_neg, cmul_add hρ hx hy hz.neg, cmul_neg, ← sub_eq_add_neg]

theorem exists_divisor [IsDiscreteValuationRing (normInteger K)] (hr : 0 < r) {t : ℕ → ℝ}
    (ht0 : t 0 = r) (hmono : Monotone t) (ht1 : ∀ k, t k < 1) (hlim : ∀ ρ < 1, ∃ k, ρ ≤ t k)
    {q' : ℝ} (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖) {n₀ : ℕ → ℕ}
    (hn₀ : ∀ k, q' ≤ t (k + 1) ^ n₀ k) (hβ : ∀ k, (t k / t (k + 1)) ^ n₀ k ≤ (1 / 2) ^ (k + 1))
    {d : ℕ → ℤ → K} (hd : ∀ k ρ, 0 < ρ → ConvergesAt (d k) ρ) (hd0 : ∀ k, d k ≠ 0)
    (hv : ∀ k, ∃ v, IsUnitOn v r (t (k + 1)) ∧ Laurent.cmul (d k) v = d (k + 1)) :
    ∃ D : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt D ρ) ∧
      ∀ m, ∃ u, IsUnitOn u r (t (m + 1)) ∧ D = Laurent.cmul (d m) u := by
  classical
  choose v hvU hvd using hv
  have hrt : ∀ k, r ≤ t k := fun k => ht0 ▸ hmono (Nat.zero_le k)
  have pos : ∀ ρ, r ≤ ρ → 0 < ρ := fun ρ h => hr.trans_le h
  have hhalf : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < 1 := fun k =>
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)

  let Spec : ℕ → (ℤ → K) → (ℤ → K) × (ℤ → K) × (ℤ → K) → Prop := fun k D p =>
    (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt p.1 ρ) ∧ (∀ s, r ≤ s → s < 1 → IsUnitOn p.2.1 r s) ∧
      p.1 = Laurent.cmul (d (k + 1)) p.2.1 ∧ IsUnitOn p.2.2 r (t (k + 1)) ∧
      p.1 = Laurent.cmul D p.2.2 ∧
      ∀ ρ ∈ Set.Icc r (t k), gaussNorm (p.2.2 - Pi.single 0 1) ρ ≤ (1 / 2) ^ (k + 1)
  let stepFn : ℕ → (ℤ → K) × (ℤ → K) × (ℤ → K) → (ℤ → K) × (ℤ → K) × (ℤ → K) := fun k p =>
    if h : ∃ p', Spec k p.1 p' then h.choose else p
  obtain ⟨S, S_zero, S_succ⟩ : ∃ S : ℕ → (ℤ → K) × (ℤ → K) × (ℤ → K),
      S 0 = (d 0, Pi.single 0 1, Pi.single 0 1) ∧ ∀ k, S (k + 1) = stepFn k (S k) :=
    ⟨fun k => Nat.rec (d 0, Pi.single 0 1, Pi.single 0 1) stepFn k, rfl, fun k => rfl⟩
  let Inv : ℕ → Prop := fun k => (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (S k).1 ρ) ∧
    IsUnitOn (S k).2.1 r (t (k + 1)) ∧ (S k).1 = Laurent.cmul (d k) (S k).2.1
  have spec_of_inv : ∀ k, Inv k → Spec k (S k).1 (S (k + 1)) := by
    intro k hk
    have hex : ∃ p', Spec k (S k).1 p' := by
      obtain ⟨D', w', z, h1, h2, h3, h4, h5, h6⟩ := divisor_step (δ := (1 / 2) ^ (k + 1)) hr
        (hrt k) (hmono (Nat.le_succ k)) (ht1 _) hq' hbig (hn₀ k) (by positivity)
        (max_lt ((hβ k).trans_lt (hhalf k)) (hhalf k)) (hd k) (hd (k + 1)) (hvU k) (hvd k)
        hk.1 hk.2.1 hk.2.2
      exact ⟨(D', w', z), h1, h2, h3, h4, h5, fun ρ hρ =>
        (h6 ρ hρ).trans (max_le (hβ k) le_rfl)⟩
    rw [S_succ]
    change Spec k (S k).1 (if h : ∃ p', Spec k (S k).1 p' then h.choose else S k)
    rw [dif_pos hex]
    exact hex.choose_spec
  have inv : ∀ k, Inv k := by
    intro k
    induction k with
    | zero =>
      show (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (S 0).1 ρ) ∧ IsUnitOn (S 0).2.1 r (t (0 + 1)) ∧
        (S 0).1 = Laurent.cmul (d 0) (S 0).2.1
      rw [S_zero]
      exact ⟨fun ρ h1 _ => hd 0 ρ (pos ρ h1), isUnitOn_single_zero_one hr (hrt 1),
        (cmul_single_zero_one _).symm⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3, -, -, -⟩ := spec_of_inv k ih
      exact ⟨h1, h2 _ (hrt _) (ht1 _), h3⟩
  have spec : ∀ k, Spec k (S k).1 (S (k + 1)) := fun k => spec_of_inv k (inv k)

  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℕ → ℤ → K, ∀ k, Dk k = (S k).1 := ⟨fun k => (S k).1, fun k => rfl⟩
  obtain ⟨zk, hzk⟩ : ∃ zk : ℕ → ℤ → K, ∀ k, zk k = (S (k + 1)).2.2 :=
    ⟨fun k => (S (k + 1)).2.2, fun k => rfl⟩
  have Dconv : ∀ k ρ, r ≤ ρ → ρ < 1 → ConvergesAt (Dk k) ρ := fun k => by
    rw [hDk]; exact (inv k).1
  have Dne : ∀ k, Dk k ≠ 0 := by
    intro k
    rw [hDk, (inv k).2.2]
    exact cmul_ne_zero hr (hd k r hr) ((inv k).2.1.1 r ⟨le_rfl, hrt _⟩) (hd0 k) (inv k).2.1.2.1
  have zconv : ∀ k ρ, r ≤ ρ → ρ ≤ t (k + 1) → ConvergesAt (zk k) ρ := fun k ρ h1 h2 => by
    rw [hzk]; exact (spec k).2.2.2.1.1 ρ ⟨h1, h2⟩
  have zsmall : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (zk k - Pi.single 0 1) ρ ≤ (1 / 2) ^ (k + 1) :=
    fun k ρ h1 h2 => by rw [hzk]; exact (spec k).2.2.2.2.2 ρ ⟨h1, h2⟩
  have zunit : ∀ k, IsUnitOn (zk k) r (t (k + 1)) := fun k => by rw [hzk]; exact (spec k).2.2.2.1
  have zone : ∀ k ρ, r ≤ ρ → ρ ≤ t k → gaussNorm (zk k) ρ = 1 := fun k ρ h1 h2 =>
    gaussNorm_eq_one_of_sub_lt_one (pos ρ h1) (zconv k ρ h1 (h2.trans (hmono (Nat.le_succ k))))
      ((zsmall k ρ h1 h2).trans_lt (hhalf k))
  have Dstep : ∀ k, Dk (k + 1) = Laurent.cmul (Dk k) (zk k) := fun k => by
    rw [hDk, hDk, hzk]; exact (spec k).2.2.2.2.1

  have Ddiff : ∀ k ρ, r ≤ ρ → ρ ≤ t k →
      gaussNorm (Dk (k + 1) - Dk k) ρ ≤ gaussNorm (Dk k) ρ * (1 / 2) ^ (k + 1) := by
    intro k ρ h1 h2
    have h0 := pos ρ h1
    have hρ1 : ρ < 1 := h2.trans_lt (ht1 k)
    have hz := zconv k ρ h1 (h2.trans (hmono (Nat.le_succ k)))
    have e : Dk (k + 1) - Dk k = Laurent.cmul (Dk k) (zk k - Pi.single 0 1) := by
      rw [Dstep, cmul_sub_right h0 (Dconv k ρ h1 hρ1) hz (convergesAt_single 0 1 ρ),
        cmul_single_zero_one]
    rw [e]
    exact (gaussNorm_cmul_le h0 (Dconv k ρ h1 hρ1) (hz.sub h0 (convergesAt_single 0 1 ρ))).trans
      (mul_le_mul_of_nonneg_left (zsmall k ρ h1 h2) (gaussNorm_nonneg h0))
  have Dnorm : ∀ m k, m ≤ k → ∀ ρ, r ≤ ρ → ρ ≤ t m → gaussNorm (Dk k) ρ = gaussNorm (Dk m) ρ := by
    intro m k hmk ρ h1 h2
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
      have h0 := pos ρ h1
      have hρk : ρ ≤ t k := h2.trans (hmono hmk)
      have hz := zconv k ρ h1 (hρk.trans (hmono (Nat.le_succ k)))
      have hzne : zk k ≠ 0 := (zunit k).2.1
      rw [Dstep, gaussNorm_cmul h0 (Dconv k ρ h1 (hρk.trans_lt (ht1 k))) hz (Dne k) hzne,
        zone k ρ h1 hρk, mul_one, ih]

  have geom : ∀ G ≥ (0 : ℝ), ∀ e > (0 : ℝ), ∀ m : ℕ, ∃ K₀ ≥ m, ∀ j ≥ K₀, G * (1 / 2) ^ (j + 1) ≤ e := by
    intro G hG e he m
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos he (by linarith : (0:ℝ) < G + 1))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨max N m, le_max_right _ _, fun j hj => ?_⟩
    have h1 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (j + 1) ≤ e / (G + 1) := h1.trans hN.le
    calc G * (1 / 2) ^ (j + 1) ≤ (G + 1) * (e / (G + 1)) :=
          mul_le_mul (by linarith) h2 (by positivity) (by linarith)
      _ = e := mul_div_cancel₀ _ (by linarith)
  have Dcauchy : ∀ m ρ, r ≤ ρ → ρ ≤ t m → UCauchy Dk ρ := by
    intro m ρ h1 h2 e he
    obtain ⟨K₀, hK₀m, hK₀⟩ := geom (gaussNorm (Dk m) ρ) (gaussNorm_nonneg (pos ρ h1)) e he m
    refine ⟨K₀, fun j hj n => ?_⟩
    have hρj : ρ ≤ t j := h2.trans (hmono (hK₀m.trans hj))
    have hρ1 : ρ < 1 := h2.trans_lt (ht1 m)
    have hc : ConvergesAt (Dk (j + 1) - Dk j) ρ :=
      (Dconv _ ρ h1 hρ1).sub (pos ρ h1) (Dconv j ρ h1 hρ1)
    refine (hc.le_gaussNorm n).trans ((Ddiff j ρ h1 hρj).trans ?_)
    rw [Dnorm m j (hK₀m.trans hj) ρ h1 h2]
    exact hK₀ j hj

  have Dlimconv : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (limSeq Dk) ρ := fun ρ h1 h2 => by
    obtain ⟨m, hm⟩ := hlim ρ h2
    exact (Dcauchy m ρ h1 hm).convergesAt_of_eventually (pos ρ h1) (K₁ := 0)
      fun k _ => Dconv k ρ h1 h2
  refine ⟨limSeq Dk, Dlimconv, fun m => ?_⟩
  have hJ : ∀ j, t (m + 1) ≤ t (m + j + 1) := fun j => hmono (by omega)
  have hm1 : r ≤ t (m + 1) := hrt _
  have hwm : IsUnitOn (S m).2.1 r (t (m + 1)) := (inv m).2.1
  obtain ⟨U, U_zero, U_succ⟩ : ∃ U : ℕ → ℤ → K, U 0 = Laurent.cmul (S m).2.1 (zk m) ∧
      ∀ j, U (j + 1) = Laurent.cmul (U j) (zk (m + j + 1)) :=
    ⟨fun j => Nat.rec (Laurent.cmul (S m).2.1 (zk m))
      (fun j x => Laurent.cmul x (zk (m + j + 1))) j, rfl, fun j => rfl⟩
  have Uconv : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → ConvergesAt (U j) ρ := by
    intro j ρ h1 h2
    induction j with
    | zero => rw [U_zero]; exact (hwm.1 ρ ⟨h1, h2⟩).cmul (pos ρ h1) (zconv m ρ h1 h2)
    | succ j ih =>
      rw [U_succ]
      exact ih.cmul (pos ρ h1) (zconv _ ρ h1 (h2.trans (hJ (j + 1))))
  have DU : ∀ j, Dk (m + j + 1) = Laurent.cmul (d m) (U j) := by
    intro j
    induction j with
    | zero =>
      rw [show m + 0 + 1 = m + 1 by omega, Dstep, U_zero, hDk m, (inv m).2.2]
      exact cmul_assoc hr (hd m r hr) (hwm.1 r ⟨le_rfl, hm1⟩) (zconv m r le_rfl hm1)
    | succ j ih =>
      rw [show m + (j + 1) + 1 = (m + j + 1) + 1 by omega, Dstep, ih, U_succ]
      exact cmul_assoc hr (hd m r hr) (Uconv j r le_rfl hm1)
        (zconv _ r le_rfl ((hrt _)))
  have Une : ∀ j, U j ≠ 0 := fun j h0 => Dne (m + j + 1) (by rw [DU j, h0, cmul_zero])
  have Unorm : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) → gaussNorm (U j) ρ = gaussNorm (U 0) ρ := by
    intro j ρ h1 h2
    induction j with
    | zero => rfl
    | succ j ih =>
      have hρ' : ρ ≤ t (m + j + 1) := h2.trans (hJ j)
      rw [U_succ, gaussNorm_cmul (pos ρ h1) (Uconv j ρ h1 h2)
        (zconv _ ρ h1 (hρ'.trans (hmono (Nat.le_succ _)))) (Une j) (zunit _).2.1,
        zone _ ρ h1 hρ', mul_one, ih]
  have Udiff : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      gaussNorm (U (j + 1) - U j) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + j + 1 + 1) := by
    intro j ρ h1 h2
    have h0 := pos ρ h1
    have hρ' : ρ ≤ t (m + j + 1) := h2.trans (hJ j)
    have hz := zconv (m + j + 1) ρ h1 (hρ'.trans (hmono (Nat.le_succ _)))
    have e : U (j + 1) - U j = Laurent.cmul (U j) (zk (m + j + 1) - Pi.single 0 1) := by
      rw [U_succ, cmul_sub_right h0 (Uconv j ρ h1 h2) hz (convergesAt_single 0 1 ρ),
        cmul_single_zero_one]
    rw [e, ← Unorm j ρ h1 h2]
    exact (gaussNorm_cmul_le h0 (Uconv j ρ h1 h2) (hz.sub h0 (convergesAt_single 0 1 ρ))).trans
      (mul_le_mul_of_nonneg_left (zsmall _ ρ h1 hρ') (gaussNorm_nonneg h0))
  have Ucauchy : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → UCauchy U ρ := by
    intro ρ h1 h2 e he
    obtain ⟨K₀, -, hK₀⟩ := geom (gaussNorm (U 0) ρ) (gaussNorm_nonneg (pos ρ h1)) e he 0
    refine ⟨K₀, fun j hj n => ?_⟩
    have hc : ConvergesAt (U (j + 1) - U j) ρ :=
      (Uconv _ ρ h1 h2).sub (pos ρ h1) (Uconv j ρ h1 h2)
    refine (hc.le_gaussNorm n).trans ((Udiff j ρ h1 h2).trans ?_)
    refine le_trans ?_ (hK₀ j hj)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega)) (gaussNorm_nonneg (pos ρ h1))
  have uconv : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) → ConvergesAt (limSeq U) ρ := fun ρ h1 h2 =>
    (Ucauchy ρ h1 h2).convergesAt_of_eventually (pos ρ h1) (K₁ := 0)
      fun j _ => Uconv j ρ h1 h2
  have Ubound : ∀ j ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      gaussNorm (U j - U 0) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + 2) := by
    intro j ρ h1 h2
    have h0 := pos ρ h1
    have hG := gaussNorm_nonneg (a := U 0) h0
    induction j with
    | zero => rw [sub_self, gaussNorm_zero]; positivity
    | succ j ih =>
      rw [show U (j + 1) - U 0 = (U (j + 1) - U j) + (U j - U 0) by ring]
      refine (gaussNorm_add_le h0 ((Uconv _ ρ h1 h2).sub h0 (Uconv j ρ h1 h2))
        ((Uconv j ρ h1 h2).sub h0 (Uconv 0 ρ h1 h2))).trans (max_le ?_ ih)
      refine (Udiff j ρ h1 h2).trans (mul_le_mul_of_nonneg_left ?_ hG)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have ubound : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      gaussNorm (limSeq U - U 0) ρ ≤ gaussNorm (U 0) ρ * (1 / 2) ^ (m + 2) := by
    intro ρ h1 h2
    refine gaussNorm_le fun n => ?_
    have hlim' : Tendsto (fun j => ‖U j n - U 0 n‖ * ρ ^ n) atTop
        (𝓝 (‖limSeq U n - U 0 n‖ * ρ ^ n)) :=
      ((((Ucauchy ρ h1 h2).tendsto (pos ρ h1) n).sub_const (U 0 n)).norm).mul_const _
    refine le_of_tendsto' hlim' fun j => ?_
    exact (((Uconv j ρ h1 h2).sub (pos ρ h1) (Uconv 0 ρ h1 h2)).le_gaussNorm n).trans
      (Ubound j ρ h1 h2)

  have hU0 : IsUnitOn (U 0) r (t (m + 1)) := by
    rw [U_zero]; exact hwm.cmul hr hm1 (zunit m)
  set N := lowIndex (U 0) r
  have udom : ∀ ρ, r ≤ ρ → ρ ≤ t (m + 1) →
      ‖limSeq U N‖ * ρ ^ N = ‖U 0 N‖ * ρ ^ N ∧
        ∀ m', m' ≠ N → ‖limSeq U m'‖ * ρ ^ m' < ‖limSeq U N‖ * ρ ^ N := by
    intro ρ h1 h2
    have h0 := pos ρ h1
    have hN := unique_dominant_of_lowIndex_eq_highIndex hr hU0.1 hU0.2.1 hU0.2.2 ⟨h1, h2⟩
    have hg : gaussNorm (U 0) ρ = ‖U 0 N‖ * ρ ^ N :=
      le_antisymm (gaussNorm_le fun m' => by
        by_cases hm' : m' = N
        · rw [hm']
        · exact (hN m' hm').le) ((Uconv 0 ρ h1 h2).le_gaussNorm N)
    have hpos : 0 < gaussNorm (U 0) ρ := gaussNorm_pos h0 (Uconv 0 ρ h1 h2) (Une 0)
    have hsmall : gaussNorm (limSeq U - U 0) ρ < ‖U 0 N‖ * ρ ^ N := by
      rw [← hg]
      refine (ubound ρ h1 h2).trans_lt ?_
      have : (1 / 2 : ℝ) ^ (m + 2) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      nlinarith
    exact unique_dominant_of_perturb h0 hN ((uconv ρ h1 h2).sub h0 (Uconv 0 ρ h1 h2)) hsmall
  have huN : limSeq U N ≠ 0 := by
    intro h0
    have := (udom r le_rfl hm1).1
    rw [h0, norm_zero, zero_mul] at this
    have hpos := norm_pos_iff.2 (ne_zero_of_mem_domSet hr (Uconv 0 r le_rfl hm1) (Une 0)
      (lowIndex_mem hr (Uconv 0 r le_rfl hm1) (Une 0)))
    have := zpow_pos hr N
    nlinarith
  have hu : IsUnitOn (limSeq U) r (t (m + 1)) := by
    refine ⟨fun ρ hρ => uconv ρ hρ.1 hρ.2, fun h0 => huN (by rw [h0]; rfl), ?_⟩
    have e1 := (low_high_of_unique_dominant hr (uconv r le_rfl hm1) (udom r le_rfl hm1).2 huN).1
    have e2 := (low_high_of_unique_dominant (pos _ hm1) (uconv _ hm1 le_rfl)
      (udom _ hm1 le_rfl).2 huN).2
    rw [e1, e2]
  refine ⟨limSeq U, hu, ?_⟩

  have hcr : ConvergesAt (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r :=
    (Dlimconv r le_rfl (hm1.trans_lt (ht1 _))).sub hr ((hd m r hr).cmul hr (uconv r le_rfl hm1))
  have hbound : ∀ e > (0 : ℝ), gaussNorm (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r ≤ e := by
    intro e he
    have hG : 0 < 1 + gaussNorm (d m) r := by linarith [gaussNorm_nonneg (a := d m) hr]
    obtain ⟨K₁, hK₁⟩ := (Dcauchy 0 r le_rfl (hrt 0)).gaussNorm_sub_le hr he
    obtain ⟨K₂, hK₂⟩ := (Ucauchy r le_rfl hm1).gaussNorm_sub_le hr (div_pos he hG)
    set j := max K₁ K₂
    have e1 : limSeq Dk - Laurent.cmul (d m) (limSeq U) =
        (limSeq Dk - Dk (m + j + 1)) + Laurent.cmul (d m) (U j - limSeq U) := by
      rw [cmul_sub_right hr (hd m r hr) (Uconv j r le_rfl hm1) (uconv r le_rfl hm1), DU j]
      ring
    rw [e1]
    refine (gaussNorm_add_le hr ((Dlimconv r le_rfl (hm1.trans_lt (ht1 _))).sub hr
      (Dconv _ r le_rfl (hm1.trans_lt (ht1 _))))
      ((hd m r hr).cmul hr ((Uconv j r le_rfl hm1).sub hr (uconv r le_rfl hm1)))).trans
      (max_le (hK₁ _ (by omega)) ?_)
    refine (gaussNorm_cmul_le hr (hd m r hr) ((Uconv j r le_rfl hm1).sub hr
      (uconv r le_rfl hm1))).trans ?_
    rw [gaussNorm_sub_comm]
    calc gaussNorm (d m) r * gaussNorm (limSeq U - U j) r
        ≤ (1 + gaussNorm (d m) r) * (e / (1 + gaussNorm (d m) r)) :=
          mul_le_mul (by linarith) (hK₂ j (le_max_right _ _)) (gaussNorm_nonneg hr) hG.le
      _ = e := mul_div_cancel₀ _ hG.ne'
  have h0 : gaussNorm (limSeq Dk - Laurent.cmul (d m) (limSeq U)) r = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun e he => by simpa using hbound e he)
      (gaussNorm_nonneg hr)
  exact sub_eq_zero.1 ((gaussNorm_eq_zero_iff hr hcr).1 h0)

end Main

end Laurent

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Polynomial

set_option linter.unusedSectionVars false

theorem exists_next_radius {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {a b ε : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (hb1 : b < 1) (hε : 0 < ε) :
    ∃ s : ℝ, ∃ n : ℕ, max a b ≤ s ∧ s < 1 ∧ q ≤ s ^ n ∧ (a / s) ^ n ≤ ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hq) ha1
  have hlim : Tendsto (fun s : ℝ => s ^ n) (𝓝[<] 1) (𝓝 1) := by
    simpa using ((continuous_pow n).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmax : max a b < 1 := max_lt ha1 hb1
  have hI : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Set.Ioo (max a b) 1 := Ioo_mem_nhdsLT hmax
  obtain ⟨s, hs1, hs2⟩ := (hI.and (hlim.eventually (lt_mem_nhds hq1))).exists
  have hs0 : 0 < s := ha.trans_le ((le_max_left _ _).trans hs1.1.le)
  refine ⟨s, n, hs1.1.le, hs1.2, hs2.le, ?_⟩
  rw [div_pow, div_le_iff₀ (pow_pos hs0 n)]
  calc a ^ n ≤ ε * q := hn.le
    _ ≤ ε * s ^ n := mul_le_mul_of_nonneg_left hs2.le hε.le

theorem exists_radii {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ (t : ℕ → ℝ) (n₀ : ℕ → ℕ), t 0 = r ∧ Monotone t ∧ (∀ k, 0 < t k ∧ t k < 1) ∧
      (∀ ρ < 1, ∃ k, ρ ≤ t k) ∧ (∀ k, q ≤ t (k + 1) ^ n₀ k) ∧
      ∀ k, (t k / t (k + 1)) ^ n₀ k ≤ (1 / 2) ^ (k + 1) := by
  have next : ∀ (k : ℕ) (x : {x : ℝ // 0 < x ∧ x < 1}), ∃ y : {x : ℝ // 0 < x ∧ x < 1},
      ∃ n : ℕ, max x.1 (1 - 1 / ((k : ℝ) + 2)) ≤ y.1 ∧ q ≤ y.1 ^ n ∧
        (x.1 / y.1) ^ n ≤ (1 / 2) ^ (k + 1) := by
    intro k x
    have hb : 1 - 1 / ((k : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((k : ℝ) + 2) := by positivity
      linarith
    obtain ⟨s, n, h1, h2, h3, h4⟩ := exists_next_radius hq hq1 x.2.1 x.2.2 hb
      (by positivity : (0 : ℝ) < (1 / 2) ^ (k + 1))
    exact ⟨⟨s, x.2.1.trans_le ((le_max_left _ _).trans h1), h2⟩, n, h1, h3, h4⟩
  choose y n hy using next
  let T : ℕ → {x : ℝ // 0 < x ∧ x < 1} := fun k => Nat.rec ⟨r, hr, hr1⟩ (fun k x => y k x) k
  have hT : ∀ k, T (k + 1) = y k (T k) := fun k => rfl
  refine ⟨fun k => (T k).1, fun k => n k (T k), rfl, ?_, fun k => (T k).2, ?_, fun k => ?_,
    fun k => ?_⟩
  · refine monotone_nat_of_le_succ fun k => ?_
    rw [hT]; exact (le_max_left _ _).trans (hy k (T k)).1
  · intro ρ hρ
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - ρ))
    refine ⟨k + 1, ?_⟩
    have h1 := (le_max_right _ _).trans (hy k (T k)).1
    rw [← hT] at h1
    have hpos : 0 < 1 - ρ := by linarith
    have : 1 / ((k : ℝ) + 2) < 1 - ρ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hk
      nlinarith
    linarith
  · show q ≤ (T (k + 1)).1 ^ n k (T k)
    rw [hT]; exact (hy k (T k)).2.1
  · show ((T k).1 / (T (k + 1)).1) ^ n k (T k) ≤ _
    rw [hT]; exact (hy k (T k)).2.2

namespace AnnulusRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem convergesAt_polySeq (p : K[X]) (ρ : ℝ) : ConvergesAt (polySeq p) ρ := by
  refine convergesAt_of_support (A := 0) (B := p.natDegree) (fun n hn => ?_) ρ
  simp only [polySeq]
  rcases hn with hn | hn
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem polySeq_ne_zero {p : K[X]} (hp : p ≠ 0) : polySeq p ≠ 0 := by
  intro h
  apply hp
  ext i
  have := congrFun h (i : ℤ)
  simpa [polySeq] using this

theorem restrict_aeval_T {I J : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)] [Fact (∃ ρ ∈ J, 0 < ρ)]
    (hJ : J ⊆ I) (p : K[X]) :
    restrict hJ (aeval (T : AnnulusRing K I) p) = aeval (T : AnnulusRing K J) p := by
  rw [← Polynomial.aeval_algHom_apply]; rfl

end AnnulusRing

namespace AnnulusRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option maxHeartbeats 2000000 in

theorem span_pair_isPrincipal_Ico [IsDiscreteValuationRing (normInteger K)]
    (hloc : ∀ (α β : ℝ) [Fact (∃ ρ ∈ Set.Icc α β, 0 < ρ)], 0 < α → α ≤ β →
      ∀ f g : AnnulusRing K (Set.Icc α β), ∃ p : K[X],
        Ideal.span ({f, g} : Set (AnnulusRing K (Set.Icc α β))) = Ideal.span {aeval T p})
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) [Fact (∃ ρ ∈ Set.Ico r 1, 0 < ρ)]
    (f g : AnnulusRing K (Set.Ico r 1)) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ D : AnnulusRing K (Set.Ico r 1),
      Ideal.span ({f, g} : Set (AnnulusRing K (Set.Ico r 1))) = Ideal.span {D} := by
  obtain ⟨q, hq, hq1, hbig⟩ := exists_q_of_isDiscreteValuationRing (K := K)
  obtain ⟨t, n₀, ht0, hmono, ht01, htlim, hn₀, hβ⟩ := exists_radii hq hq1 hr hr1
  have hrt : ∀ k, r ≤ t k := fun k => ht0 ▸ hmono (Nat.zero_le k)
  have ht1 : ∀ k, t k < 1 := fun k => (ht01 k).2
  haveI hinst : ∀ k, Fact (∃ ρ ∈ Set.Icc r (t (k + 1)), 0 < ρ) := fun k =>
    ⟨⟨r, ⟨le_rfl, hrt _⟩, hr⟩⟩
  have hsub : ∀ k, Set.Icc r (t (k + 1)) ⊆ Set.Ico r 1 := fun k ρ hρ =>
    ⟨hρ.1, hρ.2.trans_lt (ht1 _)⟩

  have hgen := fun k => hloc r (t (k + 1)) hr (hrt _) (restrict (hsub k) f) (restrict (hsub k) g)
  choose p hp using hgen
  have hf0 : f.coeff ≠ 0 := fun e => hf (AnnulusRing.ext e)
  have hg0 : g.coeff ≠ 0 := fun e => hg (AnnulusRing.ext e)
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k hpk
    have h1 : restrict (hsub k) f ∈ Ideal.span ({restrict (hsub k) f, restrict (hsub k) g} :
        Set (AnnulusRing K (Set.Icc r (t (k + 1))))) := Ideal.subset_span (by simp)
    rw [hp k, hpk, map_zero, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at h1
    exact hf0 (congrArg AnnulusRing.coeff h1)

  have hv : ∀ k, ∃ v, IsUnitOn v r (t (k + 1)) ∧ cmul (polySeq (p k)) v = polySeq (p (k + 1)) := by
    intro k
    have hJ : Set.Icc r (t (k + 1)) ⊆ Set.Icc r (t (k + 1 + 1)) :=
      Set.Icc_subset_Icc le_rfl (hmono (Nat.le_succ _))
    have e1 := hp (k + 1)
    have e2 := congrArg (Ideal.map (restrict hJ)) e1
    rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton,
      restrict_aeval_T] at e2
    have e3 : restrict hJ (restrict (hsub (k + 1)) f) = restrict (hsub k) f := rfl
    have e4 : restrict hJ (restrict (hsub (k + 1)) g) = restrict (hsub k) g := rfl
    rw [e3, e4, hp k, Ideal.span_singleton_eq_span_singleton] at e2
    obtain ⟨u, hu⟩ := e2
    refine ⟨(u : AnnulusRing K (Set.Icc r (t (k + 1)))).coeff, ⟨fun ρ hρ =>
      (u : AnnulusRing K _).convergesAt hρ (hr.trans_le hρ.1), fun h0 => ?_,
      lowIndex_eq_highIndex_of_isUnit hr u.isUnit⟩, ?_⟩
    · exact u.ne_zero (AnnulusRing.ext h0)
    · have := congrArg AnnulusRing.coeff hu
      rw [coeff_mul, coeff_aeval_alt, coeff_aeval_alt] at this
      exact this
  obtain ⟨D, hDc, hDu⟩ := exists_divisor hr ht0 hmono ht1 htlim hq hbig hn₀ hβ
    (fun k ρ _ => convergesAt_polySeq (p k) ρ) (fun k => polySeq_ne_zero (hp0 k)) hv
  let eD : AnnulusRing K (Set.Ico r 1) := ⟨D, fun ρ hρ _ => hDc ρ hρ.1 hρ.2⟩
  have hD0 : D ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hDu'⟩ := hDu 0
    exact cmul_ne_zero hr (convergesAt_polySeq _ r) (hu.1 r ⟨le_rfl, hrt _⟩)
      (polySeq_ne_zero (hp0 0)) hu.2.1 (hDu'.symm.trans h0)

  have hunit : ∀ m, ∃ w : AnnulusRing K (Set.Icc r (t (m + 1))), IsUnit w ∧
      restrict (hsub m) eD = aeval T (p m) * w := by
    intro m
    obtain ⟨u, hu, hDu'⟩ := hDu m
    refine ⟨⟨u, fun ρ hρ _ => hu.1 ρ hρ⟩, isUnit_of_lowIndex_eq_highIndex hr _
      (fun h0 => hu.2.1 (congrArg AnnulusRing.coeff h0)) hu.2.2, ?_⟩
    ext n
    rw [coeff_mul, coeff_aeval_alt]
    exact congrFun hDu' n

  have hdiv : ∀ x : AnnulusRing K (Set.Ico r 1),
      (∀ m, restrict (hsub m) x ∈ Ideal.span ({aeval T (p m)} :
        Set (AnnulusRing K (Set.Icc r (t (m + 1)))))) →
      ∃ y : AnnulusRing K (Set.Ico r 1), x = eD * y := by
    intro x hx
    have loc : ∀ m, ∃ h : ℤ → K, (∀ ρ ∈ Set.Icc r (t (m + 1)), ConvergesAt h ρ) ∧
        cmul D h = x.coeff := by
      intro m
      obtain ⟨w, hw, hwD⟩ := hunit m
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (hx m)
      obtain ⟨wi, hwi⟩ := hw.exists_right_inv
      refine ⟨(wi * z).coeff, fun ρ hρ => (wi * z).convergesAt hρ (hr.trans_le hρ.1), ?_⟩
      have : restrict (hsub m) eD * (wi * z) = restrict (hsub m) x := by
        rw [hwD, ← hz]; linear_combination (aeval T (p m) * z) * hwi
      exact congrArg AnnulusRing.coeff this
    choose h hh hhD using loc
    have hall : ∀ m, h m = h 0 := by
      intro m
      have hc : ∀ ρ ∈ Set.Icc r (t 1), ConvergesAt (h m) ρ := fun ρ hρ =>
        hh m ρ ⟨hρ.1, hρ.2.trans (hmono (by omega))⟩
      by_contra hne
      have hsub0 : h m - h 0 ≠ 0 := sub_ne_zero.2 hne
      have hzero : cmul D (h m - h 0) = 0 := by
        haveI : Fact (∃ ρ ∈ Set.Icc r (t 1), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrt _⟩, hr⟩⟩
        have e := cmul_add hr (hDc r le_rfl hr1) (hc r ⟨le_rfl, hrt _⟩)
          ((hh 0 r ⟨le_rfl, hrt _⟩).neg)
        rw [← sub_eq_add_neg, cmul_neg, hhD m, hhD 0, ← sub_eq_add_neg, sub_self] at e
        exact e
      exact cmul_ne_zero hr (hDc r le_rfl hr1) ((hc r ⟨le_rfl, hrt _⟩).sub hr
        (hh 0 r ⟨le_rfl, hrt _⟩)) hD0 hsub0 hzero
    refine ⟨⟨h 0, fun ρ hρ hρ0 => ?_⟩, AnnulusRing.ext ?_⟩
    · obtain ⟨k, hk⟩ := htlim ρ hρ.2
      rw [← hall k]
      exact hh k ρ ⟨hρ.1, hk.trans (hmono (Nat.le_succ k))⟩
    · exact (hhD 0).symm
  have memf : ∀ m, restrict (hsub m) f ∈ Ideal.span ({aeval T (p m)} :
      Set (AnnulusRing K (Set.Icc r (t (m + 1))))) := fun m => by
    rw [← hp m]; exact Ideal.subset_span (by simp)
  have memg : ∀ m, restrict (hsub m) g ∈ Ideal.span ({aeval T (p m)} :
      Set (AnnulusRing K (Set.Icc r (t (m + 1))))) := fun m => by
    rw [← hp m]; exact Ideal.subset_span (by simp)
  obtain ⟨f', hf'⟩ := hdiv f memf
  obtain ⟨g', hg'⟩ := hdiv g memg

  have hloc' : ∀ k, ∃ a b : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ t (k + 1) → ConvergesAt a ρ ∧
      ConvergesAt b ρ) ∧ cmul a f'.coeff + cmul b g'.coeff = Pi.single 0 1 := by
    intro k
    have hmem : aeval T (p k) ∈ Ideal.span ({restrict (hsub k) f, restrict (hsub k) g} :
        Set (AnnulusRing K (Set.Icc r (t (k + 1))))) := by
      rw [hp k]; exact Ideal.subset_span rfl
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hmem
    obtain ⟨w, hw, hwD⟩ := hunit k
    have hDne : restrict (hsub k) eD ≠ 0 := fun h0 => hD0 (congrArg AnnulusRing.coeff h0)
    have key : restrict (hsub k) eD * (w * α * restrict (hsub k) f' +
        w * β * restrict (hsub k) g' - 1) = 0 := by
      have e1 : restrict (hsub k) f = restrict (hsub k) eD * restrict (hsub k) f' := by
        rw [hf', map_mul]
      have e2 : restrict (hsub k) g = restrict (hsub k) eD * restrict (hsub k) g' := by
        rw [hg', map_mul]
      rw [e1, e2] at hαβ
      linear_combination w * hαβ - hwD
    rcases mul_eq_zero.1 key with h0 | h0
    · exact absurd h0 hDne
    refine ⟨(w * α).coeff, (w * β).coeff, fun ρ h1 h2 => ⟨(w * α).convergesAt ⟨h1, h2⟩
      (hr.trans_le h1), (w * β).convergesAt ⟨h1, h2⟩ (hr.trans_le h1)⟩, ?_⟩
    have := congrArg AnnulusRing.coeff (sub_eq_zero.1 h0)
    rw [coeff_add, coeff_mul, coeff_mul] at this
    exact this
  obtain ⟨a, b, hab, hid⟩ := mittag_leffler (s := fun k => t (k + 1)) hr (hrt 1)
    (fun i j hij => hmono (Nat.add_le_add_right hij 1))
    (fun k => ht1 _) (fun ρ hρ => let ⟨k, hk⟩ := htlim ρ hρ; ⟨k, hk.trans (hmono (Nat.le_succ k))⟩)
    (fun ρ h1 h2 => f'.convergesAt ⟨h1, h2⟩ (hr.trans_le h1))
    (fun ρ h1 h2 => g'.convergesAt ⟨h1, h2⟩ (hr.trans_le h1)) hloc'
  let ea : AnnulusRing K (Set.Ico r 1) := ⟨a, fun ρ hρ _ => (hab ρ hρ.1 hρ.2).1⟩
  let eb : AnnulusRing K (Set.Ico r 1) := ⟨b, fun ρ hρ _ => (hab ρ hρ.1 hρ.2).2⟩
  have hone : ea * f' + eb * g' = 1 := AnnulusRing.ext hid
  refine ⟨eD, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.mem_span_singleton'.2 ⟨f', by rw [hf', mul_comm]⟩
    · exact Ideal.mem_span_singleton'.2 ⟨g', by rw [hg', mul_comm]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Ideal.mem_span_pair.2 ⟨ea, eb, ?_⟩
    rw [hf', hg']
    linear_combination eD * hone

end AnnulusRing

namespace AnnulusRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem isBezout_halfOpen [IsDiscreteValuationRing (normInteger K)] {r : ℝ} [Fact (r < 1)]
    (hr : 0 < r) : IsBezout (AnnulusRing.halfOpen K r) := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro f g
  by_cases hf : f = 0
  · subst hf
    rw [show ({0, g} : Set (AnnulusRing.halfOpen K r)) = insert 0 {g} from rfl,
      Ideal.span_insert_zero]
    exact ⟨g, rfl⟩
  by_cases hg : g = 0
  · subst hg
    rw [Set.pair_comm, show ({0, f} : Set (AnnulusRing.halfOpen K r)) = insert 0 {f} from rfl,
      Ideal.span_insert_zero]
    exact ⟨f, rfl⟩
  obtain ⟨D, hD⟩ := span_pair_isPrincipal_Ico
    (fun α β _ hα _ f g => exists_span_eq_aeval hα f g) hr Fact.out f g hf hg
  exact ⟨D, hD⟩

end AnnulusRing

namespace Robba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

instance isBezout [IsDiscreteValuationRing (normInteger K)] : IsBezout (Robba K) := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro f g
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
  haveI : Fact (r < 1) := ⟨hr1⟩
  let f₀ : AnnulusRing.halfOpen K r := ⟨f.coeff, fun ρ hρ _ => (hc ρ hρ.1 hρ.2).1⟩
  let g₀ : AnnulusRing.halfOpen K r := ⟨g.coeff, fun ρ hρ _ => (hc ρ hρ.1 hρ.2).2⟩
  obtain ⟨D, hD⟩ := (IsBezout.iff_span_pair_isPrincipal.1
    (AnnulusRing.isBezout_halfOpen (K := K) hr0)) f₀ g₀
  refine ⟨AnnulusRing.toRobba D, ?_⟩
  have e := congrArg (Ideal.map (AnnulusRing.toRobba : AnnulusRing.halfOpen K r →ₐ[K] Robba K)) hD
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton] at e
  have ef : AnnulusRing.toRobba f₀ = f := rfl
  have eg : AnnulusRing.toRobba g₀ = g := rfl
  rw [ef, eg] at e
  exact e

end Robba

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Robba

variable (K) in

def amiceSet : Set (ℤ → K) :=
  {a | BddAbove (Set.range fun n => ‖a n‖) ∧ Tendsto (fun n : ℕ => a (-(n : ℤ))) atTop (𝓝 0)}

def norm1 (f : Robba K) : ℝ := ⨆ n, ‖f.coeff n‖

theorem gaussNorm_nonneg_alt (f : Robba K) : 0 ≤ norm1 f := Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_coeff_le_norm1 {f : Robba K} (hf : f ∈ bounded K) (n : ℤ) : ‖f.coeff n‖ ≤ norm1 f :=
  le_ciSup hf n

theorem tendsto_gaussNorm_norm1 {f : Robba K} (hf : f ∈ bounded K) :
    Tendsto (fun ρ => gaussNorm f.coeff ρ) (𝓝[<] 1) (𝓝 (norm1 f)) := by
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f f
  have hI : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo r 1 := Ioo_mem_nhdsLT hr1
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
  ·
    obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hx
    have hlim : Tendsto (fun ρ : ℝ => ‖f.coeff n‖ * ρ ^ n) (𝓝[<] 1) (𝓝 (‖f.coeff n‖ * 1 ^ n)) :=
      ((continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero)).tendsto.const_mul _).mono_left
        nhdsWithin_le_nhds
    rw [one_zpow, mul_one] at hlim
    filter_upwards [hI, hlim.eventually (lt_mem_nhds hn)] with ρ hρ h1
    exact h1.trans_le ((hc ρ hρ.1.le hρ.2).1.le_gaussNorm n)
  ·
    have hM : norm1 f < x := hx
    set ε := (x - norm1 f) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    have hF := (hc r le_rfl hr1).1.finite_le hε
    have hev : ∀ n ∈ hF.toFinset, ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ‖f.coeff n‖ * ρ ^ n < norm1 f + ε := by
      intro n _
      have hlim : Tendsto (fun ρ : ℝ => ‖f.coeff n‖ * ρ ^ n) (𝓝[<] 1)
          (𝓝 (‖f.coeff n‖ * 1 ^ n)) :=
        ((continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero)).tendsto.const_mul _).mono_left
          nhdsWithin_le_nhds
      rw [one_zpow, mul_one] at hlim
      exact hlim.eventually (gt_mem_nhds (lt_of_le_of_lt (norm_coeff_le_norm1 hf n)
        (by linarith)))
    have hall := (Finset.eventually_all hF.toFinset).2 hev
    filter_upwards [hI, hall] with ρ hρ hfin
    have hρ0 : 0 < ρ := hr0.trans hρ.1
    refine lt_of_le_of_lt (gaussNorm_le fun n => ?_) (by linarith : norm1 f + ε < x)
    by_cases hn : n ∈ hF.toFinset
    · exact (hfin n hn).le
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
      rcases le_or_gt 0 n with h0 | h0
      · calc ‖f.coeff n‖ * ρ ^ n ≤ ‖f.coeff n‖ * 1 :=
              mul_le_mul_of_nonneg_left (zpow_le_one₀ hρ0 hρ.2.le h0) (norm_nonneg _)
          _ ≤ norm1 f + ε := by rw [mul_one]; linarith [norm_coeff_le_norm1 hf n]
      · have : ρ ^ n ≤ r ^ n := by
          rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
            show r ^ n = (r ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
          exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (by omega) hr0.le hρ.1.le)
        calc ‖f.coeff n‖ * ρ ^ n ≤ ‖f.coeff n‖ * r ^ n :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ ≤ ε := hn.le
          _ ≤ norm1 f + ε := by linarith [gaussNorm_nonneg_alt f]

theorem gaussNorm_mul_alt {f g : Robba K} (hf : f ∈ bounded K) (hg : g ∈ bounded K) :
    norm1 (f * g) = norm1 f * norm1 g := by
  by_cases hf0 : f.coeff = 0
  · have : f = 0 := Robba.ext hf0
    subst this; simp [norm1]
  by_cases hg0 : g.coeff = 0
  · have : g = 0 := Robba.ext hg0
    subst this; simp [norm1]
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
  have hI : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo r 1 := Ioo_mem_nhdsLT hr1
  have h1 := tendsto_gaussNorm_norm1 ((bounded K).mul_mem hf hg)
  have h2 := (tendsto_gaussNorm_norm1 hf).mul (tendsto_gaussNorm_norm1 hg)
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [hI] with ρ hρ
  exact (gaussNorm_cmul (hr0.trans hρ.1) (hc ρ hρ.1.le hρ.2).1 (hc ρ hρ.1.le hρ.2).2 hf0 hg0).symm

theorem gaussNorm_add_le_max_alt {f g : Robba K} (hf : f ∈ bounded K) (hg : g ∈ bounded K) :
    norm1 (f + g) ≤ max (norm1 f) (norm1 g) :=
  ciSup_le fun n => (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_coeff_le_norm1 hf n) (norm_coeff_le_norm1 hg n))

theorem gaussNorm_eq_zero_iff_alt {f : Robba K} (hf : f ∈ bounded K) : norm1 f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext n
    have := norm_coeff_le_norm1 hf n
    rw [h] at this
    simpa using le_antisymm this (norm_nonneg _)
  · rintro rfl; simp [norm1]

theorem exists_norm1_eq [IsDiscreteValuationRing (normInteger K)] {f : Robba K}
    (hf : f ∈ bounded K) : ∃ n, norm1 f = ‖f.coeff n‖ := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_le_mul_of_lt (K := K)
  by_cases h0 : norm1 f = 0
  · exact ⟨0, by rw [h0, ((gaussNorm_eq_zero_iff_alt hf).1 h0)]; simp⟩
  have hpos : 0 < norm1 f := lt_of_le_of_ne (gaussNorm_nonneg_alt f) (Ne.symm h0)
  have hlt : q * norm1 f < norm1 f := by nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_lt_of_lt_ciSup hlt
  refine ⟨n₁, le_antisymm (ciSup_le fun n => not_lt.1 fun hn => ?_) (norm_coeff_le_norm1 hf n₁)⟩
  have := hq _ _ hn
  have := norm_coeff_le_norm1 hf n
  nlinarith [norm_nonneg (f.coeff n₁)]

end Robba

end GroundTheory.PAdicHodge
end
end
