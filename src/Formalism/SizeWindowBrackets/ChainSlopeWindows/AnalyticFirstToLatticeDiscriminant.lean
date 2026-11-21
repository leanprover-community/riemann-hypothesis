import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PrimeCongruenceConditions
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PBrDiv
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SecondPriceSumWeightsUncovered
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsOrthonormalFrameComplement
import Formalism.SizeWindowBrackets.GrowthBracketBoundOfSizeWindows
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
import Formalism.SizeWindowBrackets.ChainSlopeWindows.CorollaryModelSideCondition
import Formalism.SizeWindowBrackets.SSmall
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LocalizationStructureHolds
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn

section
open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.CosetIndexLemmas

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

open Formalism.LFunctionChainParameters.DeficitSplitLemmas in
theorem rounding_rd_holds : RoundingRd := by
  classical
  intro ι W pr l sg sg' R X'' g₁ g₂ T hl hunit h1 h0 hR hX hg1 hg2 hT

  have s1 : ∑ w ∈ W, 2 * l w * (sg w - sg' w) ≤ ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w := by
    rw [← Finset.sum_filter_add_sum_filter_not W (fun w => pr w ∈ R)]
    have hA : ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w * (sg w - sg' w)
        ≤ ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w := by
      refine Finset.sum_le_sum fun w hw => ?_
      have hw' := (Finset.mem_filter.1 hw).1
      nlinarith [hl w hw', h1 w hw']
    have hB : ∑ w ∈ W.filter (fun w => ¬ pr w ∈ R), 2 * l w * (sg w - sg' w) ≤ 0 := by
      refine Finset.sum_nonpos fun w hw => ?_
      have hw' := Finset.mem_filter.1 hw
      nlinarith [hl w hw'.1, h0 w hw'.1 hw'.2]
    linarith

  have s2 : ∑ w ∈ W.filter (fun w => pr w ∈ R), 2 * l w = ∑ p ∈ R, 2 * Real.log p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := W.filter (fun w => pr w ∈ R)) (t := R) (g := pr)
      (fun w hw => (Finset.mem_filter.1 hw).2)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hunit p hp, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, _⟩, he⟩; exact ⟨hw, he⟩
    · rintro ⟨hw, he⟩; exact ⟨⟨hw, he ▸ hp⟩, he⟩

  have s3 : ∑ p ∈ R, 2 * Real.log p ≤ (2 * Real.log 4 + 6) * X'' := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun p : ℕ => (p : ℝ) ≤ X'')]
    have hA : ∑ p ∈ R.filter (fun p : ℕ => (p : ℝ) ≤ X''), 2 * Real.log p ≤ 2 * (Real.log 4 * X'') := by
      rw [← Finset.mul_sum]
      have := theta_finite X'' (R.filter (fun p : ℕ => (p : ℝ) ≤ X'')) hX (fun p hp =>
        ⟨(hR p (Finset.mem_filter.1 hp).1).1, (Finset.mem_filter.1 hp).2⟩)
      linarith
    have hnn : ∀ j : ℕ, 0 ≤ Real.log (j : ℝ) := fun j => Real.log_natCast_nonneg j
    have hB : ∑ p ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X''), 2 * Real.log p
        ≤ 2 * Real.log g₁ + 2 * Real.log g₂ + 2 * Real.log T := by
      have hle : ∀ p ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X''), 2 * Real.log (p : ℝ)
          ≤ (if p = g₁ then 2 * Real.log (g₁ : ℝ) else 0) + (if p = g₂ then 2 * Real.log (g₂ : ℝ) else 0)
            + (if p = T then 2 * Real.log (T : ℝ) else 0) := by
        intro p hp
        have hp' := Finset.mem_filter.1 hp
        have nn : ∀ (P : Prop) [Decidable P] (c : ℝ), 0 ≤ c → 0 ≤ (if P then c else 0) := by
          intro P _ c hc; split_ifs <;> [exact hc; exact le_refl _]
        have n1 := nn (p = g₁) (2 * Real.log (g₁ : ℝ)) (by linarith [hnn g₁])
        have n2 := nn (p = g₂) (2 * Real.log (g₂ : ℝ)) (by linarith [hnn g₂])
        have n3 := nn (p = T) (2 * Real.log (T : ℝ)) (by linarith [hnn T])
        rcases (hR p hp'.1).2 with h | h | h | h
        · exact absurd h hp'.2
        · have e : (if p = g₁ then 2 * Real.log (g₁ : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
        · have e : (if p = g₂ then 2 * Real.log (g₂ : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
        · have e : (if p = T then 2 * Real.log (T : ℝ) else 0) = 2 * Real.log (p : ℝ) := by rw [if_pos h, h]
          linarith
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
      have m1 : ∀ (c : ℝ) (P : Prop) [Decidable P], 0 ≤ c → (if P then c else 0) ≤ c := by
        intro c P _ hc; split_ifs <;> [exact le_refl _; exact hc]
      have := m1 (2 * Real.log (g₁ : ℝ)) (g₁ ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn g₁])
      have := m1 (2 * Real.log (g₂ : ℝ)) (g₂ ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn g₂])
      have := m1 (2 * Real.log (T : ℝ)) (T ∈ R.filter (fun p : ℕ => ¬ (p : ℝ) ≤ X'')) (by linarith [hnn T])
      linarith
    linarith
  linarith

open Filter Asymptotics in
theorem ev_exp (A B κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x, x₀ ≤ x → A * x ^ B ≤ Real.exp (κ * x ^ δ) := by
  have hc : 0 < κ / (2 * (|B| + 1)) := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  have h2 := (tendsto_rpow_atTop hδ).eventually_ge_atTop (2 * |A| / κ)
  obtain ⟨x₀, hx₀⟩ := (hb.and h2).exists_forall_of_atTop
  refine ⟨max x₀ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hxd : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0, abs_of_nonneg hxd] at h1
  have hA : |A| ≤ κ * x ^ δ / 2 := by
    rw [div_le_iff₀ hκ] at h2; linarith
  have hB : B * Real.log x ≤ κ * x ^ δ / 2 := by
    have hB1 : B * Real.log x ≤ |B| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self B) hl0
    have hB2 : |B| * Real.log x ≤ (|B| + 1) * (κ / (2 * (|B| + 1)) * x ^ δ) := by
      apply mul_le_mul (by linarith) h1 hl0 (by positivity)
    have hB3 : (|B| + 1) * (κ / (2 * (|B| + 1)) * x ^ δ) = κ * x ^ δ / 2 := by
      field_simp
    linarith
  have hxB : x ^ B = Real.exp (B * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hxB0 : 0 < x ^ B := Real.rpow_pos_of_pos hx0 _
  calc A * x ^ B ≤ |A| * x ^ B := mul_le_mul_of_nonneg_right (le_abs_self A) hxB0.le
    _ ≤ Real.exp |A| * x ^ B := by
        apply mul_le_mul_of_nonneg_right _ hxB0.le
        have := Real.add_one_le_exp |A|; linarith
    _ = Real.exp (|A| + B * Real.log x) := by rw [hxB, Real.exp_add]
    _ ≤ Real.exp (κ * x ^ δ) := Real.exp_le_exp.2 (by linarith)

theorem sigma_window_eventual : SgWindowEv := by
  intro ε cH C1 e hε hC1
  obtain ⟨x1, hx1, h1⟩ := ev_exp (8 * (C1 + 1) ^ 2) (e + 2 * cH) (1 / 2) ε (by norm_num) hε
  obtain ⟨x2, hx2, h2⟩ := ev_exp 16 cH 1 (ε / 8) one_pos (by positivity)
  refine ⟨max x1 x2, ?_⟩
  intro x f m T de e0 hx hf hm hT hlT hde he0
  have hxa := h1 x (le_trans (le_max_left _ _) hx)
  have hxb := h2 x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith [le_trans (le_max_left x1 x2) hx]
  have hS : 0 < x ^ (-cH) := Real.rpow_pos_of_pos hx0 _
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _

  have hTexp : Real.exp (1 / 2 * x ^ ε) ≤ T := by
    rw [← Real.le_log_iff_exp_le hT]
    nlinarith
  have hEpos : 0 < Real.exp (1 / 2 * x ^ ε) := Real.exp_pos _

  set y := x ^ (-cH) / (2 * (C1 + 1)) with hy
  have hy0 : 0 < y := by positivity
  have hxE : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ (e + 2 * cH) = x ^ e / (x ^ (-cH)) ^ 2 := by
    rw [Real.rpow_add hx0, ← Real.rpow_natCast (x ^ (-cH)) 2, ← Real.rpow_mul hx0.le, div_eq_mul_inv,
      ← Real.rpow_neg hx0.le]
    congr 2; push_cast; ring
  have hde2 : de ≤ y ^ 2 := by
    have a1 : 2 * f / T ≤ 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) := by
      calc 2 * f / T ≤ 2 * x ^ e / T := by gcongr
        _ ≤ 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) := by gcongr
    have a2 : 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) ≤ y ^ 2 := by
      rw [div_le_iff₀ hEpos]
      have : y ^ 2 * (8 * (C1 + 1) ^ 2 * x ^ (e + 2 * cH)) = 2 * x ^ e := by
        rw [hsplit, hy]; field_simp; ring
      calc 2 * x ^ e = y ^ 2 * (8 * (C1 + 1) ^ 2 * x ^ (e + 2 * cH)) := this.symm
        _ ≤ y ^ 2 * Real.exp (1 / 2 * x ^ ε) := mul_le_mul_of_nonneg_left hxa (by positivity)
    linarith
  have hsq : Real.sqrt de ≤ y := Real.sqrt_le_iff.2 ⟨hy0.le, hde2⟩
  have p1 : C1 * Real.sqrt de ≤ x ^ (-cH) / 2 := by
    calc C1 * Real.sqrt de ≤ C1 * y := mul_le_mul_of_nonneg_left hsq hC1
      _ ≤ (C1 + 1) * y := by nlinarith
      _ = x ^ (-cH) / 2 := by rw [hy]; field_simp

  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]; norm_num
  have p2 : 4 * Real.sqrt (2 * e0) ≤ x ^ (-cH) / 2 := by
    rw [Real.sqrt_mul (by norm_num)]
    have b1 : Real.sqrt 2 * Real.sqrt e0 ≤ 2 * Real.exp (-(x ^ (ε / 8))) :=
      mul_le_mul hs2 he0 (Real.sqrt_nonneg _) (by norm_num)
    have b2 : 16 * Real.exp (-(x ^ (ε / 8))) ≤ x ^ (-cH) := by
      rw [Real.exp_neg, Real.rpow_neg hx0.le]
      have hc0 : 0 < x ^ cH := Real.rpow_pos_of_pos hx0 _
      have he0' : 0 < Real.exp (x ^ (ε / 8)) := Real.exp_pos _
      rw [one_mul] at hxb
      rw [← div_eq_mul_inv, div_le_iff₀ he0', ← div_eq_inv_mul, le_div_iff₀ hc0]
      exact hxb
    linarith
  linarith

open Filter in
theorem deletion_eventual_holds : DelEv := by
  intro ε hε
  obtain ⟨x₀, hx₀⟩ := ((tendsto_rpow_atTop (show 0 < ε / 7 by positivity)).eventually_ge_atTop 6).exists_forall_of_atTop
  refine ⟨x₀, fun x del hx hdel => ?_⟩
  have h6 := hx₀ x hx
  refine hdel.trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp (x ^ (ε / 7))
  norm_num
  linarith

open Formalism.LFunctionChainParameters.LErr in
theorem round_window_eventual : RoundWindowEv := by
  intro ε c hε hc
  obtain ⟨x1, hx1, h1⟩ := ev_exp c ((1 : ℝ) / 2 + ε / 2 + ε) 1 (ε / 3) one_pos (by positivity)
  refine ⟨x1, fun x m n hx hm hn => ?_⟩
  have hxa := h1 x hx
  have hx1' : 1 ≤ x := le_trans hx1 hx
  have hx0 : 0 < x := by linarith
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hX : XppTx x ε n = x * n * Real.exp (x ^ (ε / 3)) := by
    unfold XppTx wppTx bpTx aTx XpTx bTx
    have := Real.exp_pos (x ^ ε)
    have := Real.exp_pos (x ^ (ε / 3))
    have hn0 : 0 < n := by linarith
    field_simp
  rw [hX]
  have hE : 0 < Real.exp (x ^ (ε / 3)) := Real.exp_pos _
  rw [one_mul] at hxa
  calc c * m * x ^ ε ≤ c * x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε := by gcongr
    _ = c * x ^ ((1 : ℝ) / 2 + ε / 2 + ε) := by rw [mul_assoc, ← Real.rpow_add hx0]
    _ ≤ Real.exp (x ^ (ε / 3)) := hxa
    _ ≤ x * n * Real.exp (x ^ (ε / 3)) := by
        have : 1 ≤ x * n := by nlinarith
        nlinarith

end Formalism.LFunctionChainParameters.CosetIndexLemmas
end
end

section
open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LSmall

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem node_sizes_of_windows : NodeSizesOfWindows (H := H) := by
  intro m TT T2 x b b' η κ w'' off bt w ⟨hb, hb', hη, hκ, hx, hoff0, hoff, hw0, hw'', hbt, hsum⟩ ⟨hthick, htop, hthin⟩
  have hκb : 0 ≤ κ * b' := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro u0 j ρ hρ
    by_cases h1 : IsThickAt T2 u0 ρ
    · linarith [(hthick u0 j ρ h1).1]
    by_cases h2 : ∀ t ∈ TT, ρ ≠ topPl t
    · linarith [(hthin u0 j ρ hρ h1 h2).1]
    push Not at h2
    obtain ⟨t, ht, rfl⟩ := h2
    linarith [(htop u0 j t ht).1, (hbt t ht).1]
  · intro u0 j ρ h1
    have := hthick u0 j ρ h1
    exact ⟨this.1, by linarith [this.2]⟩
  · intro u0 j ρ hρ h1
    by_cases h2 : ∀ t ∈ TT, ρ ≠ topPl t
    · linarith [(hthin u0 j ρ hρ h1 h2).2]
    push Not at h2
    obtain ⟨t, ht, rfl⟩ := h2
    linarith [(htop u0 j t ht).2, (hbt t ht).2]

end

theorem window_sizes_explicit : WindowSizesText := by
  intro H _ _ _ TT x b b' η κ off bt hx hb hb' hη hη4 hκ hκ4 hoff hbt
  have hx0 : 0 < x := by linarith
  have hn : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)
  have hq0 : 0 ≤ b' / x := by positivity
  have hq3 : b' / x ≤ b' / 3 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  refine ⟨hb, hb', hη, hκ, hx0, ?_, ?_, by positivity, ?_, hbt, ?_⟩
  · rcases hoff with rfl | rfl
    · exact hq0
    · exact_mod_cast Int.floor_nonneg.2 hq0
  · rcases hoff with rfl | rfl
    · exact le_refl _
    · exact Int.floor_le _
  · apply div_le_div_of_nonneg_left hb'.le hx0
    nlinarith
  · have : κ * b' ≤ 1 / 4 * b' := mul_le_mul_of_nonneg_right hκ4 hb'.le
    linarith

theorem node_sizes_explicit : NodeSizesText := by
  intro H _ _ _ m TT T2 x b b' η κ off bt w h1 h2 h3 h4 h5 h6 h7 h8 h9 hw
  exact node_sizes_of_windows TT T2 x b b' η κ _ off bt w
    (window_sizes_explicit H TT x b b' η κ off bt h1 h2 h3 h4 h5 h6 h7 h8 h9) hw

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

section Conj

open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

lemma cj_apply {m n : Type} (M : Matrix m n ℂ) (i : m) (j : n) : cj M i j = starRingEnd ℂ (M i j) := rfl

lemma cj_cj {m n : Type} (M : Matrix m n ℂ) : cj (cj M) = M := by
  ext i j; simp [cj_apply]

lemma cj_sub {m n : Type} (M N : Matrix m n ℂ) : cj (M - N) = cj M - cj N := by
  ext i j; simp [cj_apply]

section
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

end

end Conj

section Host

open Formalism.LFunctionChainParameters.LHost
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)

lemma hOf_of_coprime {e m : ℕ} (h : m.Coprime (2 ^ (e + 2))) :
    hOf e m = Additive.ofMul (hcl e (ZMod.unitOfCoprime m h)) := dif_pos h

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

lemma sg_ne {H : Type} [AddCommGroup H] : (0 : E0 × H) ≠ sg := by
  intro h
  have := congrArg (fun x : E0 × H => x.1.2) h
  simp [sg] at this

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

lemma odd_iff_cop (e m : ℕ) : Odd m ↔ m.Coprime (2 ^ (e + 2)) := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]

lemma hOf_one (e : ℕ) : hOf e 1 = 0 := by
  rw [hOf_of_coprime (Nat.coprime_one_left _), unitOfCoprime_one]
  rfl

lemma hOf_mul (e : ℕ) {a b : ℕ} (ha : Odd a) (hb : Odd b) : hOf e (a * b) = hOf e a + hOf e b := by
  have ca := (odd_iff_cop e a).1 ha
  have cb := (odd_iff_cop e b).1 hb
  rw [hOf_of_coprime ca, hOf_of_coprime cb, hOf_of_coprime (Nat.Coprime.mul_left ca cb)]
  have : ZMod.unitOfCoprime (a * b) (Nat.Coprime.mul_left ca cb) = ZMod.unitOfCoprime a ca * ZMod.unitOfCoprime b cb := by
    ext; simp
  rw [this]
  rfl

lemma omV_one (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : omV e ψ 1 = 1 := by
  unfold omV
  split_ifs with h1 h2
  · rfl
  · rw [hOf_one]; exact AddChar.map_zero_eq_one ψ
  · exact absurd odd_one h2

lemma omV_mul (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) (a b : ℕ) : omV e ψ (a * b) = omV e ψ a * omV e ψ b := by
  unfold omV
  by_cases h1 : ∀ t : HA e, ψ ((0, 0), t) = 1
  · simp only [if_pos h1, mul_one]
  simp only [if_neg h1]
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · rw [if_pos ha, if_pos hb, if_pos (ha.mul hb), hOf_mul e ha hb, ← AddChar.map_add_eq_mul]
      simp
    · rw [if_neg hb, if_neg (fun h => hb (Nat.odd_mul.1 h).2), mul_zero]
  · rw [if_neg ha, if_neg (fun h => ha (Nat.odd_mul.1 h).1), zero_mul]

lemma laV_one (s : ℂ) (l : ℕ) : laV s l 1 = 1 := by
  unfold laV
  split_ifs
  · rfl
  · simp

lemma laV_mul (s : ℂ) (l a b : ℕ) : laV s l (a * b) = laV s l a * laV s l b := by
  unfold laV
  split_ifs
  · simp
  · rw [Nat.cast_mul, jacobiSym.mul_left]; push_cast; rfl

def prodHom (e q d : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : ℕ →* ℂ where
  toFun m := omV e ψ m * laV (ψ sg) q m * laV (ψ sgc0) d m
  map_one' := by rw [omV_one, laV_one, laV_one]; norm_num
  map_mul' a b := by rw [omV_mul, laV_mul, laV_mul]; ring

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

end Host

end Formalism.LFunctionChainParameters.LSmall
end
end

section
open Complex Filter Topology

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6.Chi8

open Formalism.ZF.ComplexPowerDifferenceIntegral

def chi : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

def g (s : ℂ) (n : ℕ) : ℂ :=
  ((8 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 3 : ℝ) : ℂ) ^ (-s)
    - (((8 * (n : ℝ) + 5 : ℝ) : ℂ) ^ (-s) - ((8 * (n : ℝ) + 7 : ℝ) : ℂ) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, g s n

lemma chi_apply (x : ZMod 8) : chi x = ((ZMod.χ₈ x : ℤ) : ℂ) := rfl

lemma chi_cast (m r : ℕ) : chi ((m * 8 + r : ℕ) : ZMod 8) = chi ((r : ℕ) : ZMod 8) := by
  have h8 : ((8 : ℕ) : ZMod 8) = 0 := ZMod.natCast_self 8
  rw [Nat.cast_add, Nat.cast_mul, h8, mul_zero, zero_add]

lemma chi0 : chi ((0 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi1 : chi ((1 : ℕ) : ZMod 8) = 1 := by
  rw [chi_apply, show ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 by decide]; simp
lemma chi2 : chi ((2 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi3 : chi ((3 : ℕ) : ZMod 8) = -1 := by
  rw [chi_apply, show ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 by decide]; simp
lemma chi4 : chi ((4 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi5 : chi ((5 : ℕ) : ZMod 8) = -1 := by
  rw [chi_apply, show ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 by decide]; simp
lemma chi6 : chi ((6 : ℕ) : ZMod 8) = 0 := by
  rw [chi_apply, show ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 by decide]; simp
lemma chi7 : chi ((7 : ℕ) : ZMod 8) = 1 := by
  rw [chi_apply, show ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 by decide]; simp

def tm (s : ℂ) (n : ℕ) : ℂ := LSeries.term (fun n : ℕ => chi (n : ZMod 8)) s n

lemma tm_zero (s : ℂ) (m r : ℕ) (h : chi ((r : ℕ) : ZMod 8) = 0) : tm s (m * 8 + r) = 0 := by
  unfold tm
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · rw [chi_cast, h, zero_div]

lemma tm_eval (s : ℂ) (m r : ℕ) (hr : 0 < r) :
    tm s (m * 8 + r) = chi ((r : ℕ) : ZMod 8) * ((8 * (m : ℝ) + (r : ℝ) : ℝ) : ℂ) ^ (-s) := by
  unfold tm
  rw [LSeries.term_of_ne_zero (by omega), chi_cast, Complex.cpow_neg, div_eq_mul_inv]
  congr 3
  push_cast
  ring

lemma block (s : ℂ) (m : ℕ) : ∑ r : Fin 8, tm s (m * 8 + (r : ℕ)) = g s m := by
  rw [Fin.sum_univ_eight]
  change tm s (m * 8 + 0) + tm s (m * 8 + 1) + tm s (m * 8 + 2) + tm s (m * 8 + 3) + tm s (m * 8 + 4)
    + tm s (m * 8 + 5) + tm s (m * 8 + 6) + tm s (m * 8 + 7) = g s m
  rw [tm_zero s m 0 chi0, tm_zero s m 2 chi2, tm_zero s m 4 chi4, tm_zero s m 6 chi6,
    tm_eval s m 1 (by norm_num), tm_eval s m 3 (by norm_num), tm_eval s m 5 (by norm_num),
    tm_eval s m 7 (by norm_num), chi1, chi3, chi5, chi7]
  unfold g
  simp only [Nat.cast_ofNat, Nat.cast_one]
  ring

def gr (σ : ℝ) (n : ℕ) : ℝ :=
  (8 * (n : ℝ) + 1) ^ (-σ) - (8 * (n : ℝ) + 3) ^ (-σ) - ((8 * (n : ℝ) + 5) ^ (-σ) - (8 * (n : ℝ) + 7) ^ (-σ))

end Formalism.LFunctionChainParameters.LChain6.Chi8

namespace Formalism.LFunctionChainParameters.LChain6

end Formalism.LFunctionChainParameters.LChain6
end
end

section
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

section Defs
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem concl_transport {T Pl Pl' : Type} (TT : Finset T) (e : T ↪ Pl) (e' : T ↪ Pl') (aP : Pl → ℝ) (aP' : Pl' → ℝ)
    (h : ∀ t, aP (e t) = aP' (e' t)) (muC hu Fo logT logOm m a La B0 Nc xe C0 : ℝ) :
    ThmConcl (TT.map e) aP muC hu Fo logT logOm m a La B0 Nc xe C0 ↔
      ThmConcl (TT.map e') aP' muC hu Fo logT logOm m a La B0 Nc xe C0 := by
  simp [ThmConcl, Finset.sum_map, h, Finset.card_map]

theorem second_conclusion_transport {T Pl Pl' J : Type} [Fintype J] (TT : Finset T) (e : T ↪ Pl) (e' : T ↪ Pl') (aP : Pl → ℝ)
    (aP' : Pl' → ℝ) (h : ∀ t, aP (e t) = aP' (e' t)) (sE : J → ℝ) (lg m B0 C0 : ℝ) :
    TypePrimeCostDeviationBound (TT.map e) aP sE lg m B0 C0 ↔ TypePrimeCostDeviationBound (TT.map e') aP' sE lg m B0 C0 := by
  simp [TypePrimeCostDeviationBound, Finset.sum_map, h]

theorem third_conclusion_transport {T Pl Pl' U : Type} (TT : Finset T) (e : T ↪ Pl) (e' : T ↪ Pl') (aP : U → Pl → ℝ)
    (aP' : U → Pl' → ℝ) (h : ∀ u t, aP u (e t) = aP' u (e' t)) (hu logT : U → ℝ) (a La B0 m C0 : ℝ) :
    CorrectedHeightVariationBound (TT.map e) hu logT aP a La B0 m C0 ↔ CorrectedHeightVariationBound (TT.map e') hu logT aP' a La B0 m C0 := by
  simp [CorrectedHeightVariationBound, Finset.sum_map, h, Finset.card_map]

theorem divisibility_of_inner_divisibility : DivOfDivIn (H := H) (W := W) (m := m) := by
  intro D ell G C N TT T2 a w Fm Rw logOm C0 g₁ g₂ hx hk hLa hlg hX' ⟨hR, hc1, hc2, hc3, hT, h2, h3, hF⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (divisibility_free_at _ _ _ _ _ _ C logOm).1
      (construct_divisibility_of_conclusion H W m G C D ell N TT T2 a w Fm logOm C0 (fun u0 => (Rw u0).D) (fun u0 => (Rw u0).XE)
        (fun u0 => (Rw u0).R) (fun u0 => (Rw u0).ψ) (fun u0 => (hR u0).1) (fun u0 => (hR u0).2.1) hX'
        (fun u0 => (hR u0).2.2.1) (fun u0 => (hR u0).2.2.2) hc1 hx hk hLa
        (fun u0 u => (concl_transport TT (topPhi H) (topEmb H) (aPhi a) (fun ρ => a ρ.2) (fun _ => rfl) _ _ _ _ _ _ _ _ _ _ _ _).1
          (hT u0 u)))
  · exact (construct_exponent_comparison H W m G C D ell N TT T2 a w Fm C0 ![g₁, g₂] hlg hc2 hx
      (fun u0 u => (second_conclusion_transport TT (topPhi H) (topEmb H) (aPhi a) (fun ρ => a ρ.2) (fun _ => rfl) _ _ _ _ _).1 (h2 u0 u))).2
  · exact construct_height_comparison H W m G C D ell N TT T2 a w Fm C0 hc3 hx hLa
      (fun u0 => (third_conclusion_transport TT (topPhi H) (topEmb H) (fun _ => aPhi a) (fun _ ρ => a ρ.2) (fun _ _ => rfl) _ _ _ _ _ _ _).1 (h3 u0))
  · exact construct_height_bound H W m G C D ell N TT T2 a w Fm (fun u0 => (Rw u0).D) (fun u0 => (Rw u0).XE)
        (fun u0 => (Rw u0).R) (fun u0 => (Rw u0).ψ) (fun u0 => (hR u0).1) (fun u0 => (hR u0).2.1) hX'
        (fun u0 => (hR u0).2.2.1) (fun u0 => (hR u0).2.2.2) hF

theorem inputs_first_to_discriminant : Inputs6aToD (H := H) (W := W) (m := m) := by
  intro D ell G C cT N TT T2 a w Fm Rw η θ eK K CL logOm C0 g₁ g₂ hlg
    ⟨h1, h2, h3, h4, h5, hDiv, h6, h7, h8, h9, h10, h11, h12⟩ hThin hVal
  have hE0 := h9.1
  have hx : 0 ≤ G.x := le_trans zero_le_one hE0.1
  have hk : 0 ≤ G.k := le_trans zero_le_one hE0.2.2.2.2.2.2.2.2.2.1
  have hLa : 0 ≤ G.La := hE0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨d1, d2, d3, d4⟩ := divisibility_of_inner_divisibility D ell G C N TT T2 a w Fm Rw logOm C0 g₁ g₂ hx hk hLa hlg
    (fun u0 => (h1 u0).1.1) hDiv
  exact ⟨h1, h2, h3, h4, h5, d1, d2, d3, h6, h7, d4, h8, h9, ⟨h10, hThin, hVal⟩, h11, h12⟩

end Defs

theorem analytic_first_to_lattice_discriminant : Core6aToCore2d := by
  intro c' hHA ε A hε hA
  obtain ⟨x₁, hT⟩ := hHA ε A hε hA
  refine ⟨x₁, ?_⟩
  rintro Cord eD eL K cHH eK CL eW KW x hxx ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Rw, Lp,
    P, π, s, sB, BAD, Sig, η, g₁, g₂, logOm, C0, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2, hlg, hPer, hL, hB⟩
  obtain ⟨hH, hTV⟩ := hT x hxx CL q d h25
  obtain ⟨hThin, hVal⟩ := hTV e he
  refine ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P, π, s, sB, BAD, Sig, η,
    Real.exp (-c' * x ^ (ε / 8)), g₁, g₂, logOm, hH, hx, hεG, heD, heL, hcHH, hPe, hv, hg1, hg2, hlg, hPer, hL, fun o ho => ?_⟩
  refine inputs_first_to_discriminant _ _ G C cT N TT T2 (a o) (w o) (Fm o) (Rw o) η _ eK K CL logOm C0 g₁ g₂ hlg (hB o ho) ?_ ?_
  · rw [hx, hεG]; exact hThin
  · rw [hx, hεG]; exact hVal

theorem ramE_one_le {K : Type} [Field K] [NumberField K] (w : slopeLatticeData.FinPl K) : 1 ≤ ramE w := by
  have := w.2.isPrime
  have h : 0 < w.1.ramificationIdx ℤ := Ideal.ramificationIdx_pos w.1 ℤ
  unfold ramE
  exact_mod_cast h

theorem round_of_floor : RoundOfFloor := by
  classical
  intro I m F u g₁ g₂ Xpp hX hcl hσ h0 hg1 hg2 hT
  have hdiff : ∀ w ∈ F.S, 0 ≤ F.sgw u w - F.sgR u w ∧ F.sgw u w - F.sgR u w ≤ 1 := by
    intro w hw
    have he := ramE_pos w
    have he1 := ramE_one_le w
    have h1 : ((F.σ u w : ℤ) : ℝ) ≤ ramE w * F.sgw u w := by rw [hσ w hw]; exact Int.floor_le _
    have h2 : ramE w * F.sgw u w < ((F.σ u w : ℤ) : ℝ) + 1 := by rw [hσ w hw]; exact Int.lt_floor_add_one _
    have h3 : F.sgR u w = ((F.σ u w : ℤ) : ℝ) / ramE w := rfl
    rw [h3]
    constructor
    · rw [sub_nonneg, div_le_iff₀ he]; linarith
    · have : F.sgw u w - 1 ≤ ((F.σ u w : ℤ) : ℝ) / ramE w := by rw [le_div_iff₀ he]; nlinarith
      linarith
  refine ⟨fun w hw => by linarith [(hdiff w hw).1], ?_⟩
  refine CosetIndexLemmas.rounding_rd_holds (slopeLatticeData.FinPl F.K) F.S prBelow lE (F.sgw u) (F.sgR u)
    (F.Pr.filter (fun p => (p : ℝ) ≤ Xpp ∨ p = g₁ ∨ p = g₂ ∨ p = F.T u)) Xpp g₁ g₂ (F.T u)
    (fun w _ => lE_nonneg w) ?_ (fun w hw => (hdiff w hw).2) ?_ ?_ hX hg1 hg2 hT
  · intro p hp
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hp).1
    exact (unit_rule_over_places F.K).2 F.S _ ((unit_rule_over_places F.K).1 w0).1 (fun w' hw' => hcl w0 hw0 w' hw')
  · intro w hw hn
    have hPr : prBelow w ∈ F.Pr := Finset.mem_image_of_mem _ hw
    have hn' : ¬ ((prBelow w : ℝ) ≤ Xpp ∨ prBelow w = g₁ ∨ prBelow w = g₂ ∨ prBelow w = F.T u) :=
      fun h => hn (Finset.mem_filter.2 ⟨hPr, h⟩)
    simp only [not_or, not_le] at hn'
    have hz := h0 w hw hn'.1 hn'.2.1 hn'.2.2.1 hn'.2.2.2
    have hs : F.σ u w = 0 := by rw [hσ w hw, hz]; simp
    have h3 : F.sgR u w = ((F.σ u w : ℤ) : ℝ) / ramE w := rfl
    rw [h3, hs, hz]; simp
  · intro p hp
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hp).1
    exact ⟨((unit_rule_over_places F.K).1 w0).1, (Finset.mem_filter.1 hp).2⟩

section DefsB
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

theorem slopes_from_size_and_count : SlopesFromSizeAndCount (U0 := U0) (W := W) (Top := Top) (m := m) (f := f) := by
  intro D C cZ cL cE5 c5 Sc LZ Gam X bN ⟨hZ, hZW, hcS⟩ ⟨hE, hU, hV, hLW, hEW, hCW, hc1, hc2⟩
  have h0 : 0 ≤ c5 := hCW.1
  have hP5 : BoundedBy' D c5 X := exact_coefficient_to_proposition D cE5 c5 X bN hEW hE hU h0 hc1
  have hJ := joint_four_five (withGam D Gam) C cZ cL Sc LZ c5 Gam X hZW hZ hCW hP5 hV hLW hcS hc2
  exact ⟨hJ.1, hJ.2, proposition_to_log_t_upper (withGam D Gam) c5 Gam X hCW hP5 hLW⟩

theorem level_of_count : LevelOfCount (U0 := U0) (W := W) (Top := Top) (m := m) (f := f) := by
  intro D C cE5 c5 Gam X bN ⟨hE, hU, hV, hLW, hEW, hCW, hc1, hc2⟩ ⟨hm, hfb, hw, hlg, hmk, hc⟩ hL hb u0 u
  have h0 : 0 ≤ c5 := hCW.1
  have hP5 : BoundedBy' D c5 X := exact_coefficient_to_proposition D cE5 c5 X bN hEW hE hU h0 hc1
  have hlow : (m : ℝ) * D.L / 2 ≤ Real.log (D.T u0 u) :=
    level_lower_of_count (withGam D Gam) c5 Gam X hCW hP5 hLW hw hlg hmk hEW.2.2.2.2.1 hc u0 u
  have hf : 1 ≤ f := hEW.1
  have hG : 0 < Gam := lt_of_lt_of_le one_pos hCW.2.2.2.1
  have hTpos : 0 < D.T u0 u :=
    lt_of_lt_of_le (mul_pos (hLW u0 u).1 (Real.rpow_pos_of_pos hG _)) (hLW u0 u).2.1
  have hpow : D.b ^ ((m : ℝ) / 2) ≤ D.T u0 u :=
    (pow_of_log (m : ℝ) D.b (D.T u0 u) (by linarith) hTpos).1 (by rw [← hL]; exact hlow)
  have hm' : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb1 : D.b ≤ D.b ^ ((m : ℝ) / 2) := Real.self_le_rpow_of_one_le hb (by linarith)
  have hf' : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h := level_sizes f m D.b (D.T u0 u) 2 hf hm hfb hpow (by linarith) le_rfl
  exact ⟨h.2.1, h.2.2.2, hlow⟩

end DefsB

section DefsB2
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem inputs_second_to_first : Inputs6bTo6a (H := H) (W := W) (m := m) := by
  intro D ell G C N TT T2 a w Fm Rw O η θ eK K logOm C0 cZ cL cE5 c5 g₁ g₂
    ⟨h1, hPl, hMx, hc28, h4, h5, hDiv, hS4, hS5, ⟨hT5, hlam⟩, hLev, ⟨hg1, hg2, hmL⟩, h8, h9, h10, h11, h12⟩
  have hE0 := h9.1
  have hb : 1 ≤ bTx G.x G.ε := hE0.2.2.2.1
  have hXpp : 0 ≤ XppH H G := hE0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hSl, hCt, hUp⟩ := slopes_from_size_and_count (mkData G C.cHH D ell N TT T2 a w Fm) C cZ cL cE5 c5 O.Sc O.LZ O.Gam O.X O.bN
    hS4 hS5
  have hLv := level_of_count (mkData G C.cHH D ell N TT T2 a w Fm) C cE5 c5 O.Gam O.X O.bN hS5 hLev rfl hb
  have hlogT : ∀ u0 (u : W u0), Real.log ((Fm u0).T u : ℝ) ≤ XppH H G := fun u0 u => le_trans (hUp u0 u) hmL
  have hRd : ∀ u0 (u : W u0), (∀ w ∈ (Fm u0).S, (Fm u0).sgR u w ≤ (Fm u0).sgw u w) ∧
      (Fm u0).Rd u ≤ (2 * Real.log 4 + 6) * XppH H G := fun u0 u =>
    round_of_floor (W u0) m (Fm u0) u g₁ g₂ (XppH H G) hXpp (hPl u0).2.2.2.1
      ((hPl u0).2.2.2.2.2 u).2.2.2.2.2.2.2.2.2.2.2.2.2.1 ((hPl u0).2.2.2.2.2 u).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg1 hg2
      (hlogT u0 u)
  refine ⟨h1, fun u0 => ?_, ⟨by linarith, by linarith, fun u0 u => ⟨?_, ?_⟩⟩, h4, h5, hDiv, hCt, hSl, h8, h9, h10, h11, h12⟩
  · obtain ⟨p1, p2, p3, p4, p5, pu⟩ := hPl u0
    refine ⟨p1, p2, p3, p4, p5, fun u => ?_⟩
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, -, -, q16⟩ := pu u
    exact ⟨q1, q2, q3, q4, q5, q6, q7, (hLv u0 u).1, q8, q9, q10, q11, q12, q13, (hRd u0 u).1, q16, hMx u0 u, (hLv u0 u).2.1⟩
  · have h := index_to_lambda (mkData G C.cHH D ell N TT T2 a w Fm) O.aM (O.VV u0 u) O.Wt O.bt hT5
    rw [(construct_parameter_definitions H W m G C.cHH D ell N TT T2 a w Fm).2.2.2.2.2.2] at h
    exact le_trans (hlam u0 u) h
  · have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    calc (Fm u0).Rd u ≤ (2 * Real.log 4 + 6) * XppH H G := (hRd u0 u).2
      _ ≤ C.cSl1 * XppH H G := mul_le_mul_of_nonneg_right (by linarith) hXpp

end DefsB2

theorem analytic_second_to_first : Core6bToCore6a := by
  rintro A c' Cord eD eL K cHH eK CL eW KW ε x ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, N, TT, T2, a, w, Fm, Rw, O, Lp,
    P, π, s, sB, BAD, Sig, η, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2, hlg,
    hPer, hL, hB⟩
  exact ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, 7, N, TT, T2, a, w, Fm, Rw, Lp, P, π, s, sB, BAD, Sig, η, g₁, g₂,
    logOm, C0, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2, hlg, hPer, hL, fun o ho =>
      inputs_second_to_first _ _ G C N TT T2 (a o) (w o) (Fm o) (Rw o) (O o) η _ eK K logOm C0 cZ cL cE5 c5 g₁ g₂ (hB o ho)⟩

theorem lattice_of_chain : LatOfChain := by
  intro I _ m F Rw sg Gam C0S delB hdual ⟨hX', hX, hcc, hccs, hN, hNs, hT1, hT2, de, del, hdel, hCh⟩
  obtain ⟨p1, p2, p3, -, p5, p6, -, p8, p9, p10, p11⟩ := HilbertSchmidtUnitaryInvariance.chain_substitution I F.Dall F.D F.D1 F.d F.r F.Pf F.Vr F.ga
    F.c F.Vrow F.U F.J F.J1 _ F.Y' F.Y F.Dstar sg F.η0 F.η1 F.e0 de del C0S Gam hCh
  have hDall : 0 < F.Dall := (HilbertSchmidtUnitaryInvariance.corollary_chain I F.Dall F.D F.D1 F.d F.r F.Pf F.Vr F.ga
    F.c F.Vrow F.U F.J F.J1 _ F.Y' F.Y F.Dstar sg F.η0 F.η1 F.e0 de del C0S Gam hCh).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, c2, c3, c4, -, -, c7, -, c9, c10, c11, c12, c13, -, -, -, -, -, -, -, -, c22, -, -, c25, c26, -⟩ := hCh
  have hsum : F.Dall = F.D + F.D1 := (HilbertSchmidtUnitaryInvariance.frame_properties F.Dall F.D F.D1 F.J F.J1 c22).2.2.1
  have hn : (0 : ℝ) < (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := by
    have : 0 < Fintype.card (Fin F.D ⊕ Fin F.D1) := by simp; omega
    exact_mod_cast this
  have hle : (Fintype.card (Fin F.D) : ℝ) ≤ (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := by
    have : Fintype.card (Fin F.D) ≤ Fintype.card (Fin F.D ⊕ Fin F.D1) := by simp
    exact_mod_cast this
  have hdef : F.toFam.del = 1 - (Fintype.card (Fin F.D) : ℝ) / (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := rfl
  have h1 : 1 - del ≤ (Fintype.card (Fin F.D) : ℝ) / (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := by
    rw [le_div_iff₀ hn]; exact p11
  have h2 : (Fintype.card (Fin F.D) : ℝ) / (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) ≤ 1 := by
    rw [div_le_one hn]; exact hle
  have hd0 : 0 ≤ F.toFam.del := by rw [hdef]; linarith
  have hd1 : F.toFam.del ≤ del := by rw [hdef]; linarith
  have hd2 : (1 - F.toFam.del) * (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) ≤ (Fintype.card (Fin F.D) : ℝ) := by
    rw [hdef, sub_sub_cancel, div_mul_cancel₀ _ hn.ne']
  refine ⟨⟨⟨hX', hX, c26, c25, hcc, hccs, hN, hNs, p8, ?_, hT2, hd0, lt_of_le_of_lt hd1 p10, hd2, p6⟩, p1, fun _ => rfl, p2,
    c2, c3, c4, p3, c9, c10, c11, c12, c13, p5⟩, le_trans hd1 hdel, c7⟩
  intro i
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨β, hβ, hint⟩ := hT1 i φ hφ
  rw [hdual.2.2]
  exact ⟨β, hint, hβ⟩

theorem mu_max_of_submodule : MuMaxOfSub := by
  intro I m F hS u hX hM hMf hne
  obtain ⟨hXf, hinj, hht, hmap⟩ := hS u
  have hle : (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) ≤ F.Mf u := by rw [hmap]; exact inf_le_left
  have hne' : (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (F.j u) y ∈ (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) := ⟨y, hy, rfl⟩
    rw [h0, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot _).2 (hinj (h1.trans (map_zero _).symm))
  have h := ((slope_inequality_mean F.K (F.V u) (Fin (F.r u)) (F.Vf u) (Fin (F.d u)) (F.b u) (F.X u) (F.bf u) (F.Xf u) hX hXf
    (F.j u) (F.M u) hM hne').2 (F.Mf u) hMf hle).2 hinj.injOn
  linarith

section DefsC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem inputs_third_to_second : Inputs6cTo6b (H := H) (W := W) (m := m) := by
  intro D ell G C N TT T2 a w Fc Rw O η θ eK K logOm C0 cZ cL cE5 c5 C0S g₁ g₂
    ⟨hLat, hPl, hSub, hc28, hr, h5, hDiv, hS4, hS5, hT5, hLev, hRo, h8, h9, h10, h11, h12⟩
  have hL := fun u0 => lattice_of_chain (W u0) m (Fc u0) (Rw u0) (sgX G C.cHH) O.Gam C0S G.delBar
    (hDiv.1 u0).2.2.2 (hLat u0)
  refine ⟨fun u0 => (hL u0).1, hPl, fun u0 u => ?_, hc28, fun u0 u => ?_, h5, hDiv, hS4, hS5, hT5, hLev, hRo,
    fun u0 => ⟨(hL u0).2.1, (h8 u0).1, (h8 u0).2⟩, h9, h10, h11, h12⟩
  · obtain ⟨q1, q2, q3, -⟩ := (hPl u0).2.2.2.2.2 u
    refine mu_max_of_submodule (W u0) m (Fc u0) (hSub u0) u ((hLat u0).2.1 u) q1 q3 ?_
    intro h0
    have hb : (Fc u0).b u ⟨0, hr u0 u⟩ ∈ Submodule.span (Fc u0).K (((Fc u0).M u : Submodule _ _) : Set ((Fc u0).V u)) := by
      have := q2
      rw [this]; exact Submodule.mem_top
    rw [h0] at hb
    simp at hb
    exact ((Fc u0).b u).ne_zero _ hb
  · show (0 : ℝ) < (Fintype.card (Fin ((Fc u0).r u)) : ℝ)
    rw [Fintype.card_fin]
    exact_mod_cast hr u0 u

end DefsC

theorem analytic_third_to_second : Core6cToCore6b := by
  rintro A c' Cord eD eL K cHH eK CL eW KW ε x ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, N, TT, T2, a, w, Fc, Rw, O, Lp,
    P, π, s, sB, BAD, Sig, η, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, C0S, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2,
    hlg, hPer, hL, hB⟩
  exact ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, N, TT, T2, a, w, fun o u0 => (Fc o u0).toFam, Rw, O, Lp, P, π, s, sB,
    BAD, Sig, η, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2, hlg, hPer, hL,
    fun o ho => inputs_third_to_second _ _ G C N TT T2 (a o) (w o) (Fc o) (Rw o) (O o) η _ eK K logOm C0 cZ cL cE5 c5 C0S g₁ g₂
      (hB o ho)⟩

theorem rpow_third_le (ε x : ℝ) (hε : 0 < ε) (hx : 1 ≤ x) (h2 : 2 ≤ x ^ (2 * ε / 3)) :
    x ^ (ε / 3) + x ^ (ε / 4) ≤ x ^ ε := by
  have hx0 : 0 < x := by linarith
  have h1 : x ^ (ε / 4) ≤ x ^ (ε / 3) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h3 : x ^ ε = x ^ (ε / 3) * x ^ (2 * ε / 3) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have h4 : 0 < x ^ (ε / 3) := Real.rpow_pos_of_pos hx0 _
  nlinarith

theorem ev_auxiliary (ε A c' K cHH : ℝ) (hε : 0 < ε) (hε4 : ε < 1 / 4) (hc' : 0 < c') :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 20 ≤ x ∧ E8 x ε ≤ x ^ (-cHH) / 2 ∧ 6 ≤ x ^ ((1 : ℝ) / 2 - ε) ∧
      2 * K + 2 ≤ 15 * x ^ ((1 : ℝ) / 2 - ε) ∧ 4 * Real.exp (x ^ (ε / 4)) ≤ bpTx x ε ∧
      ∀ f : ℝ, 0 ≤ f → f ≤ 2 * x ^ A →
        2 * f * (x + 1) * Real.exp (-c' * x ^ (ε / 8)) ≤ 1 / x ∧
        6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) ≤ bTx x ε / x := by
  obtain ⟨y1, -, h1⟩ := CosetIndexLemmas.ev_exp 2 cHH 1 (ε / 8) one_pos (by positivity)
  obtain ⟨y2, h2⟩ := ((tendsto_rpow_atTop (show 0 < (1 : ℝ) / 2 - ε by linarith)).eventually_ge_atTop
    (max 6 ((2 * K + 2) / 15))).exists_forall_of_atTop
  obtain ⟨y3, h3⟩ := ((tendsto_rpow_atTop (show 0 < 2 * ε / 3 by positivity)).eventually_ge_atTop 2).exists_forall_of_atTop
  obtain ⟨y4, -, h4⟩ := CosetIndexLemmas.ev_exp 8 (A + 2) c' (ε / 8) hc' (by positivity)
  obtain ⟨y5, -, h5⟩ := CosetIndexLemmas.ev_exp 48 (A + 2) 1 (ε / 3) one_pos (by positivity)
  refine ⟨max 20 (max y1 (max y2 (max y3 (max y4 y5)))), fun x hx => ?_⟩
  have hx20 : 20 ≤ x := le_trans (le_max_left _ _) hx
  have hx' := le_trans (le_max_right _ _) hx
  have g1 := h1 x (le_trans (le_max_left _ _) hx')
  have hx'' := le_trans (le_max_right _ _) hx'
  have g2 := h2 x (le_trans (le_max_left _ _) hx'')
  have hx3 := le_trans (le_max_right _ _) hx''
  have g3 := h3 x (le_trans (le_max_left _ _) hx3)
  have hx4 := le_trans (le_max_right _ _) hx3
  have g4 := h4 x (le_trans (le_max_left _ _) hx4)
  have g5 := h5 x (le_trans (le_max_right _ _) hx4)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hsum := rpow_third_le ε x hε hx1 g3
  have hA2 : x ^ (A + 2) = x ^ A * x * x := by
    rw [Real.rpow_add hx0, show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]; ring
  have hxA : 0 < x ^ A := Real.rpow_pos_of_pos hx0 _
  refine ⟨hx20, ?_, le_trans (le_max_left _ _) g2, ?_, ?_, fun f hf0 hf => ⟨?_, ?_⟩⟩
  · unfold E8
    rw [Real.exp_neg, Real.rpow_neg hx0.le]
    rw [one_mul] at g1
    have hp : 0 < x ^ cHH := Real.rpow_pos_of_pos hx0 _
    rw [inv_eq_one_div, inv_eq_one_div, div_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith
  · have := le_trans (le_max_right _ _) g2
    rw [div_le_iff₀ (by norm_num)] at this
    linarith
  · unfold bpTx aTx bTx XpTx
    rw [le_div_iff₀ (Real.exp_pos _)]
    have e1 : Real.exp (x ^ (ε / 4)) * Real.exp (x ^ (ε / 3)) ≤ Real.exp (x ^ ε) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have e0 : 0 < Real.exp (x ^ ε) := Real.exp_pos _
    nlinarith
  · rw [neg_mul, Real.exp_neg, le_div_iff₀ hx0]
    have e0 : 0 < Real.exp (c' * x ^ (ε / 8)) := Real.exp_pos _
    rw [hA2] at g4
    have k1 : 2 * f * (x + 1) * x ≤ 8 * (x ^ A * x * x) := by
      have : 2 * f * (x + 1) * x ≤ 2 * (2 * x ^ A) * (x + 1) * x := by gcongr
      have k2 : 2 * (2 * x ^ A) * (x + 1) * x ≤ 2 * (2 * x ^ A) * (2 * x) * x := by gcongr; linarith
      nlinarith
    calc 2 * f * (x + 1) * (Real.exp (c' * x ^ (ε / 8)))⁻¹ * x
        = (2 * f * (x + 1) * x) * (Real.exp (c' * x ^ (ε / 8)))⁻¹ := by ring
      _ ≤ Real.exp (c' * x ^ (ε / 8)) * (Real.exp (c' * x ^ (ε / 8)))⁻¹ := by
          gcongr; exact le_trans k1 g4
      _ = 1 := mul_inv_cancel₀ e0.ne'
  · rw [le_div_iff₀ hx0]
    unfold bTx
    rw [hA2, one_mul] at g5
    have e4 : 1 ≤ Real.exp (x ^ (ε / 4)) := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
    have e1 : Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 4)) ≤ Real.exp (x ^ ε) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 hsum
    have k1 : 6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) * x
        ≤ 6 * (2 * x ^ A) * (2 * x) * (2 * Real.exp (x ^ (ε / 4))) * x := by
      gcongr <;> linarith
    calc 6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) * x
        ≤ 6 * (2 * x ^ A) * (2 * x) * (2 * Real.exp (x ^ (ε / 4))) * x := k1
      _ = (48 * (x ^ A * x * x)) * Real.exp (x ^ (ε / 4)) := by ring
      _ ≤ Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 4)) := by gcongr
      _ ≤ Real.exp (x ^ ε) := e1

theorem deF_bound {I : Type} [Fintype I] {m : ℕ} (F : Fam I m) (f : ℕ) (T0 : ℝ) (hT0 : 0 < T0)
    (h : ∀ u, F.du u = F.dM u * (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ∧ 2 ≤ (F.T u : ℝ) ∧ T0 ≤ (F.T u : ℝ))
    (hpos : 0 < MatrixLatticeEstimates.RsG F.ιf) :
    0 ≤ F.deF ∧ F.deF ≤ 2 * (f : ℝ) / T0 ∧
      ∑ u, ((Fintype.card (F.ιf u) : ℝ) - (Fintype.card (F.ι u) : ℝ)) ≤ F.deF * MatrixLatticeEstimates.RsG F.ιf := by
  have hu : ∀ u, F.du u ≤ F.dM u ∧ (1 - 2 * (f : ℝ) / T0) * F.dM u ≤ F.du u := by
    intro u
    obtain ⟨h1, h2, h3⟩ := h u
    have hdM : 0 ≤ F.dM u := Nat.cast_nonneg _
    have hb0 : 0 ≤ 1 - 1 / ((F.T u : ℝ) - 1) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hb1 : 1 - 1 / ((F.T u : ℝ) - 1) ≤ 1 := by
      have : 0 ≤ 1 / ((F.T u : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
      linarith
    have hp1 : (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ≤ 1 := pow_le_one₀ hb0 hb1
    have hdef := defect_bound_alt f (F.T u : ℝ) h2
    have hq : 2 * (f : ℝ) / (F.T u : ℝ) ≤ 2 * (f : ℝ) / T0 :=
      div_le_div_of_nonneg_left (by positivity) hT0 h3
    rw [h1]
    constructor
    · nlinarith
    · have : 1 - 2 * (f : ℝ) / T0 ≤ (1 - 1 / ((F.T u : ℝ) - 1)) ^ f := by linarith
      nlinarith
  have hle : MatrixLatticeEstimates.RsG F.ι ≤ MatrixLatticeEstimates.RsG F.ιf := Finset.sum_le_sum fun u _ => (hu u).1
  have hge : (1 - 2 * (f : ℝ) / T0) * MatrixLatticeEstimates.RsG F.ιf ≤ MatrixLatticeEstimates.RsG F.ι := by
    unfold MatrixLatticeEstimates.RsG
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => (hu u).2
  refine ⟨?_, ?_, ?_⟩
  · unfold Fam.deF
    rw [sub_nonneg, div_le_one hpos]; exact hle
  · unfold Fam.deF
    have : 1 - 2 * (f : ℝ) / T0 ≤ MatrixLatticeEstimates.RsG F.ι / MatrixLatticeEstimates.RsG F.ιf := by rw [le_div_iff₀ hpos]; exact hge
    linarith
  · unfold Fam.deF
    rw [Finset.sum_sub_distrib, sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
    exact le_refl _

theorem rsG_fin {I : Type} [Fintype I] (d : I → ℕ) : MatrixLatticeEstimates.RsG (fun u => Fin (d u)) = HilbertSchmidtNormSquare.Rs d := by
  unfold MatrixLatticeEstimates.RsG HilbertSchmidtNormSquare.Rs
  simp

theorem latIn_of_trace {I : Type} [Fintype I] {m : ℕ} (F : FamC I m) (Rw : Rows F.toFam) (x ε sg Gam C0S de : ℝ)
    (hT : F.TraceIn Rw x ε sg Gam C0S) (hx : 0 < x) (hsg0 : 0 < sg) (hsg : sg ≤ 1 / 20) (hE8 : E8 x ε ≤ sg / 2)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4) (hcor : ∑ u, ((F.d u : ℝ) - (F.r u : ℝ)) ≤ de * HilbertSchmidtNormSquare.Rs F.d)
    (w4 : ∀ u, F.Dstar / Gam ^ 2 / C0S ≤ (F.d u : ℝ)) :
    F.LatIn Rw sg Gam C0S (E7 x ε) := by
  obtain ⟨⟨r1, r2, r3, r4, r5, r6⟩, t1, t2, ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, ⟨w1, w2, w3⟩, hI,
    ⟨m1, m2, m3, m4, m5, m6⟩, ⟨i1, i2⟩⟩ := hT
  have h7 : E7 x ε < 1 := by
    unfold E7
    rw [Real.exp_lt_one_iff]
    have := Real.rpow_pos_of_pos hx (ε / 7)
    linarith
  exact ⟨r1, r2, r3, r4, r5, r6, t1, t2, de, E7 x ε, le_refl _, s1, s2, hsg0, hsg, w1, w2, w3, w4, s4, le_trans s5 hE8,
    le_trans s6 hE8, s7, le_trans s8 hE8, s3, hI, hde0, hde4, hcor, m1, m2, m3, i1, h7, i2, m4, m5, m6⟩

theorem words_of_count : WordsOfCount := by
  intro X Gam T k dst Dstar d C0S f hX hG hf hk hT h4 hdst hD hXD hd hC
  have hf' : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hG0 : 0 < Gam := by linarith
  have hy : 0 < (f : ℝ) * k := by positivity
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hGp : 0 < Gam ^ (-(2 / ((f : ℝ) * k))) := Real.rpow_pos_of_pos hG0 _
  have e1 : (X * Gam ^ (-(2 / ((f : ℝ) * k)))) ^ ((f : ℝ) * k) = Dstar / dst * Gam ^ (-2 : ℝ) := by
    rw [Real.mul_rpow hX.le hGp.le, hXD, ← Real.rpow_mul hG0.le]
    congr 2
    field_simp
  have e2 : Dstar / dst * Gam ^ (-2 : ℝ) ≤ T ^ ((f : ℝ) * k) := by
    rw [← e1]
    exact Real.rpow_le_rpow (mul_pos hX hGp).le hT hy.le
  have hz : T ≤ T ^ k := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ k := Real.rpow_le_rpow_of_exponent_le hT1 hk
  set z : ℝ := T ^ k with hzdef
  have hz0 : 0 < z := by linarith
  have e3 : z ^ f = T ^ ((f : ℝ) * k) := by
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, mul_comm]
  have hfz : (f : ℝ) / z ≤ 1 / 4 := by
    rw [div_le_iff₀ hz0]; linarith
  have e4 : (z - 1) ^ f = z ^ f * (1 + -(1 / z)) ^ f := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have hinv : 1 / z ≤ 1 := by
    rw [div_le_one hz0]; linarith
  have e5 : 1 + (f : ℝ) * -(1 / z) ≤ (1 + -(1 / z)) ^ f := one_add_mul_le_pow (by linarith) f
  have e6 : 3 / 4 ≤ (1 + -(1 / z)) ^ f := by
    have : (f : ℝ) * -(1 / z) = -((f : ℝ) / z) := by ring
    linarith
  have e7 : 3 / 4 * z ^ f ≤ (z - 1) ^ f := by
    rw [e4]
    have := pow_pos hz0 f
    nlinarith
  have e8 : Gam ^ (-2 : ℝ) = 1 / Gam ^ 2 := by
    rw [Real.rpow_neg hG0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have e9 : 3 / 4 * (Dstar / Gam ^ 2) ≤ d := by
    rw [hd]
    have h1 : dst * (3 / 4 * (Dstar / dst * Gam ^ (-2 : ℝ))) ≤ dst * (z - 1) ^ f := by
      apply mul_le_mul_of_nonneg_left _ hdst.le
      rw [e3] at e7
      linarith
    have h2 : dst * (3 / 4 * (Dstar / dst * Gam ^ (-2 : ℝ))) = 3 / 4 * (Dstar / Gam ^ 2) := by
      rw [e8]; field_simp
    linarith
  have hq : 0 < Dstar / Gam ^ 2 := by positivity
  have e10 : Dstar / Gam ^ 2 / C0S ≤ Dstar / Gam ^ 2 / 2 := div_le_div_of_nonneg_left hq.le (by norm_num) hC
  linarith

theorem modulus_v_eventually : HostVEv := by
  intro ε A hε hA
  obtain ⟨y1, -, h1⟩ := CosetIndexLemmas.ev_exp 1 1 1 (ε / 30) one_pos (by positivity)
  obtain ⟨y2, h2⟩ := ((tendsto_rpow_atTop (show 0 < ε / 15 by positivity)).eventually_ge_atTop
    (A + 2)).exists_forall_of_atTop
  obtain ⟨y3, h3⟩ := ((tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop 14).exists_forall_of_atTop
  refine ⟨max 3 (max y1 (max y2 y3)), fun x hx e q d he hq1 hq2 hd1 hd2 => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hx' := le_trans (le_max_right _ _) hx
  have g1 := h1 x (le_trans (le_max_left _ _) hx')
  have hx'' := le_trans (le_max_right _ _) hx'
  have g2 := h2 x (le_trans (le_max_left _ _) hx'')
  have g3 := h3 x (le_trans (le_max_right _ _) hx'')
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : Real.log x ≤ x ^ (ε / 30) := by
    rw [Real.log_le_iff_le_exp hx0]
    simpa using g1
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hX1 : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := by
    unfold X1; rw [← Real.exp_mul]
  have hX2 : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) := by
    unfold X2; rw [← Real.exp_mul]
  have hy0 : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
  have hq8 : (8 : ℝ) ≤ (q : ℝ) := by
    have := Real.add_one_le_exp (x ^ (ε / 5) * (1 / 2))
    rw [hX1] at hq1
    linarith
  have hd8 : (8 : ℝ) ≤ (d : ℝ) := by
    have := Real.add_one_le_exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2))
    rw [hX2] at hd1
    have hl2 : 1 ≤ Real.log x ^ 2 := by nlinarith
    have : x ^ (ε / 5) ≤ x ^ (ε / 5) * Real.log x ^ 2 := by nlinarith
    linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hs8 : 8 ≤ Real.sqrt ((q : ℝ) * (d : ℝ)) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hp1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hp0 : 0 < (2 : ℝ) ^ (-(e : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpw : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  have hP0 : 0 < (2 : ℝ) ^ ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · unfold hostV
    have := Real.pi_le_four
    rw [hhalf] at hpw
    nlinarith
  · have hS0 : 0 < Real.sqrt ((q : ℝ) * (d : ℝ)) := by linarith
    unfold hostV
    rw [Real.log_mul (by norm_num) (mul_pos hP0 hS0).ne', Real.log_mul hP0.ne' hS0.ne',
      Real.log_rpow (by norm_num), Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne']
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hl2' : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hee : (e : ℝ) * Real.log 2 ≤ A * Real.log x := by
      have h := Real.log_le_log (by positivity) he
      rw [Real.log_rpow hx0] at h
      push_cast at h
      rw [Real.log_pow] at h
      exact h
    have hlq : Real.log (q : ℝ) ≤ x ^ (ε / 5) := by
      have h := Real.log_le_log hq0 hq2
      unfold X1 at h
      rwa [Real.log_exp] at h
    have hld : Real.log (d : ℝ) ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
      have h := Real.log_le_log hd0 hd2
      unfold X2 at h
      rwa [Real.log_exp] at h
    set z : ℝ := x ^ (4 * ε / 15) with hz
    have hz1 : 1 ≤ z := Real.one_le_rpow hx1 (by positivity)
    have c1 : x ^ (ε / 30) ≤ z := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have c2 : x ^ (ε / 5) ≤ z := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have c3 : x ^ (ε / 5) * Real.log x ^ 2 ≤ z := by
      have e1 : z = x ^ (ε / 5) * (x ^ (ε / 30)) ^ 2 := by
        rw [hz, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
      rw [e1]
      have : Real.log x ^ 2 ≤ (x ^ (ε / 30)) ^ 2 := pow_le_pow_left₀ (by linarith) hlx 2
      gcongr
    have c4 : x ^ (ε / 3) = x ^ (ε / 15) * z := by
      rw [hz, ← Real.rpow_add hx0]; congr 1; ring
    have c5 : ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) * Real.log 2 ≤ (e : ℝ) * Real.log 2 := by nlinarith
    have c6 : A * Real.log x ≤ A * z := by
      have : Real.log x ≤ z := le_trans hlx c1
      gcongr
    rw [c4]
    have c7 : (A + 2) * z ≤ x ^ (ε / 15) * z := by gcongr
    linarith

theorem deF_boundC {I : Type} [Fintype I] {m : ℕ} (F : FamC I m) (f : ℕ) (T0 : ℝ) (hT0 : 0 < T0)
    (h : ∀ u, F.toFam.du u = F.toFam.dM u * (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ∧ 2 ≤ (F.T u : ℝ) ∧ T0 ≤ (F.T u : ℝ))
    (hpos : 0 < HilbertSchmidtNormSquare.Rs F.d) :
    0 ≤ F.toFam.deF ∧ F.toFam.deF ≤ 2 * (f : ℝ) / T0 ∧
      ∑ u, ((F.d u : ℝ) - (F.r u : ℝ)) ≤ F.toFam.deF * HilbertSchmidtNormSquare.Rs F.d := by
  have hR : MatrixLatticeEstimates.RsG F.toFam.ιf = HilbertSchmidtNormSquare.Rs F.d := rsG_fin F.d
  have h0 := deF_bound F.toFam f T0 hT0 h (by rw [hR]; exact hpos)
  refine ⟨h0.1, h0.2.1, ?_⟩
  have h3 := h0.2.2
  rw [hR] at h3
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun u _ => ?_)) h3
  have e1 : (Fintype.card (F.toFam.ιf u) : ℝ) = (F.d u : ℝ) := by
    show ((Fintype.card (Fin (F.d u)) : ℕ) : ℝ) = _
    rw [Fintype.card_fin]
  have e2 : (Fintype.card (F.toFam.ι u) : ℝ) = (F.r u : ℝ) := by
    show ((Fintype.card (Fin (F.r u)) : ℕ) : ℝ) = _
    rw [Fintype.card_fin]
  rw [e1, e2]

set_option maxHeartbeats 1600000 in
theorem inputs_fourth_to_third : Inputs6dTo6c := by
  intro ε A c' K cHH eK hε hε4 hA hc'
  obtain ⟨x1, h1⟩ := text_sizes_windows ε (|eK| + A + 2) hε
  obtain ⟨x2, h2⟩ := analytic_bounds_eventual ε (|eK| + A + 2) hε (by positivity)
  obtain ⟨x3, h3⟩ := CosetIndexLemmas.round_window_eventual ε (|K| + 1) hε (by positivity)
  obtain ⟨x4, h4⟩ := CosetIndexLemmas.sigma_window_eventual ε cHH 3 (A + 1) hε (by norm_num)
  obtain ⟨x5, h5⟩ := text_key ε (|eK| + A + 2) hε
  obtain ⟨x6, h6⟩ := ev_auxiliary ε A c' K cHH hε hε4 hc'
  obtain ⟨x7, h7⟩ := CosetIndexLemmas.deletion_eventual_holds ε hε
  refine ⟨max x1 (max x2 (max x3 (max x4 (max x5 (max x6 x7))))), fun x hx => ?_⟩
  have hx_1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxa := le_trans (le_max_right _ _) hx
  have hx_2 : x2 ≤ x := le_trans (le_max_left _ _) hxa
  have hxb := le_trans (le_max_right _ _) hxa
  have hx_3 : x3 ≤ x := le_trans (le_max_left _ _) hxb
  have hxc := le_trans (le_max_right _ _) hxb
  have hx_4 : x4 ≤ x := le_trans (le_max_left _ _) hxc
  have hxd := le_trans (le_max_right _ _) hxc
  have hx_5 : x5 ≤ x := le_trans (le_max_left _ _) hxd
  have hxe := le_trans (le_max_right _ _) hxd
  have hx_6 : x6 ≤ x := le_trans (le_max_left _ _) hxe
  have hx_7 : x7 ≤ x := le_trans (le_max_right _ _) hxe
  intro H _ _ _ W _ m D ell k v C N TT T2 a w Fc Rw O η logOm C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂ hn hv hlv hCB hc28 hcH1 hcH
    ⟨hTr, hPl, hSub, hr, hDiv, ⟨hZ, hcZ, hcL, hSc0, hSc, hLZ, hcS⟩,
      ⟨hEx, hUp, hVar, hLW, hGam, hGfk, hc50, hc56, hc53, hNode⟩, ⟨hC0S2, hRk⟩, ⟨haM, hWt, hbt, hlam⟩, hSz⟩
  obtain ⟨⟨hm1, hm2, hxm, heK0, hkK, hkn⟩, ⟨hTT, hT2⟩, hat, ⟨hη0, hη, hκ0, hκ, hoff, hbtw, hNW⟩, hcut, hword,
    ⟨hg1a, hg1b, hg2a, hg2b⟩⟩ := hSz
  obtain ⟨hx20, hE8, h6m, hKm, hbp4, hcost⟩ := h6 x hx_6
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxε1 : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε.le

  have hn1 : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) < (Fintype.card H : ℝ) := by linarith
  have hEA : A ≤ |eK| + A + 2 := by linarith [abs_nonneg eK]
  have hnE : (Fintype.card H : ℝ) ≤ x ^ (|eK| + A + 2) :=
    le_trans hn (Real.rpow_le_rpow_of_exponent_le hx1 hEA)
  have hfΦ : ((PhiSet (H := H)).card : ℝ) = 2 * (Fintype.card H : ℝ) :=
    (construct_parameter_definitions H W m (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w
      (fun u0 => (Fc u0).toFam)).2.2.2.2.1
  have hfpos : 0 < (PhiSet (H := H)).card := by
    have : (0 : ℝ) < ((PhiSet (H := H)).card : ℝ) := by rw [hfΦ]; linarith
    exact_mod_cast this
  have hxA1 : x ^ (A + 1) = x ^ A * x := by rw [Real.rpow_add hx0, Real.rpow_one]
  have hxA0 : 0 < x ^ A := Real.rpow_pos_of_pos hx0 _
  have hfA : 2 * (Fintype.card H : ℝ) ≤ x ^ (A + 1) := by
    rw [hxA1]
    clear * - hn hx20 hxA0
    nlinarith
  have hfE : 2 * (Fintype.card H : ℝ) ≤ x ^ (|eK| + A + 2) :=
    le_trans hfA (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [abs_nonneg eK]))

  have hm6 : (6 : ℝ) ≤ (m : ℝ) := le_trans h6m hm1
  have hm6' : 6 ≤ m := by exact_mod_cast hm6
  have hmx : (m : ℝ) ≤ x := by
    calc (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := hm2
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hmE : (m : ℝ) ≤ x ^ (|eK| + A + 2) :=
    le_trans hm2 (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [abs_nonneg eK]))
  have hk120 : 120 ≤ k := by
    clear * - hxm hx20 hm6
    nlinarith
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hmk : (m : ℝ) ≤ k := by
    clear * - hxm hx1 hm6
    nlinarith
  have hm2k : (m : ℝ) ^ 2 ≤ k := by
    clear * - hxm hmx hm6
    nlinarith
  have hkE : k ≤ x ^ (|eK| + A + 2) :=
    le_trans hkK (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [le_abs_self eK]))

  have hpi3 := Real.pi_gt_three
  have hv0 : 0 < v := by linarith
  have hlrd0 : 0 ≤ Real.log (2 * v) := Real.log_nonneg (by linarith)
  have hlvv : Real.log v ≤ Real.log (2 * v) := Real.log_le_log hv0 (by linarith)

  obtain ⟨-, hb1, hlb, hLa2, hka, hbp0, hkbp, hXpp0, hXppa⟩ :=
    h1 x k (Fintype.card H : ℝ) (Real.log (2 * v)) hx_1 hk0 hkE hn0 hnE hlv
  have hb0 : 0 < bTx x ε := by linarith
  have ha0 : 0 < aTx x ε := mul_pos hx0 hb0
  have hab : aTx x ε = x * bTx x ε := rfl
  have hexp4 : 1 ≤ Real.exp (x ^ (ε / 4)) := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hbppos : 0 < bpTx x ε := by linarith
  have hScb : O.Sc ≤ bpTx x ε := by linarith
  have hnT0 : (0 : ℝ) < (TT.card : ℝ) := by
    have : 0 < x ^ (-(ε / 8)) * (Fintype.card H : ℝ) / 2 := by
      have := Real.rpow_pos_of_pos hx0 (-(ε / 8))
      positivity
    linarith
  have hnT1 : (1 : ℝ) ≤ (TT.card : ℝ) := by
    have : 0 < TT.card := by exact_mod_cast hnT0
    exact_mod_cast this
  have hcTT : ((Fintype.card TT : ℕ) : ℝ) = (TT.card : ℝ) := by rw [Fintype.card_coe]
  obtain ⟨t1, t2, -, t4, t5, t6, t7, t8, -, -, -, t12, -, -⟩ :=
    h2 x k (2 * (Fintype.card H : ℝ)) (m : ℝ) (TT.card : ℝ) 1 O.Sc (Real.log (2 * v)) v hx_2 hk1 hkE (by linarith) hfE
      (by linarith) hmE le_rfl (Real.one_le_rpow hx1 (by positivity)) hnT1 hSc0 hScb hv0 hlvv hlrd0
  have hLa : Real.log (aTx x ε * (2 * v)) = Real.log (aTx x ε) + Real.log (2 * v) :=
    Real.log_mul ha0.ne' (by linarith : (2 * v) ≠ 0)
  have hxn : x * (Fintype.card H : ℝ) ≤ bpTx x ε := ((h5 x hx_5).2.2.2.2.2 _ hn0 hnE).2.2

  have hat' : ∀ t : TT, 0 ≤ a t ∧ a t ≤ 2 * aTx x ε := by
    intro t
    obtain ⟨ha1, ha2⟩ := abs_le.1 (hat t.1 t.2)
    have e1 : a t = (a t / bTx x ε) * bTx x ε := (div_mul_cancel₀ _ hb0.ne').symm
    have e2 : 0 ≤ a t / bTx x ε := by linarith
    have e3 : (a t / bTx x ε) * bTx x ε ≤ (x + 1) * bTx x ε := mul_le_mul_of_nonneg_right (by linarith) hb0.le
    have e4 := mul_nonneg (sub_nonneg.2 hx1) hb0.le
    constructor
    · rw [e1]; exact mul_nonneg e2 hb0.le
    · rw [hab]
      clear * - e1 e3 e4
      linarith

  have hoff0 : 0 ≤ off := by
    have hq : 0 ≤ bpTx x ε / x := div_nonneg hbp0 hx0.le
    rcases hoff with h | h
    · rw [h]; exact hq
    · rw [h]; exact_mod_cast Int.floor_nonneg.2 hq
  have hw1 : ∀ u0 j ρ, InPhi ρ → 1 ≤ w u0 j ρ := by
    intro u0 j ρ hρ
    obtain ⟨nw1, nw2, nw3⟩ := hNW
    by_cases hth : IsThickAt T2 u0 ρ
    · linarith [(nw1 u0 j ρ hth).1]
    · by_cases htop : ∀ t ∈ TT, ρ ≠ topPl t
      · have h := (nw3 u0 j ρ hρ hth htop).1
        have : 1 ≤ bpTx x ε / (x * (Fintype.card H : ℝ)) := by
          rw [le_div_iff₀ (by positivity), one_mul]; exact hxn
        linarith
      · simp only [not_forall, not_not] at htop
        obtain ⟨t, ht, rfl⟩ := htop
        have h := (nw2 u0 j t ht).1
        linarith [(hbtw t ht).1]
  have hwΦ : ∀ u0 j (ρ : Fin (PhiSet (H := H)).card), 1 ≤ w u0 j (ePhi ρ) := fun u0 j ρ =>
    hw1 u0 j _ (Finset.mem_filter.1 (ePhi ρ).2).2

  have hg1ne : (g₁ : ℝ) ≠ 0 := by
    intro h; rw [h, Real.log_zero] at hg1a; linarith
  have hg2ne : (g₂ : ℝ) ≠ 0 := by
    intro h; rw [h, Real.log_zero] at hg2a; linarith
  have hlg : Real.log ((g₁ : ℝ) * (g₂ : ℝ)) = Real.log g₁ + Real.log g₂ := Real.log_mul hg1ne hg2ne

  have hCB' := hCB
  obtain ⟨-, -, -, -, -, -, -, kCount, -, -, -, kSl1, -⟩ := hCB
  have hc5K : c5 ≤ K := by linarith
  have hK28 : 28 ≤ K := by linarith
  have hKabs : K ≤ |K| := le_abs_self K

  have hL1 : 1 ≤ Real.log (bTx x ε) := t5
  have hLLa : Real.log (bTx x ε) ≤ Real.log (aTx x ε * (2 * v)) := by rw [hLa]; exact t4
  have hx3ε : x ^ (ε / 3) ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have z_L0 : 0 ≤ Real.log (bTx x ε) := by linarith
  have z_La1 : 1 ≤ Real.log (aTx x ε * (2 * v)) := by linarith
  have z_k : Real.log k ≤ Real.log (aTx x ε * (2 * v)) := by rw [hLa]; exact t1
  have z_kv : Real.log (k * v) ≤ Real.log (aTx x ε * (2 * v)) := by rw [hLa]; exact t2
  have z_f1 : ((PhiSet (H := H)).card : ℝ) * k * (bpTx x ε + O.Sc) ≤ ((Fintype.card TT : ℕ) : ℝ) * aTx x ε := by
    rw [hfΦ, hcTT]; exact t6
  have z_f2 : ((PhiSet (H := H)).card : ℝ) * k ^ 2 ≤ ((Fintype.card TT : ℕ) : ℝ) * aTx x ε := by
    rw [hfΦ, hcTT]; exact t7
  have z_8f : 8 * ((PhiSet (H := H)).card : ℝ) ≤ bTx x ε := by rw [hfΦ]; exact t12
  have z_nT : 1 ≤ ((Fintype.card TT : ℕ) : ℝ) := by rw [hcTT]; exact hnT1
  have hε1 : ε ≤ 1 := by linarith
  have ZW : ZWindows (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) cZ cL (c5 + 1)
      O.Sc O.LZ :=
    ⟨hcZ, hcL, by linarith, ha0.le, hk1, hmk, hbp0, hSc0, hat', z_L0, hLLa, z_k, z_kv, hLZ, z_f1, z_f2⟩
  have EW : ExactWindows (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) O.bN := by
    refine ⟨hfpos, by omega, hmk, hmx, hL1, hv0, Real.log_nonneg ?_, ?_, ?_, ?_, fun u0 j ρ => ⟨(hNode u0 j ρ).1, ?_,
      (hNode u0 j ρ).2.1, ?_⟩⟩
    · show 1 ≤ v / Real.pi
      rw [le_div_iff₀ Real.pi_pos]; linarith
    · show Real.log (v / Real.pi) ≤ Real.log (bTx x ε)
      rw [hlb]
      have : Real.log (v / Real.pi) ≤ Real.log (2 * v) :=
        Real.log_le_log (div_pos hv0 Real.pi_pos) (by
          rw [div_le_iff₀ Real.pi_pos]
          clear * - hv0 hpi3
          nlinarith)
      linarith
    · show Real.log (2 * v) ≤ Real.log (bTx x ε)
      rw [hlb]; linarith
    · show 0 ≤ Real.log ((g₁ : ℝ) * (g₂ : ℝ))
      rw [hlg]; linarith
    · show 0 < w u0 j (ePhi ρ)
      linarith [hwΦ u0 j ρ]
    · show Real.log (O.bN u0 j ρ) ≤ 2 * Real.log (bTx x ε)
      rw [hlb]; exact (hNode u0 j ρ).2.2
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hk0]
    have := Real.exp_one_lt_d9
    linarith
  have CW : CountWindows (withGam (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w
      (fun u0 => (Fc u0).toFam)) O.Gam) c5 O.Gam :=
    ⟨hc50, hfpos, hk1, hGam, rfl, hGfk, z_L0, hLLa, z_La1, by
      show 1 ≤ (m : ℝ) * Real.log (bTx x ε)
      clear * - hm6 hL1
      nlinarith, hlogk⟩
  have S5 : Step5In (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) C cE5 c5 O.Gam
      O.X O.bN :=
    ⟨hEx, fun u0 u => by
      show Real.log (O.X u0 u) ≤ c5 * (m : ℝ) * Real.log (bTx x ε)
      rw [hlb]; exact hUp u0 u, hVar, hLW, EW, CW, hc56, hc53⟩
  have LWn : LevelWin (mkData (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w (fun u0 => (Fc u0).toFam)) c5 := by
    refine ⟨hm6', z_8f, fun u0 j ρ => ?_, ?_, hm2k, by linarith⟩
    · show 1 ≤ w u0 j (ePhi ρ) * v / Real.pi
      rw [le_div_iff₀ Real.pi_pos, one_mul]
      have hw := hwΦ u0 j ρ
      clear * - hw hv hpi3
      nlinarith
    · show 16 * Real.log (bTx x ε) ≤ Real.log ((g₁ : ℝ) * (g₂ : ℝ))
      rw [hlb, hlg]; linarith
  have hLv := level_of_count _ C cE5 c5 O.Gam O.X O.bN S5 LWn rfl hb1
  have hRW := h3 x (m : ℝ) (Fintype.card H : ℝ) hx_3 hm2 hn1
  have hmxε : x ^ ε ≤ (m : ℝ) * x ^ ε := by
    clear * - hm6 hxε1
    nlinarith

  have hsg0 : 0 < x ^ (-C.cHH) := Real.rpow_pos_of_pos hx0 _
  have hsgle : x ^ (-cHH) ≤ x ^ (-C.cHH) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsg20 : x ^ (-C.cHH) ≤ 1 / 20 := by
    calc x ^ (-C.cHH) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 1 / 20 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx20
  have hE8sg : E8 x ε ≤ x ^ (-C.cHH) / 2 := by linarith
  have hE80 : 0 < E8 x ε := Real.exp_pos _
  have hT0 : 0 < Real.exp ((m : ℝ) * x ^ ε / 2) := Real.exp_pos _
  have hfA' : ((PhiSet (H := H)).card : ℝ) ≤ x ^ (A + 1) := by rw [hfΦ]; exact hfA
  have hSg : ∀ de e0 : ℝ, de ≤ 2 * ((PhiSet (H := H)).card : ℝ) / Real.exp ((m : ℝ) * x ^ ε / 2) →
      Real.sqrt e0 ≤ E8 x ε → 3 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-C.cHH) := fun de e0 hde he0 =>
    le_trans (h4 x _ (m : ℝ) _ de e0 hx_4 hfA' (by linarith) hT0 (by rw [Real.log_exp]) hde he0) hsgle
  have hw4 : ∀ u0 (u : W u0), (Fc u0).Dstar / O.Gam ^ 2 / C0S ≤ ((Fc u0).d u : ℝ) := by
    intro u0 u
    obtain ⟨-, -, -, ⟨-, s2, -⟩, -⟩ := hTr u0
    obtain ⟨k1, k2, k3⟩ := hRk u0 u
    exact words_of_count (O.X u0 u) O.Gam ((Fc u0).T u : ℝ) k (O.dst u0 u) (Fc u0).Dstar _ C0S _ (hLW u0 u).1 hGam hfpos hk1
      (hLW u0 u).2.1 (hLv u0 u).1 k1 s2 k2 k3 hC0S2
  have hde : ∀ u0, 0 ≤ (Fc u0).toFam.deF ∧
      (Fc u0).toFam.deF ≤ 2 * ((PhiSet (H := H)).card : ℝ) / Real.exp ((m : ℝ) * x ^ ε / 2) ∧
      ∑ u, (((Fc u0).d u : ℝ) - ((Fc u0).r u : ℝ)) ≤ (Fc u0).toFam.deF * HilbertSchmidtNormSquare.Rs (Fc u0).d := by
    intro u0
    obtain ⟨-, -, -, ⟨-, s2, -⟩, ⟨w1, w2, w3⟩, -⟩ := hTr u0
    have w4 := hw4 u0
    have hRs : 0 < HilbertSchmidtNormSquare.Rs (Fc u0).d :=
      lt_of_lt_of_le (div_pos s2 hsg0) (HilbertSchmidtUnitaryInvariance.wordCount_valid (W u0) (Fc u0).d C0S O.Gam _ (Fc u0).Dstar w1 w2 hsg0 s2.le
        w3 w4)
    refine deF_boundC (Fc u0) _ _ hT0 (fun u => ⟨((hPl u0).2.2.2.2.2 u).2.2.2.2.2.2.2.2.2.1, ?_, ?_⟩) hRs
    · have := (hLv u0 u).1
      have h4f : (4 : ℝ) * ((PhiSet (H := H)).card : ℝ) ≤ ((Fc u0).T u : ℝ) := this
      rw [hfΦ] at h4f
      linarith
    · have h4f : (4 : ℝ) * ((PhiSet (H := H)).card : ℝ) ≤ ((Fc u0).T u : ℝ) := (hLv u0 u).1
      have hTp : (0 : ℝ) < ((Fc u0).T u : ℝ) := by rw [hfΦ] at h4f; linarith
      have hl : (m : ℝ) * Real.log (bTx x ε) / 2 ≤ Real.log ((Fc u0).T u : ℝ) := (hLv u0 u).2.2
      rw [hlb] at hl
      calc Real.exp ((m : ℝ) * x ^ ε / 2) ≤ Real.exp (Real.log ((Fc u0).T u : ℝ)) := Real.exp_le_exp.2 hl
        _ = ((Fc u0).T u : ℝ) := Real.exp_log hTp
  have hs8 : ∀ u0, Real.sqrt (Fc u0).e0 ≤ E8 x ε ∧ 0 ≤ (Fc u0).e0 := fun u0 => by
    obtain ⟨-, -, -, ⟨-, -, -, -, -, -, s7, s8⟩, -⟩ := hTr u0
    exact ⟨s8, s7⟩
  have hLat : ∀ u0, (Fc u0).LatIn (Rw u0) (x ^ (-C.cHH)) O.Gam C0S (E7 x ε) := by
    intro u0
    obtain ⟨d0, d1, d2⟩ := hde u0
    have h := hSg _ _ d1 (hs8 u0).1
    have hq := Real.sqrt_nonneg (2 * (Fc u0).e0)
    have hq' := Real.sqrt_nonneg (Fc u0).toFam.deF
    have h13 : Real.sqrt (Fc u0).toFam.deF ≤ 1 / 3 := by linarith
    have hd4 : (Fc u0).toFam.deF ≤ 1 / 4 := by
      rw [← Real.sq_sqrt d0]
      clear * - h13 hq'
      nlinarith
    exact latIn_of_trace (Fc u0) (Rw u0) x ε _ O.Gam C0S _ (hTr u0) hx0 hsg0 hsg20 hE8sg d0 hd4 d2 (hw4 u0)
  have hsqE : 4 * Real.sqrt (2 * E8 x ε ^ 2) ≤ x ^ (-C.cHH) := by
    have h := hSg 0 (E8 x ε ^ 2) (by positivity) (by rw [Real.sqrt_sq hE80.le])
    rw [Real.sqrt_zero] at h
    linarith
  have hNS : NodeSizes T2 (bTx x ε) (bpTx x ε) η w :=
    LSmall.node_sizes_explicit H m TT T2 x (bTx x ε) (bpTx x ε) η κ off btH w (by linarith) hb0 hbppos hη0 (by linarith) hκ0
      hκ hoff hbtw hNW
  have hfP : fPl H = 2 * (Fintype.card H : ℝ) := hfΦ
  obtain ⟨hco1, hco2⟩ := hcost (fPl H) (by rw [hfP]; linarith) (by rw [hfP]; linarith)
  refine ⟨hLat, hPl, hSub, hc28, hr, ?_, hDiv, ⟨hZ, ZW, hcS⟩, S5, ⟨⟨hk0, t8, ha0.le, haM, hWt, fun t => ?_⟩, hlam⟩, LWn,
    ⟨?_, ?_, ?_⟩, fun u0 => ⟨?_, ?_⟩, ⟨⟨hx1, hε, hε1, hb1, le_refl _, z_nT, hm2, hxm,
      heK0, hk1, hkK, hka, z_L0, ?_, ?_, ?_, hbp0, hkbp, hXpp0, hXppa, hat', ?_, ?_, fun u0 => ?_, ?_, ?_, ?_, hCB'⟩,
      ?_⟩, ⟨hη0, Real.exp_pos _, hbppos, ?_, (Real.exp_pos _).le, hat, hNS, hcut⟩, ⟨hco1, ?_⟩,
    ⟨?_, hTT, hT2, hm1, hkn⟩⟩
  · show 2 * E8 x ε ^ 2 ≤ 1 / 4
    have exp_forty_eq : E8 x ε ≤ 1 / 40 := by linarith
    clear * - exp_forty_eq hE80
    nlinarith
  · show O.bt t ≤ 2 * bpTx x ε
    rw [hbt t]
    have hb2 := (hbtw t.1 t.2).2
    clear * - hb2 hκ hbp0
    nlinarith
  · show Real.log g₁ ≤ XppTx x ε (Fintype.card H : ℝ)
    have e1 : (|K| + 1) * x ^ ε ≤ (|K| + 1) * ((m : ℝ) * x ^ ε) := by gcongr
    have e2 : K * x ^ ε ≤ (|K| + 1) * x ^ ε := by gcongr; linarith
    clear * - e1 e2 hg1b hRW
    linarith
  · show Real.log g₂ ≤ XppTx x ε (Fintype.card H : ℝ)
    have e1 : (|K| + 1) * x ^ ε ≤ (|K| + 1) * ((m : ℝ) * x ^ ε) := by gcongr
    have e2 : K * x ^ ε ≤ (|K| + 1) * x ^ ε := by gcongr; linarith
    clear * - e1 e2 hg2b hRW
    linarith
  · show (c5 + 1) * (m : ℝ) * Real.log (bTx x ε) ≤ XppTx x ε (Fintype.card H : ℝ)
    rw [hlb]
    have e1 : (c5 + 1) * (m : ℝ) * x ^ ε ≤ (|K| + 1) * (m : ℝ) * x ^ ε := by gcongr; linarith
    linarith
  · show 5 * x ^ (-C.cHH) + 3 * Real.sqrt (Fc u0).toFam.deF ≤ 6 * x ^ (-C.cHH)
    have h := hSg _ _ (hde u0).2.1 (hs8 u0).1
    have hq := Real.sqrt_nonneg (2 * (Fc u0).e0)
    linarith
  · show 2 * (Fc u0).e0 ≤ 2 * E8 x ε ^ 2
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hs8 u0).1 2
    rw [Real.sq_sqrt (hs8 u0).2] at h
    linarith
  · show Real.log (bTx x ε) ≤ 2 * x ^ ε
    rw [hlb]; linarith
  · show 0 ≤ Real.log (aTx x ε * (2 * v))
    linarith
  · show Real.log (aTx x ε * (2 * v)) ≤ 2 * x ^ ε
    rw [hLa]; exact hLa2
  · exact threshold_constant_nonneg (H := H) m x ε hx0.le
  · exact (construct_parameter_definitions H W m (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w
      (fun u0 => (Fc u0).toFam)).2.2.2.2.2.1 hx0.le hk0.le
  · obtain ⟨-, -, -, -, ⟨w1, w2, w3⟩, -⟩ := hTr u0
    rw [w3]
    exact HilbertSchmidtUnitaryInvariance.word_log_real k _ (by positivity) hword
  · show E7 x ε ≤ 1 / 2
    have := h7 x (E7 x ε) hx_7 (le_refl _)
    linarith
  · show 0 ≤ 6 * x ^ (-C.cHH)
    linarith
  · show 0 ≤ 2 * E8 x ε ^ 2
    positivity
  · show (6 * x ^ (-C.cHH) + 4 * Real.sqrt (2 * E8 x ε ^ 2)) * (x ^ C.cHH * bTx x ε)
      ≤ K * x ^ ε * (((Fintype.card TT : ℕ) : ℝ) * aTx x ε)
    rw [hcTT]
    have hone : x ^ (-C.cHH) * x ^ C.cHH = 1 := by rw [← Real.rpow_add hx0]; simp
    have hP : 0 < x ^ C.cHH := Real.rpow_pos_of_pos hx0 _
    have r0 : (6 * x ^ (-C.cHH) + 4 * Real.sqrt (2 * E8 x ε ^ 2)) * (x ^ C.cHH * bTx x ε)
        ≤ (7 * x ^ (-C.cHH)) * (x ^ C.cHH * bTx x ε) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have r1 : (7 * x ^ (-C.cHH)) * (x ^ C.cHH * bTx x ε) = 7 * bTx x ε := by
      calc (7 * x ^ (-C.cHH)) * (x ^ C.cHH * bTx x ε) = 7 * (x ^ (-C.cHH) * x ^ C.cHH) * bTx x ε := by ring
        _ = 7 * bTx x ε := by rw [hone]; ring
    have r2 : 28 ≤ K * x ^ ε := by
      clear * - hK28 hxε1
      nlinarith
    have r3 : bTx x ε ≤ (TT.card : ℝ) * aTx x ε := by
      rw [hab]
      have q1 : bTx x ε ≤ x * bTx x ε := by
        clear * - hx1 hb0
        nlinarith
      clear * - q1 hnT1 hb0 hx0
      nlinarith [mul_pos hx0 hb0]
    have r4 : 28 * bTx x ε ≤ K * x ^ ε * ((TT.card : ℝ) * aTx x ε) :=
      mul_le_mul r2 r3 hb0.le (by linarith)
    linarith
  · show bpTx x ε * XpTx x ε ≤ x * bTx x ε
    unfold bpTx
    rw [div_mul_cancel₀ _ (show XpTx x ε ≠ 0 from (Real.exp_pos _).ne')]
    exact le_refl _
  · refine le_trans (mul_le_mul_of_nonneg_left (by linarith) ?_) hco2
    rw [hfP]; positivity
  · show aTx x ε ≤ 2 * x * bTx x ε
    rw [hab]
    clear * - hx0 hb0
    nlinarith [mul_pos hx0 hb0]

theorem card_HA (e : ℕ) : (Fintype.card (HA e) : ℝ) = ((2 ^ e : ℕ) : ℝ) := by
  have hcard : Nat.card (HA e) = 2 ^ e := FrobeniusOrbits.Group.card_H e
  rw [← Nat.card_eq_fintype_card, hcard]

theorem analytic_to_third : Core6ToCore6c := by
  intro ε A c' K cHH eK hε hε4 hA hc'
  obtain ⟨x1, h1⟩ := inputs_fourth_to_third ε A c' K cHH eK hε hε4 hA hc'
  obtain ⟨x2, h2⟩ := modulus_v_eventually ε A hε hA
  refine ⟨max x1 x2, ?_⟩
  rintro Cord eD eL CL eW KW x hx ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, k, C, N, TT, T2, a, btH, w, Fc, Rw, O, Lp,
    P, π, s, sB, BAD, Sig, η, κ, off, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, C0S, heD, heL, hc1, hcHH, hCB, hc28, hPe, -, -, he,
    h25, hg1, hg2, hPer, hL, hB⟩
  obtain ⟨hv1, hv2⟩ := h2 x (le_trans (le_max_right _ _) hx) e q d he h25.2.2.1 h25.2.2.2.1 h25.2.2.2.2.1 h25.2.2.2.2.2.1
  exact ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, glob6 x ε k (hostV e q d) g₁ g₂ C.cHH, C, N, TT, T2, a, w, Fc, Rw, O, Lp, P, π,
    s, sB, BAD, Sig, η, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, C0S, rfl, rfl, heD, heL, hcHH, hPe, he, h25, rfl, hg1, hg2, rfl,
    hPer, hL, fun o ho => h1 x (le_trans (le_max_left _ _) hx) (HA e) (W o) m _ _ k _ C N TT T2 (a o) (w o) (Fc o) (Rw o)
      (O o) η logOm C0 cZ cL cE5 c5 C0S κ off (btH o) g₁ g₂ (by rw [card_HA]; exact he) hv1 hv2 hCB hc28 hc1 hcHH (hB o ho)⟩

theorem log_ne_bound : LogNE := by
  intro ε A hε hA
  obtain ⟨y1, h1⟩ := ((tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop
    (max A 3)).exists_forall_of_atTop
  refine ⟨max 8 y1, fun x hx n q d hn1 hn hq1 hq2 hd1 hd2 => ?_⟩
  have hx8 : 8 ≤ x := le_trans (le_max_left _ _) hx
  have g1 := h1 x (le_trans (le_max_right _ _) hx)
  have hyA : A ≤ x ^ (ε / 5) := le_trans (le_max_left _ _) g1
  have hy3 : 3 ≤ x ^ (ε / 5) := le_trans (le_max_right _ _) g1
  have hx0 : 0 < x := by linarith
  have hL2 : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h := Real.exp_one_lt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have e0 := Real.exp_pos 1
    rw [e2]
    nlinarith
  have hX1 : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := by
    unfold X1; rw [← Real.exp_mul]
  have hX2 : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) := by
    unfold X2; rw [← Real.exp_mul]
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_trans (by rw [hX1]; exact Real.exp_pos _) hq1
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_trans (by rw [hX2]; exact Real.exp_pos _) hd1
  have a1 : x ^ (ε / 5) / 2 < Real.log q := by
    have h := Real.log_lt_log (by rw [hX1]; exact Real.exp_pos _) hq1
    rw [hX1, Real.log_exp] at h
    linarith
  have a2 : Real.log q ≤ x ^ (ε / 5) := by
    have h := Real.log_le_log hq0 hq2
    unfold X1 at h
    rwa [Real.log_exp] at h
  have a3 : x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d := by
    have h := Real.log_lt_log (by rw [hX2]; exact Real.exp_pos _) hd1
    rw [hX2, Real.log_exp] at h
    linarith
  have a4 : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have h := Real.log_le_log hd0 hd2
    unfold X2 at h
    rwa [Real.log_exp] at h
  refine ⟨a1, a2, a3, a4, ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hln : Real.log n ≤ A * Real.log x := by
    have h := Real.log_le_log hn0 hn
    rwa [Real.log_rpow hx0] at h
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  push_cast
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne',
    Real.log_mul (by norm_num) hn0.ne']
  set y : ℝ := x ^ (ε / 5) with hy
  set L : ℝ := Real.log x with hL
  have b1 : A * L ≤ y * L := by gcongr
  have b2 : 2 * y ≤ y * L := by nlinarith
  have b3 : 2 * (y * L) ≤ y * L ^ 2 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y) (by linarith : (0 : ℝ) ≤ L)]
  linarith

theorem no_real_zero_small : Chi8NoRealZero → NoRealZeroSmall := by
  intro h
  refine ⟨fun σ h0 h1 hz => ?_, h⟩
  have := (Formalism.ZeroFreeDirichlet.zeta_negative_real_axis σ h0 h1).2
  rw [hz] at this
  simp at this

theorem chain_analytic_at_point : Chain6At := by
  intro h8
  obtain ⟨c', hc', hHA⟩ := analytic_input_conditional (no_real_zero_small h8) log_ne_bound
  obtain ⟨Cord, hC0, hC2⟩ := lattice_complete_reduction
  obtain ⟨Cd, -, hAt⟩ := chain_at_alt
  refine ⟨Cord, hC0, fun eD eL A K cHH eK CL eW KW ε hε hε4 hA => ?_⟩
  obtain ⟨x1, h1⟩ := analytic_to_third ε A c' K cHH eK hε hε4 hA hc'
  obtain ⟨x2, h2⟩ := analytic_first_to_lattice_discriminant c' hHA ε A hε hA
  obtain ⟨x3, h3⟩ := hC2 ε eW KW hε hε4
  obtain ⟨x4, h4⟩ := x_large_eventually K cHH eK Cd CL ε hε
  refine ⟨max x1 (max x2 (max x3 x4)), fun x hx hCore => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxa := le_trans (le_max_right _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_max_left _ _) hxa
  have hxb := le_trans (le_max_right _ _) hxa
  have hx3 : x3 ≤ x := le_trans (le_max_left _ _) hxb
  have hx4 : x4 ≤ x := le_trans (le_max_right _ _) hxb
  have c6c := h1 Cord eD eL CL eW KW x hx1 hCore
  have c6a := analytic_second_to_first _ _ _ _ _ _ _ _ _ _ _ _ _ (analytic_third_to_second _ _ _ _ _ _ _ _ _ _ _ _ _ c6c)
  have c2d := h2 Cord eD eL K cHH eK CL eW KW x hx2 c6a
  have c2 := h3 eD eL K cHH eK CL x hx3 (lattice_discriminant_reduction _ _ _ _ _ _ _ _ _ _ _ c2d)
  have c0 := first_variant_reduction _ _ _ _ _ _ _ _ (lattice_reduction_to_first_variant _ _ _ _ _ _ _ _ c2)
  exact hAt eD eL ε x ⟨K, cHH, eK, CL, c0, h4 x hx4⟩

section TaParams
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

end TaParams

section DefsD'
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DefsD'

end Formalism.LFunctionChainParameters.LChain6
end
end
