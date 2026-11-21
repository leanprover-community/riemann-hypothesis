import Mathlib
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SignatureAndNodeGaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.IndefiniteRowSideFullHecke.SignatureAndNodeGaps GlobalTheory.Chain.ItPairCompare

namespace GlobalTheory.Chain.ParOfSizes

section HC

variable {R : Ranks} (P : HCParam R) {h₀ : ℝ}

theorem b_le_of_le {i j : Fin R.m} (h : i.1 ≤ j.1) : P.b i ≤ P.b j := by
  rcases h.lt_or_eq with hlt | heq
  ·
    have h1 := gap_of_lt P hlt
    have h2 := gap_of_le P (le_refl i.1)
    have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
    linarith
  · exact le_of_eq (congrArg P.b (Fin.ext heq))

theorem le_b_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    {i j : Fin R.m} (h : i.1 < j.1) : h₀ ≤ ((P.b j - P.b i : ℚ) : ℝ) := by
  have hi : i.1 + 1 < R.m := by omega

  have hstep := hg i.1 hi
  have hmono : P.b ⟨i.1 + 1, hi⟩ ≤ P.b j := b_le_of_le P (show i.1 + 1 ≤ j.1 by omega)
  have hq : (P.b ⟨i.1 + 1, hi⟩ - P.b ⟨i.1, by omega⟩ : ℚ) ≤ P.b j - P.b i := by
    have e : (⟨i.1, by omega⟩ : Fin R.m) = i := Fin.ext rfl
    rw [e]
    linarith
  exact hstep.trans (by exact_mod_cast hq)

theorem hermitianParam_oppositeSign_entries_dist_ge_gap (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (x y : Idx R j) (hx : sgn R j x = false) (hy : sgn R j y = true) :
    h₀ ≤ |((val P j x - val P j y : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs]
  rcases x with a | i | a
  · simp [sgn] at hx
  · simp only [sgn, decide_eq_false_iff_not, not_or, not_le] at hx
    obtain ⟨hij, hodd⟩ := hx
    have hi1 : i.1 - 1 < R.m := by omega
    rcases y with c | i2 | ⟨⟨i2, hi2⟩, a⟩
    ·
      have h1 := neg_b_lt_v P c ⟨i.1 - 1, hi1⟩
      have h2 := le_b_sub P hg (i := ⟨i.1 - 1, hi1⟩) (j := i) (show i.1 - 1 < i.1 by omega)
      refine h2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
    · simp only [sgn, decide_eq_true_eq] at hy
      rcases lt_trichotomy i2.1 i.1 with h2 | h2 | h2
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        rw [abs_sub_comm]
        exact le_abs.mpr (Or.inl (by linarith))
      · exfalso
        rw [h2] at hy
        rcases hy with hy | hy
        · omega
        · exact hodd hy
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        exact le_abs.mpr (Or.inl (by linarith))
    ·
      have hi3 : i2.1 + 1 < R.m := by omega
      have g1 := gap_of_lt P (i := i2) (j := ⟨i2.1 + 1, hi3⟩) (show i2.1 < i2.1 + 1 by omega)
      have g2 := le_b_sub P hg (i := ⟨i2.1 + 1, hi3⟩) (j := i) (show i2.1 + 1 < i.1 by omega)
      have ha0 : (0 : ℚ) ≤ (a.1 : ℚ) := Nat.cast_nonneg _
      have ha1 : (a.1 : ℚ) + 1 ≤ R.t := by exact_mod_cast a.2
      refine g2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
  · simp [sgn] at hx

theorem le_val_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (c : ℚ) (x y : Idx R j) (h : sgn R j x ≠ sgn R j y) :
    h₀ ≤ |(((val P j x + c) - (val P j y + c) : ℚ) : ℝ)| := by
  rw [add_sub_add_right_eq_sub]
  by_cases hx : sgn R j x = false
  · have hy : sgn R j y = true := by
      cases hy' : sgn R j y
      · exact absurd (hx.trans hy'.symm) h
      · rfl
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j x y hx hy
  · have hx' : sgn R j x = true := by simpa using hx
    have hy : sgn R j y = false := by
      cases hy' : sgn R j y
      · rfl
      · exact absurd (hx'.trans hy'.symm) h
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j y x hy hx'

end HC

end GlobalTheory.Chain.ParOfSizes

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes

namespace GlobalTheory.Chain.ParOfNodeGap

theorem minSig_lamS_le {D : D7} (k : Fin D.R.m) (τ : D.what₂.Tau) : minSig (lamS D k τ) ≤ D.R.m := by
  unfold minSig
  refine (min_le_right _ _).trans ?_
  calc ((lamS D k τ).filter fun x => x.2 = false).card
      ≤ (Finset.univ.image fun i : Fin D.R.m =>
          ((val (D.hc τ) (k : ℕ) (Sum.inr (Sum.inl i)) + (D.hc τ).e k : ℚ), false)).card := by
        apply Finset.card_le_card
        rintro ⟨a, s⟩ hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx, hs⟩ := hx
        simp only at hs
        subst hs
        obtain ⟨y, hy, hsy⟩ := (mem_lamS k τ a false).1 hx
        rcases y with y | y | y
        · simp [sgn] at hsy
        · exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, by rw [hy]⟩
        · simp [sgn] at hsy
    _ ≤ (Finset.univ : Finset (Fin D.R.m)).card := Finset.card_image_le
    _ = D.R.m := by simp

theorem num_bound' {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 2 ≤ m) (hN : 3 * m ^ 2 ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (N : ℝ) ^ 3 := by
  have hqm : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
        positivity
      · rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr h
        · norm_num
    refine h1.trans ?_
    have : (q : ℝ) ≤ m := by exact_mod_cast hq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNR : 3 * (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN12 : (12 : ℝ) ≤ N := by nlinarith
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hqm hpos (by positivity)
    _ ≤ 120 * (N : ℝ) * ((N : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 40 * (N : ℝ) ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (by linarith : (0 : ℝ) ≤ N - 10)]

private theorem le_sub_b_succ_of_nodeGap {D : D7} {h : ℝ} (H : D.NodeGap h) (τ : D.what₂.Tau) :
    ∀ (i : ℕ) (hi : i + 1 < D.R.m), h ≤ (((D.hc τ).b ⟨i + 1, hi⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
  intro i hi
  have := H D.u₀ τ i hi
  rwa [D.hcW_base] at this

private theorem rankY_le_N (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.rankY j ≤ D.R.N D.R.m := by
  have h1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul hj le_rfl
  simp only [Ranks.rankY, Ranks.r, Ranks.N]
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem three_mul_m_sq_le_N (D : D7) : 3 * D.R.m ^ 2 ≤ D.R.N D.R.m := by
  have h1 : 3 * D.R.m + 1 ≤ D.R.t := D.R.three_m_lt_t
  have h2 : D.R.m * (3 * D.R.m + 1) ≤ D.R.m * D.R.t := Nat.mul_le_mul le_rfl h1
  simp only [Ranks.N]
  nlinarith

theorem stepGap_of_nodeGap {D : D7} (h : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6))
    (k : Fin D.R.m) : StepGap D k := by
  set H : ℝ := 4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6 with hH
  have hg := le_sub_b_succ_of_nodeGap h
  have hNpos : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcube : ∀ j : ℕ, j ≤ D.R.m → ((D.R.rankY j : ℕ) : ℝ) ^ 3 < H := by
    intro j hj
    have : ((D.R.rankY j : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := by exact_mod_cast rankY_le_N D hj
    have : ((D.R.rankY j : ℕ) : ℝ) ^ 3 ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_nonneg hNpos 3]
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    refine le_trans ?_ (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
    have hb := num_bound' (minSig_lamS_le k τ) (rankY_le_N D k.isLt.le) D.R.two_le_m (three_mul_m_sq_le_N D)
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith

theorem chainPar_of_nodeGap :
    ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) → ∀ k, GlobalTheory.Chain.ChainPar D k := by
  intro D h k
  exact (chainPar_iff_stepGap k).mpr (stepGap_of_nodeGap h k)

end GlobalTheory.Chain.ParOfNodeGap

end
end
