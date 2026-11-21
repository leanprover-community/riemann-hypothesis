import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqOrth
import Formalism.LandauZeroFreeBounds.Statement
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC

section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem inRegion_of_lt {c Z β : ℝ} {q : ℕ} (hc : 0 < c) (hZ : 3 ≤ Z) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Z ^ 2)
    (hβ : 1 - c / 3 / Real.log Z < β) : Formalism.ZeroFreeDirichlet.InRegion c q (β : ℂ) := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]
  have hZpos : 0 < Z := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have h2q : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hZ3 : Real.log (Z ^ 3) = 3 * Real.log Z := by rw [Real.log_pow]; norm_num
  have hle : Real.log ((q : ℝ) * 2) ≤ 3 * Real.log Z := by
    rw [← hZ3]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hdiv : c / 3 / Real.log Z ≤ c / Real.log ((q : ℝ) * 2) := by
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le h2q hle
  linarith

theorem isLZero_changeLevel {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]

theorem page_across (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Z : ℝ) (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (χ₁ : DirichletCharacter ℂ M₁)
      (χ₂ : DirichletCharacter ℂ M₂) (β₁ β₂ : ℝ), 3 ≤ Z → (M₁ : ℝ) ≤ Z → (M₂ : ℝ) ≤ Z →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0 →
      1 - c₀ / Real.log Z < β₁ → 1 - c₀ / Real.log Z < β₂ → β₁ < 1 → β₂ < 1 →
      ∀ n : ℕ, n.Coprime (M₁ * M₂) → χ₁ (n : ZMod M₁) = χ₂ (n : ZMod M₂) := by
  obtain ⟨c, hc, hzfr⟩ := hZ
  refine ⟨c / 3, by positivity, ?_⟩
  intro Z M₁ M₂ _ _ χ₁ χ₂ β₁ β₂ hZ3 hM₁ hM₂ _ _ hne₁ hne₂ hz₁ hz₂ hb₁ hb₂ _ _ n hn
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hq1 : 1 ≤ M₁ * M₂ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hqZ : ((M₁ * M₂ : ℕ) : ℝ) ≤ Z ^ 2 := by
    push_cast
    rw [pow_two]
    exact mul_le_mul hM₁ hM₂ (Nat.cast_nonneg _) (by linarith)

  have hr₁ := inRegion_of_lt hc hZ3 hq1 hqZ hb₁
  have hr₂ := inRegion_of_lt hc hZ3 hq1 hqZ hb₂
  have hL₁ := isLZero_changeLevel (dvd_mul_right M₁ M₂) χ₁ hne₁ hz₁
  have hL₂ := isLZero_changeLevel (dvd_mul_left M₂ M₁) χ₂ hne₂ hz₂
  obtain ⟨-, -, -, -, huniq⟩ := hzfr (M₁ * M₂) _ _ hr₁ hL₁
  have heq := (huniq _ _ hr₂ hL₂).1
  have hv := congrArg (fun ψ : DirichletCharacter ℂ (M₁ * M₂) =>
    ψ ((ZMod.unitOfCoprime n hn : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂))) heq
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_left M₂ M₁),
    ZMod.cast_natCast (dvd_mul_right M₁ M₂)] at hv
  exact hv.symm

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

def clsB (m₀ s a₀ : ℕ) : Finset ℕ :=
  (range (m₀ * s)).filter (fun b => b % m₀ = a₀ % m₀ ∧ b.Coprime s)

def smallCnt (X : ℝ) (M b : ℕ) : ℕ :=
  (((Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).filter (fun p => p % M = b)).card

theorem sum_jacobiSym_eq_sum_residueClass (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) :
    ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) =
      ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ) := by
  have hM : 0 < m₀ * s := Nat.mul_pos hm hs
  have : NeZero s := ⟨hs.ne'⟩
  have hcongr : ∀ q : ℕ, (jacobiSym (q : ℤ) s : ℝ) = (jacobiSym ((q % (m₀ * s) : ℕ) : ℤ) s : ℝ) := by
    intro q
    have h : q ≡ q % (m₀ * s) [MOD s] :=
      Nat.ModEq.of_dvd (dvd_mul_left s m₀) (Nat.mod_modEq q (m₀ * s)).symm
    rw [jacobi_congr h]
  have hzero : ∀ q ∈ PPset m₀ a₀ X, q % (m₀ * s) ∉ clsB m₀ s a₀ →
      (jacobiSym (q : ℤ) s : ℝ) = 0 := by
    intro q hq hnot
    have hqm : q % m₀ = a₀ % m₀ := (Finset.mem_filter.mp hq).2.2.1
    have hnc : ¬ q.Coprime s := by
      intro hc
      apply hnot
      simp only [clsB, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hM, by rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), hqm], ?_⟩
      have hg := (Nat.ModEq.of_dvd (dvd_mul_left s m₀) (Nat.mod_modEq q (m₀ * s))).gcd_eq
      rw [Nat.Coprime, hg]
      exact hc
    have h0 : jacobiSym (q : ℤ) s = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hnc
    rw [h0]
    simp
  symm
  calc ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)
      = ∑ b ∈ clsB m₀ s a₀, ∑ q ∈ PPset m₀ a₀ X,
          if q % (m₀ * s) = b then (jacobiSym (q : ℤ) s : ℝ) else 0 := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hqb := (Finset.mem_filter.mp hq).2
        rw [hcongr q, hqb]
        simp
    _ = ∑ q ∈ PPset m₀ a₀ X, ∑ b ∈ clsB m₀ s a₀,
          if q % (m₀ * s) = b then (jacobiSym (q : ℤ) s : ℝ) else 0 := Finset.sum_comm
    _ = ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.sum_ite_eq]
        by_cases h : q % (m₀ * s) ∈ clsB m₀ s a₀
        · rw [if_pos h]
        · rw [if_neg h, hzero q hq h]

theorem cnt_add_small (m₀ s a₀ : ℕ) (X : ℝ) (b : ℕ) (hb : b ∈ clsB m₀ s a₀) :
    ((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card + smallCnt X (m₀ * s) b = piAP X (m₀ * s) b := by
  obtain ⟨hbr, hbm, -⟩ : b < m₀ * s ∧ b % m₀ = a₀ % m₀ ∧ b.Coprime s := by
    simpa [clsB] using hb
  have hbM : b % (m₀ * s) = b := Nat.mod_eq_of_lt hbr
  have hmod : ∀ p : ℕ, p % (m₀ * s) = b → p % m₀ = a₀ % m₀ := fun p h => by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_right m₀ s), h, hbm]
  have key := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p % (m₀ * s) = b))
    (fun p : ℕ => X ^ (1 / 2 : ℝ) < (p : ℝ))
  unfold piAP
  rw [hbM, ← key]
  congr 1
  · congr 1
    ext p
    simp only [PPset, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, hmod p h5, h4⟩, h5⟩
  · unfold smallCnt
    congr 1
    ext p
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, h4⟩, h5⟩

private theorem sum_card_filter_mod_le_card (T B : Finset ℕ) (M : ℕ) :
    ∑ b ∈ B, (T.filter (fun p => p % M = b)).card ≤ T.card := by
  calc ∑ b ∈ B, (T.filter (fun p => p % M = b)).card
      = ∑ b ∈ B, ∑ p ∈ T, if p % M = b then 1 else 0 := by simp only [Finset.card_filter]
    _ = ∑ p ∈ T, ∑ b ∈ B, if p % M = b then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ T, if p % M ∈ B then 1 else 0 := by simp only [Finset.sum_ite_eq]
    _ ≤ ∑ p ∈ T, 1 := Finset.sum_le_sum (fun p _ => by split_ifs <;> simp)
    _ = T.card := by simp

theorem sum_small_le (m₀ s a₀ : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∑ b ∈ clsB m₀ s a₀, (smallCnt X (m₀ * s) b : ℝ)) ≤ X ^ (1 / 2 : ℝ) := by
  have h1 : ∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b ≤
      ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card :=
    sum_card_filter_mod_le_card _ _ _
  have h2 : ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card ≤ ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    calc _ ≤ (Finset.Icc (1 : ℕ) ⌊X ^ (1 / 2 : ℝ)⌋₊).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.1, Nat.le_floor hp.2.2⟩
      _ = ⌊X ^ (1 / 2 : ℝ)⌋₊ := by simp
  have h3 : (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX _)
  have h4 : ((∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b : ℕ) : ℝ) ≤ (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast h1.trans h2
  push_cast at h4
  linarith

theorem sum_cnt_le (m₀ s a₀ : ℕ) (X : ℝ) :
    (∑ b ∈ clsB m₀ s a₀, (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)) ≤
      ((PPset m₀ a₀ X).card : ℝ) := by
  exact_mod_cast sum_card_filter_mod_le_card (PPset m₀ a₀ X) (clsB m₀ s a₀) (m₀ * s)

theorem abs_jac_le (a : ℤ) (s : ℕ) : |(jacobiSym a s : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a s with h | h | h <;> simp [h]

theorem main_le_two_pi {P m k : ℝ} (hP : 0 ≤ P) (hk : |k| ≤ 1 / 2) (h : |P - m| ≤ k * m) :
    |m| ≤ 2 * P ∧ |P - m| ≤ 2 * |k| * P := by
  have h0 : k * m ≤ |k| * |m| := by rw [← abs_mul]; exact le_abs_self _
  have h1 : |k| * |m| ≤ 1 / 2 * |m| := mul_le_mul_of_nonneg_right hk (abs_nonneg m)
  have h2 : |m| - |P| ≤ |m - P| := abs_sub_abs_le_abs_sub m P
  rw [abs_sub_comm, abs_of_nonneg hP] at h2
  have hm : |m| ≤ 2 * P := by linarith
  refine ⟨hm, ?_⟩
  have h3 : |k| * |m| ≤ |k| * (2 * P) := mul_le_mul_of_nonneg_left hm (abs_nonneg k)
  linarith

private theorem twist_decomposition_bound_of_sum_bounds (C : Finset ℕ) (J N S main : ℕ → ℝ) (k A B : ℝ)
    (hJ : ∀ b, |J b| ≤ 1) (hS0 : ∀ b, 0 ≤ S b)
    (hNb : ∀ b ∈ C, |N b + S b - main b| ≤ 2 * |k| * (N b + S b))
    (hMb : ∀ b ∈ C, |main b| ≤ 2 * (N b + S b))
    (hN : ∑ b ∈ C, N b ≤ A) (hS : ∑ b ∈ C, S b ≤ B) :
    |∑ b ∈ C, J b * N b - ∑ b ∈ C, J b * main b| ≤ 2 * |k| * (A + B) + B ∧
      ∑ b ∈ C, |main b| ≤ 2 * (A + B) := by
  have hk := abs_nonneg k
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have step : ∀ b ∈ C, |J b * N b - J b * main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) := by
      intro b hb
      rw [← mul_sub, abs_mul]
      have h' := abs_le.mp (hNb b hb)
      have e : |N b - main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) :=
        abs_le.mpr ⟨by linarith [h'.1, hS0 b], by linarith [h'.2, hS0 b]⟩
      calc |J b| * |N b - main b| ≤ 1 * |N b - main b| :=
            mul_le_mul_of_nonneg_right (hJ b) (abs_nonneg _)
        _ = |N b - main b| := one_mul _
        _ ≤ _ := e
    refine (Finset.sum_le_sum step).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hA := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * |k|)
    have hB := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 2 * |k|)
    linarith
  · calc ∑ b ∈ C, |main b| ≤ ∑ b ∈ C, 2 * (N b + S b) := Finset.sum_le_sum hMb
      _ = 2 * (∑ b ∈ C, N b + ∑ b ∈ C, S b) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (A + B) := by linarith

theorem twist_decomp (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) (hX : 0 ≤ X)
    (main : ℕ → ℝ) (k : ℝ) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - main b| ≤ k * main b) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) -
        ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * main b| ≤
      2 * |k| * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) ∧
    ∑ b ∈ clsB m₀ s a₀, |main b| ≤ 2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) := by
  have hmain := twist_decomposition_bound_of_sum_bounds (clsB m₀ s a₀) (fun b => (jacobiSym (b : ℤ) s : ℝ))
    (fun b => (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ))
    (fun b => (smallCnt X (m₀ * s) b : ℝ)) main k ((PPset m₀ a₀ X).card : ℝ) (X ^ (1 / 2 : ℝ))
    (fun b => abs_jac_le _ _) (fun b => Nat.cast_nonneg _)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).2
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).1
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (sum_cnt_le m₀ s a₀ X) (sum_small_le m₀ s a₀ X hX)
  rw [sum_jacobiSym_eq_sum_residueClass m₀ s a₀ X hm hs]
  exact hmain

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem coprime_of_cls {m₀ s a₀ b : ℕ} (ha : a₀.Coprime m₀) (hb : b ∈ clsB m₀ s a₀) : b.Coprime (m₀ * s) := by
  simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb
  have hm : b.Coprime m₀ := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hb.2.1, ← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  exact Nat.Coprime.mul_right hm hb.2.2

private theorem sum_clsB_mul_mod_eq_sum {M : Type*} [AddCommMonoid M] (m₀ s a₀ u : ℕ) (hN : 0 < m₀ * s)
    (hu1 : u % m₀ = 1 % m₀) (hus : u.Coprime s) (f : ℕ → M) :
    ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s)) = ∑ b ∈ clsB m₀ s a₀, f b := by
  have hcm : ∀ x k : ℕ, Nat.Coprime x k ↔ Nat.Coprime (x % k) k := fun x k => by
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  have hum : u.Coprime m₀ := by
    rw [hcm, hu1, ← hcm]
    exact Nat.coprime_one_left _
  have huN : u.Coprime (m₀ * s) := Nat.Coprime.mul_right hum hus
  have hmap : ∀ b ∈ clsB m₀ s a₀, (b * u) % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro b hb
    simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hN, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), Nat.mul_mod, hb.2.1, hu1, ← Nat.mul_mod, mul_one]
    · rw [hcm, Nat.mod_mod_of_dvd _ (dvd_mul_left s m₀), ← hcm]
      exact Nat.Coprime.mul hb.2.2 hus
  have hinj : Set.InjOn (fun b => (b * u) % (m₀ * s)) (clsB m₀ s a₀) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, clsB, Finset.mem_filter, Finset.mem_range] at hx hy
    have h := Nat.ModEq.cancel_right_of_coprime huN.symm (show x * u ≡ y * u [MOD m₀ * s] from hxy)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  have himg : (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)) = clsB m₀ s a₀ :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmap)
      (by rw [Finset.card_image_of_injOn hinj])
  calc ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s))
      = ∑ x ∈ (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)), f x := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ clsB m₀ s a₀, f b := by rw [himg]

private theorem jacobiSym_mul_mod_eq_mul (m₀ s b u : ℕ) :
    jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s = jacobiSym (b : ℤ) s * jacobiSym (u : ℤ) s := by
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)

private theorem exists_jacobiSym_neg_one_in_residue_class (m₀ s : ℕ) (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s)
    (hcop : m₀.Coprime s) :
    ∃ u : ℕ, u % m₀ = 1 % m₀ ∧ u.Coprime s ∧ jacobiSym (u : ℤ) s = -1 := by
  have hp : s.minFac.Prime := Nat.minFac_prime (by omega)
  haveI := Fact.mk hp
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨t, ht⟩ := Nat.minFac_dvd s
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  haveI : NeZero t := ⟨ht0⟩
  haveI : NeZero s.minFac := ⟨hp.ne_zero⟩
  have hp2 : s.minFac ≠ 2 := by
    intro h2
    rw [h2] at ht
    rw [ht] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul t)
  have hpt : s.minFac.Coprime t := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨v, hv⟩
    have hu := hsq s.minFac ⟨v, by rw [mul_assoc, ← hv]; exact ht⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
  have hmp : (m₀ * t).Coprime s.minFac :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.minFac_dvd s) hcop) hpt.symm
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod s.minFac)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  let c := Nat.chineseRemainder hmp 1 g.val
  have hc1 : (c : ℕ) ≡ 1 [MOD m₀ * t] := c.2.1
  have hc2 : (c : ℕ) ≡ g.val [MOD s.minFac] := c.2.2
  have hJ : jacobiSym ((c : ℕ) : ℤ) s = -1 := by
    have e1 : jacobiSym ((c : ℕ) : ℤ) s.minFac = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      have hcg : (((c : ℕ) : ℤ) : ZMod s.minFac) = g := by
        rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc2, ZMod.natCast_zmod_val]
      rwa [hcg]
    have e2 : jacobiSym ((c : ℕ) : ℤ) t = 1 := by
      have hct : (c : ℕ) ≡ 1 [MOD t] := Nat.ModEq.of_mul_left m₀ hc1
      have h' : (((c : ℕ) % t : ℕ) : ℤ) = ((1 % t : ℕ) : ℤ) := congrArg _ hct
      push_cast at h'
      rw [jacobiSym.mod_left' h', jacobiSym.one_left]
    have hsplit : jacobiSym ((c : ℕ) : ℤ) s = jacobiSym ((c : ℕ) : ℤ) (s.minFac * t) := by rw [← ht]
    rw [hsplit, jacobiSym.mul_right, e1, e2]
    norm_num
  refine ⟨c, Nat.ModEq.of_mul_right t hc1, ?_, hJ⟩
  have hg1 : Int.gcd ((c : ℕ) : ℤ) s = 1 := by
    by_contra hne
    have h0 := jacobiSym.eq_zero_iff_not_coprime.mpr hne
    rw [hJ] at h0
    norm_num at h0
  rwa [Int.gcd_natCast_natCast] at hg1

theorem sum_jac_cls_eq_zero (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) :
    ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨u, hu1, hus, hJu⟩ := exists_jacobiSym_neg_one_in_residue_class m₀ s h1 hodd hsq hcop
  have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus (fun x => (jacobiSym (x : ℤ) s : ℝ))
  simp only [jacobiSym_mul_mod_eq_mul, hJu, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
    Finset.sum_neg_distrib] at hre
  linarith

theorem main_twist_bound (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hli : 0 < liX X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X| ≤
      2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hφ : (0 : ℝ) < ((m₀ * s).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hN
  have hsum0 := sum_jac_cls_eq_zero m₀ s a₀ h1 hodd hsq hcop ha
  have hRHS : 0 ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by positivity
  rcases e with _ | ⟨χ, β⟩
  · simp only [mainAP]
    rw [← Finset.sum_mul, hsum0, zero_mul, abs_zero]
    simpa [mainAP] using hRHS
  · have hexp : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP (some (χ, β)) b X =
        -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
          ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re := by
      simp only [mainAP]
      rw [Finset.mul_sum]
      have key : ∀ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
          ((liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β)) / ((m₀ * s).totient : ℝ)) =
          (jacobiSym (b : ℤ) s : ℝ) * (liX X / ((m₀ * s).totient : ℝ)) +
          -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
            ((jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re) := fun b _ => by ring
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, hsum0, zero_mul, zero_add]
    have hre1 : ∀ b : ℕ, |(χ (b : ZMod (m₀ * s))).re| ≤ 1 := fun b =>
      (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
    by_cases hc : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s →
        χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
    · have hLb := hG χ β rfl hc
      have hS : |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| ≤
          ((clsB m₀ s a₀).card : ℝ) := by
        calc _ ≤ ∑ b ∈ clsB m₀ s a₀, |(jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ clsB m₀ s a₀, (1 : ℝ) := Finset.sum_le_sum fun b _ => by
              rw [abs_mul]
              have hj : |(jacobiSym (b : ℤ) s : ℝ)| ≤ 1 := by
                rcases jacobiSym.trichotomy (b : ℤ) s with h | h | h <;> simp [h]
              calc _ ≤ 1 * 1 := mul_le_mul hj (hre1 b) (abs_nonneg _) zero_le_one
                _ = 1 := one_mul 1
          _ = ((clsB m₀ s a₀).card : ℝ) := by simp
      have hlow : ∀ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) ≤ |mainAP (some (χ, β)) b X| := by
        intro b _
        have h3 : (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ r * liX X := by
          calc (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ |(χ (b : ZMod (m₀ * s))).re * liX (X ^ β)| :=
                le_abs_self _
            _ = |(χ (b : ZMod (m₀ * s))).re| * |liX (X ^ β)| := abs_mul _ _
            _ ≤ 1 * |liX (X ^ β)| := mul_le_mul_of_nonneg_right (hre1 b) (abs_nonneg _)
            _ ≤ r * liX X := by linarith
        refine le_trans ?_ (le_abs_self _)
        simp only [mainAP]
        rw [div_le_div_iff₀ (by positivity) hφ]
        have h4 : liX X / 2 ≤ liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) := by nlinarith
        nlinarith
      rw [hexp, abs_mul, abs_neg, abs_div, abs_of_pos hφ]
      calc |liX (X ^ β)| / ((m₀ * s).totient : ℝ) *
            |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re|
          ≤ r * liX X / ((m₀ * s).totient : ℝ) * ((clsB m₀ s a₀).card : ℝ) :=
            mul_le_mul (div_le_div_of_nonneg_right hLb hφ.le) hS (abs_nonneg _) (by positivity)
        _ = 2 * r * ∑ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp
        _ ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP (some (χ, β)) b X| :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlow) (by linarith)
    · push_neg at hc
      obtain ⟨u, hu1, hus, hne⟩ := hc
      have hpt : ∀ b : ℕ, (((jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s : ℝ)) : ℂ) *
          χ ((((b * u) % (m₀ * s) : ℕ)) : ZMod (m₀ * s)) =
          (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) *
            ((((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s))) := by
        intro b
        rw [jacobiSym_mul_mod_eq_mul, ZMod.natCast_mod, Nat.cast_mul, map_mul]
        push_cast
        ring
      have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus
        (fun x => (((jacobiSym (x : ℤ) s : ℝ)) : ℂ) * χ (x : ZMod (m₀ * s)))
      simp only [hpt] at hre
      rw [← Finset.mul_sum] at hre
      have hgcd : Int.gcd (u : ℤ) s = 1 := by rw [Int.gcd_natCast_natCast]; exact hus
      have hc1 : (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) ≠ 1 := by
        rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          simpa using hh
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          linear_combination -hh
      have hT : ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
        have h0 : ((((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) - 1) *
            ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
          rw [sub_mul, hre, one_mul, sub_self]
        exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc1)
      have hS0 : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re = 0 := by
        have h0 := congrArg Complex.re hT
        rw [Complex.re_sum] at h0
        simpa [Complex.re_ofReal_mul] using h0
      rw [hexp, hS0, mul_zero, abs_zero]
      exact hRHS

theorem twist_one (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r k : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hX : 0 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hli : 0 < liX X) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP e b X| ≤ k * mainAP e b X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (4 * r + 2 * |k|) * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) := by
  have hs : 0 < s := by omega
  obtain ⟨hd, hsumabs⟩ := twist_decomp m₀ s a₀ X hm hs hX (fun b => mainAP e b X) k hk hb
  beta_reduce at hd hsumabs
  have hmain := main_twist_bound m₀ s a₀ hm h1 hodd hsq hcop ha X r e hr0 hr hli hG
  have h2 : 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| ≤
      2 * r * (2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hsumabs (by linarith)
  have h3 := abs_sub_abs_le_abs_sub (∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ))
    (∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X)
  nlinarith [hd, hmain, h2, h3, abs_nonneg k]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

set_option maxHeartbeats 1000000 in
theorem twist_bound (hP : PNTAPRelW) (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊x ^ 400⌋₊ ^ 2 → s ≠ nstar →
      |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤ x ^ (-3 : ℝ) * ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨x₁, hx₁⟩ := count_a hP hE ε hε
  obtain ⟨c₀, hc₀, hpage⟩ := page_across hZ
  obtain ⟨c₃, A₀, C₀, hc₃, H⟩ := hP
  have H' : ∀ M : ℕ, ∃ e : Option (DirichletCharacter ℂ M × ℝ), ∀ (hM : 0 < M), 8 ∣ M →
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → @IsExcPair M ⟨hM.ne'⟩ p.1 p.2) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X := by
    intro M
    by_cases h : 0 < M ∧ 8 ∣ M
    · obtain ⟨e, he1, _, he3⟩ := @H M ⟨h.1.ne'⟩ h.2
      exact ⟨e, fun _ _ => ⟨he1, he3⟩⟩
    · exact ⟨none, fun hM h8 => absurd ⟨hM, h8⟩ h⟩
  choose E hE using H'
  obtain ⟨x₂, hx₂⟩ := eventually_log_cube (200 + 16 / c₃) (ε / 6) (by positivity) (by positivity)
  set L₀ : ℝ := max (max 2 (8 * (ε / 5 + 5 + Real.log 128) / c₀))
    (max (max (8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃) (Real.log (32 * (|A₀| + 1))))
      (8 * |C₀| * (Real.log 806 + ε / 5 + 1))) with hL₀
  refine ⟨max (max x₁ x₂) (Real.exp L₀), ?_⟩
  intro x X m₀ a₀ hx hm h8 ha hX1 hX2 hX3
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxL : Real.exp L₀ ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxL
  have hLL : L₀ ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxL
  have hL1 : 2 ≤ Real.log x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hL2 : 8 * (ε / 5 + 5 + Real.log 128) / c₀ ≤ Real.log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL3 : 8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃ ≤ Real.log x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL4 : Real.log (32 * (|A₀| + 1)) ≤ Real.log x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL5 : 8 * |C₀| * (Real.log 806 + ε / 5 + 1) ≤ Real.log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  have hu2 : (200 + 16 / c₃) * Real.log x ^ 3 ≤ Real.log X := (hx₂ x hxx₂).trans hX2
  have hu0 : 0 < Real.log X := by
    have : 0 < (200 + 16 / c₃) * Real.log x ^ 3 := by positivity
    linarith
  rcases le_or_gt X 0 with hXn | hXp
  · refine ⟨0, fun s _ _ _ _ _ _ => ?_⟩
    have : PPset m₀ a₀ X = ∅ := by
      unfold PPset; rw [Nat.floor_of_nonpos hXn]; simp
    simp [this]

  have hm8 : 8 ≤ m₀ := Nat.le_of_dvd hm h8
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : 2 ≤ Real.log 8 := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hX4 : 4 ≤ X := by
    have h4 : Real.log 4 ≤ Real.log X := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      have : (8 : ℝ) ≤ Real.log x ^ 3 := by nlinarith
      have : 0 ≤ 16 / c₃ * Real.log x ^ 3 := by positivity
      nlinarith
    exact (Real.log_le_log_iff (by norm_num) hXp).mp h4
  set N := ⌊x ^ 400⌋₊ with hN
  have hx400 : 1 ≤ x ^ 400 := one_le_pow₀ hx1
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx400)
  have hNx : (N : ℝ) ≤ x ^ 400 := Nat.floor_le (by linarith)
  have hlogN : Real.log N ≤ 400 * Real.log x := by
    have := Real.log_le_log (by exact_mod_cast hN1) hNx
    rwa [Real.log_pow] at this
  set Z : ℝ := ((m₀ * N ^ 2 : ℕ) : ℝ) with hZdef
  have hZ3 : 3 ≤ Z := by
    have : 8 ≤ m₀ * N ^ 2 := le_trans hm8 (Nat.le_mul_of_pos_right _ (by positivity))
    simp only [hZdef]; exact_mod_cast (show 3 ≤ m₀ * N ^ 2 by omega)
  have hm0 : (0 : ℝ) < m₀ := by exact_mod_cast hm
  have hℓ : Real.log Z ≤ Real.log m₀ + 800 * Real.log x := by
    simp only [hZdef]; push_cast
    rw [Real.log_mul hm0.ne' (by positivity), Real.log_pow]
    push_cast; linarith
  have hℓm : Real.log m₀ ≤ 4 * Real.exp (ε / 5 * Real.log x) := by
    have hxe : x ^ (ε / 5) = Real.exp (ε / 5 * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, mul_comm]
    have hLp : 0 < Real.log x ^ 2 := by positivity
    have h := hX1.trans hX3
    rw [hxe] at h
    have : Real.log m₀ / 4 * Real.log x ^ 2 ≤ Real.exp (ε / 5 * Real.log x) * Real.log x ^ 2 := by linarith
    have := le_of_mul_le_mul_right this hLp
    linarith
  have hlogu : Real.log (Real.log X) ≤ (ε / 5 + 2) * Real.log x := by
    have hLp : 0 < Real.log x := by linarith
    calc Real.log (Real.log X) ≤ Real.log (x ^ (ε / 5) * Real.log x ^ 2) := Real.log_le_log hu0 hX3
      _ = ε / 5 * Real.log x + 2 * Real.log (Real.log x) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_pow]; push_cast; ring
      _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos hLp
          nlinarith

  let bad : ℕ → Prop := fun s => 1 < s ∧ Odd s ∧ Squarefree s ∧ s.Coprime m₀ ∧ s ≤ N ^ 2 ∧
      ∃ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), E (m₀ * s) = some (χ, β) ∧ 1 - β < c₀ / Real.log Z ∧
        ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
  have hMZ : ∀ t, t ≤ N ^ 2 → ((m₀ * t : ℕ) : ℝ) ≤ Z := fun t ht => by
    simp only [hZdef]; exact_mod_cast Nat.mul_le_mul_left m₀ ht
  have huniq : ∀ s₁ s₂, bad s₁ → bad s₂ → s₁ = s₂ := by
    rintro s₁ s₂ ⟨h11, ho1, hq1, hc1, hN1', χ₁, β₁, he1, hlt1, hal1⟩ ⟨h12, ho2, hq2, hc2, hN2', χ₂, β₂, he2, hlt2, hal2⟩
    have hM1 : 0 < m₀ * s₁ := Nat.mul_pos hm (by omega)
    have hM2 : 0 < m₀ * s₂ := Nat.mul_pos hm (by omega)
    have : NeZero (m₀ * s₁) := ⟨hM1.ne'⟩
    have : NeZero (m₀ * s₂) := ⟨hM2.ne'⟩
    obtain ⟨sq1, ne1, L1, _, lt1⟩ := (hE (m₀ * s₁) hM1 (dvd_mul_of_dvd_left h8 _)).1 _ he1
    obtain ⟨sq2, ne2, L2, _, lt2⟩ := (hE (m₀ * s₂) hM2 (dvd_mul_of_dvd_left h8 _)).1 _ he2
    have hag := hpage Z (m₀ * s₁) (m₀ * s₂) χ₁ χ₂ β₁ β₂ hZ3 (hMZ _ hN1') (hMZ _ hN2') sq1 sq2 ne1 ne2 L1 L2
      (by linarith) (by linarith) lt1 lt2
    apply jacobi_separate m₀ s₁ s₂ hm ho1 ho2 hq1 hq2 hc1 hc2
    intro u hu hus
    have hum : u.Coprime m₀ := by
      unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq (show u ≡ 1 [MOD m₀] from hu)]; simp
    have hu1 : u.Coprime s₁ := (Nat.coprime_mul_iff_right.mp hus).1
    have hu2' : u.Coprime s₂ := (Nat.coprime_mul_iff_right.mp hus).2
    have hn : u.Coprime ((m₀ * s₁) * (m₀ * s₂)) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right hum hu1) (Nat.Coprime.mul_right hum hu2')
    have := hag u hn
    rw [hal1 u hu hu1, hal2 u hu hu2'] at this
    exact_mod_cast this
  refine ⟨if h : ∃ s, bad s then Classical.choose h else 0, ?_⟩
  intro s h1 hodd hsq hcop hsN hne
  have hnb : ¬ bad s := by
    intro hb
    have hex : ∃ s, bad s := ⟨s, hb⟩
    rw [dif_pos hex] at hne
    exact hne (huniq _ _ hb (Classical.choose_spec hex))
  have hM : 0 < m₀ * s := Nat.mul_pos hm (by omega)
  have h8M : 8 ∣ m₀ * s := dvd_mul_of_dvd_left h8 s
  have : NeZero (m₀ * s) := ⟨hM.ne'⟩
  obtain ⟨hEx, hPNT⟩ := hE (m₀ * s) hM h8M
  have hlm0 : 2 ≤ Real.log ((m₀ * s : ℕ) : ℝ) := by
    have : (8 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by
      exact_mod_cast le_trans hm8 (Nat.le_mul_of_pos_right _ (by omega))
    linarith [Real.log_le_log (by norm_num) this]
  have hlm : Real.log ((m₀ * s : ℕ) : ℝ) ≤ Real.log Z :=
    Real.log_le_log (by exact_mod_cast hM) (hMZ s hsN)
  obtain ⟨f1, f2, f3, f4⟩ := final_ineq ε c₀ c₃ A₀ C₀ (Real.log x) (Real.log X) (Real.log ((m₀ * s : ℕ) : ℝ))
    (Real.log m₀) (Real.log Z) hε hc₀ hc₃ hL1 hL2 hL3 hL4 hL5 hX1 hu2 hlogu hℓm hlm0 hlm hℓ
  set η : ℝ := Real.exp (-(3 * Real.log x)) with hη
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hxη : x ^ (-3 : ℝ) = η := by rw [Real.rpow_def_of_pos hx0, hη]; ring_nf
  set ρ : ℝ := Real.exp (-(c₃ * Real.log X / Real.log ((m₀ * s : ℕ) : ℝ))) +
    Real.exp (-Real.sqrt (c₃ * Real.log X)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set k : ℝ := A₀ * ρ with hk
  have hkabs : |k| = |A₀| * ρ := by rw [hk, abs_mul, abs_of_pos hρ0]
  have hk2 : 2 * |k| ≤ η / 8 := by rw [hkabs, ← mul_assoc]; exact f3
  have hk' : |k| ≤ 1 / 2 := by linarith
  set r : ℝ := 4 * Real.log X * Real.exp (-(c₀ / Real.log Z * Real.log X)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr4 : 4 * r ≤ η / 8 := by
    have : 4 * r = 16 * Real.log X * Real.exp (-(c₀ / Real.log Z * Real.log X)) := by rw [hr]; ring
    rw [this]; exact f2
  have hr' : r ≤ 1 / 2 := by linarith
  have hli : 0 < liX X := lt_of_lt_of_le (by positivity) (liX_lower hX4)
  have hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP (E (m₀ * s)) b X| ≤
      k * mainAP (E (m₀ * s)) b X :=
    fun b hbB => hPNT X b (by linarith) f1 (coprime_of_cls ha hbB)
  have hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), E (m₀ * s) = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X := by
    intro χ β heq hal
    obtain ⟨_, _, _, hβl, _⟩ := hEx (χ, β) heq
    have hβ2 : β ≤ 1 - c₀ / Real.log Z := by
      by_contra hc
      exact hnb ⟨h1, hodd, hsq, hcop, hsN, χ, β, heq, by linarith, hal⟩
    have hβ1 : 1 / 2 ≤ β := by
      have : 1 / (8 * Real.log ((m₀ * s : ℕ) : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      simp only at hβl
      linarith
    exact liX_pow_le hX4 hβ1 hβ2
  have hmain := twist_one m₀ s a₀ hm h1 hodd hsq hcop.symm ha X r k (E (m₀ * s)) hXp.le hr0 hr' hli hk' hb hG
  have hcount := hx₁ x X m₀ a₀ hxx₁ hm h8 ha hX1 hX2 hX3
  set P : ℝ := ((PPset m₀ a₀ X).card : ℝ)
  set d : ℝ := Real.exp (-(2 / 5 * Real.log X))
  have hsq2 : X ^ (1 / 2 : ℝ) ≤ d * P := by
    have e : X ^ (1 / 2 : ℝ) = X ^ (-(2 / 5) : ℝ) * X ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hXp]; norm_num
    have e2 : X ^ (-(2 / 5) : ℝ) = d := by
      rw [Real.rpow_def_of_pos hXp]; show _ = Real.exp _; congr 1; ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := (Real.exp_pos _).le
  have ha4 : 4 * r + 2 * |k| ≤ η / 4 := by linarith
  have t1 : (4 * r + 2 * |k|) * (P + X ^ (1 / 2 : ℝ)) ≤ η / 4 * (P + d * P) :=
    mul_le_mul ha4 (by linarith) (add_nonneg hP0 (Real.rpow_nonneg hXp.le _)) (by linarith)
  have t2 : d * P ≤ η / 4 * P := mul_le_mul_of_nonneg_right f4 hP0
  have t3 : η / 4 * (d * P) ≤ η / 4 * (1 / 4 * P) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hP0) (by linarith)
  rw [hxη]
  have : η / 4 * (P + d * P) = η / 4 * P + η / 4 * (d * P) := by ring
  have hηP : 0 ≤ η * P := mul_nonneg hη0 hP0
  have e3 : η / 4 * (1 / 4 * P) = η * P / 16 := by ring
  have e4 : η / 4 * P = η * P / 4 := by ring
  have e5 : (-3 : ℝ) = -3 := rfl
  linarith

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
