import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset ArithmeticFunction

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2



theorem finite_splitting_of_group : GFiniteSplit := by
  intro q _ χ x z hx hxz
  unfold Gchi Sz tailL cN
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊z⌋₊ := Icc_subset_Icc le_rfl (Nat.floor_le_floor hxz)
  have e1 : (∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn.2
      rw [min_eq_left ((one_le_div hn0).2 hle)]
    · intro n hn hn'
      rw [mem_Icc] at hn hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have : x < n := by
        by_contra hc
        exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
      rw [min_eq_right ((div_le_one hn0).2 this.le)]; simp
  rw [e1]
  have : ∀ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) - ((Λ n * min 1 (x / n) : ℝ) : ℂ) * χ (n : ZMod q) := by
    intro n _; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem markov_discard_bound : MarkovDiscard := by
  intro P B J S V t ht hS hlt
  by_contra hcon
  push Not at hcon
  have hcov : P ⊆ B ∪ (Finset.univ.biUnion fun j => P.filter fun q => t < |S j q|) := by
    intro q hq
    by_cases hB : q ∈ B
    · exact mem_union_left _ hB
    · obtain ⟨j, hj⟩ := hcon q hq hB
      exact mem_union_right _ (mem_biUnion.2 ⟨j, mem_univ _, mem_filter.2 ⟨hq, hj⟩⟩)
  have hj : ∀ j, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) ≤ V / t ^ 2 * P.card := by
    intro j
    have h1 : (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) * t ^ 2 ≤ ∑ q ∈ P, S j q ^ 2 := by
      calc (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) * t ^ 2
          = ∑ q ∈ P.filter (fun q => t < |S j q|), t ^ 2 := by simp
        _ ≤ ∑ q ∈ P.filter (fun q => t < |S j q|), S j q ^ 2 := by
            apply Finset.sum_le_sum
            intro q hq
            have := (mem_filter.1 hq).2
            rw [← sq_abs (S j q)]
            exact pow_le_pow_left₀ ht.le this.le 2
        _ ≤ ∑ q ∈ P, S j q ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h2 := h1.trans (hS j)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact h2
  have hc : (P.card : ℝ) ≤ B.card + ∑ j : Fin J, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) := by
    have := (Finset.card_le_card hcov).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
    exact_mod_cast this
  have : ∑ j : Fin J, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) ≤ J * (V / t ^ 2 * P.card) := by
    calc _ ≤ ∑ _j : Fin J, V / t ^ 2 * P.card := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  nlinarith


theorem class_splits : ClassSplit := by
  intro y q₁ d hq hd hM
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have main : ∀ p : ℕ, p.Prime → p ∣ (d + 1) / 4 → SplitsIn d p := by
    intro p hp hdiv
    have := Fact.mk hp
    refine ⟨0, 1, zero_ne_one, ?_, ?_⟩ <;> simp [(ZMod.natCast_eq_zero_iff _ _).2 hdiv]
  have odd : ∀ p : ℕ, p.Prime → p ∣ d + 1 → p ∣ (d + 1) / 4 := by
    intro p hp hdiv
    by_cases h2 : p = 2
    · subst h2; omega
    · rw [← h4] at hdiv
      rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
      · exfalso
        have : p ∣ 2 ^ 2 := by simpa using h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
      · exact h
  refine ⟨main _ hq (odd _ hq ((Dvd.intro _ rfl).trans hM)), fun p hp hpy => ?_⟩
  by_cases h2 : p = 2
  · subst h2; exact main 2 hp (by omega)
  · apply main _ hp (odd _ hp _)
    refine Dvd.dvd.trans ?_ hM
    apply Dvd.dvd.mul_left
    apply Finset.dvd_prod_of_mem (fun p => p)
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, Nat.le_floor hpy⟩, hp⟩
    have := hp.two_le; omega

theorem primorial_upper_bound : PrimorialBound := by
  intro y q₁ hy hq
  unfold oddM
  have h1 : (∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p) ≤ primorial ⌊y⌋₊ := by
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      exact (mem_filter.1 hp).2.one_lt.le
  have h2 : ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) ≤ Real.exp (2 * y) := by
    calc ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ ⌊y⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast h1.trans (primorial_le_four_pow _)
      _ = (4 : ℝ) ^ (⌊y⌋₊ : ℝ) := by push_cast; rw [Real.rpow_natCast]
      _ ≤ (4 : ℝ) ^ y := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hy)
      _ = Real.exp (Real.log 4 * y) := by rw [Real.rpow_def_of_pos (by norm_num)]
      _ ≤ Real.exp (2 * y) := by
          apply Real.exp_le_exp.2
          have : Real.log 4 ≤ 2 := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have := Real.log_two_lt_d9
            linarith
          nlinarith
  calc ((q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ)
      = (q₁ : ℝ) * ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) := by push_cast; ring
    _ ≤ Real.exp y * Real.exp (2 * y) := mul_le_mul hq h2 (by positivity) (by positivity)
    _ = Real.exp (3 * y) := by rw [← Real.exp_add]; ring_nf





theorem class_admissible : ClassAdmissible := by
  intro y z q₁ hy hq h8 hz
  set M := oddM y q₁ with hMdef
  have hMpf : ∀ p : ℕ, p.Prime → p ∣ M → p = q₁ ∨ (3 ≤ p ∧ (p : ℝ) ≤ y) := by
    intro p hp hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
    · obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
      simp only [mem_filter, mem_Icc] at hr
      have : p = r := (Nat.prime_dvd_prime_iff_eq hp hr.2).1 hpr
      subst this
      exact Or.inr ⟨hr.1.1, (Nat.le_floor_iff (by linarith)).1 hr.1.2⟩
  have hMpos : 0 < M := by
    apply Nat.mul_pos hq.pos
    exact Finset.prod_pos fun p hp => (mem_filter.1 hp).2.pos
  have hcop : Nat.Coprime 16 M := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    rcases hMpf 2 Nat.prime_two h with h | h
    · omega
    · omega
  obtain ⟨a₀, h16, hM⟩ := Nat.chineseRemainder hcop 7 (M - 1)
  have h16' : a₀ % 16 = 7 := h16
  have hM' : M ∣ a₀ + 1 := by
    have : a₀ + 1 ≡ (M - 1) + 1 [MOD M] := Nat.ModEq.add_right 1 hM
    rw [Nat.sub_add_cancel hMpos] at this
    exact (Nat.modEq_zero_iff_dvd).1 (this.trans (by simp [Nat.ModEq]))
  have hcM : a₀.Coprime M := by
    have : Nat.Coprime a₀ (a₀ + 1) := by simp
    exact Nat.Coprime.coprime_dvd_right hM' this
  have hc16 : a₀.Coprime 16 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  refine ⟨a₀, h16', hM', Nat.Coprime.mul_right hc16 hcM, by omega, Dvd.dvd.mul_right (by norm_num) _, ?_, ?_⟩
  · intro p hp hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
    · have : p ∣ 2 ^ 4 := by simpa using h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      subst this; left; exact_mod_cast hy
    · rcases hMpf p hp h with h | h
      · subst h; exact Or.inr hz
      · exact Or.inl h.2
  · intro d hd
    have hd' : d ≡ a₀ [MOD 16 * M] := hd
    have d16 : d ≡ a₀ [MOD 16] := Nat.ModEq.of_mul_right M hd'
    have dM : d ≡ a₀ [MOD M] := Nat.ModEq.of_mul_left 16 hd'
    refine ⟨d16.trans h16, ?_⟩
    exact (Nat.modEq_zero_iff_dvd).1 ((Nat.ModEq.add_right 1 dM).trans ((Nat.modEq_zero_iff_dvd).2 hM'))


theorem twist_evaluation_formula : TwEval := by
  intro t θ q _ n
  by_cases hu : IsUnit (n : ZMod (t * q))
  · unfold tw
    rw [MulChar.mul_apply]
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu']
    have h1 : (ZMod.cast ((n : ZMod (t * q))) : ZMod t) = (n : ZMod t) := by
      have : (ZMod.castHom (Dvd.intro q rfl : t ∣ t * q) (ZMod t)) (n : ZMod (t*q)) = (n : ZMod t) := map_natCast _ n
      simpa using this
    have h2 : (ZMod.cast ((n : ZMod (t * q))) : ZMod q) = (n : ZMod q) := by
      have : (ZMod.castHom (Dvd.intro_left t rfl : q ∣ t * q) (ZMod q)) (n : ZMod (t*q)) = (n : ZMod q) := map_natCast _ n
      simpa using this
    rw [h1, h2]
    congr 1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [qc, legendreSym]
  · rw [MulChar.map_nonunit _ hu]
    have hc : ¬ n.Coprime (t * q) := fun h => hu ((ZMod.isUnit_iff_coprime n _).2 h)
    by_cases h1 : n.Coprime t
    · have h2 : ¬ n.Coprime q := fun h => hc (Nat.Coprime.mul_right h1 h)
      have : jacobiSym (n : ℤ) q = 0 := by
        have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
        rw [jacobiSym.eq_zero_iff_not_coprime]
        simpa [Int.gcd_natCast_natCast] using h2
      simp [this]
    · have : θ (n : ZMod t) = 0 := MulChar.map_nonunit _ (fun h => h1 ((ZMod.isUnit_iff_coprime n _).1 h))
      simp [this]





end Formalism.HermitianLattices.ZeroFreeRegionGL2
