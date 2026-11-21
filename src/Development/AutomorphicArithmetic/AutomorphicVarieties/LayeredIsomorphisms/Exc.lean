import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.near1 :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K] (s : K) (Z a b : ℕ),
      1 ≤ a → a ≤ Z → 1 ≤ b → b ≤ Z → ‖s - (a : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) →
        ‖s - (b : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) → a = b := by
  intro l _ K _ _ _ s Z a b ha1 haZ hb1 hbZ hsa hsb
  by_contra hab
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  set k := Nat.log l Z with hk
  set d : ℤ := (a : ℤ) - b with hd
  have hd0 : d ≠ 0 := by omega
  have hK : ‖(d : ℚ_[l])‖ < (l : ℝ) ^ (-(k : ℤ)) := by
    have h1 : algebraMap ℚ_[l] K (d : ℚ_[l]) = (s - b) + -(s - a) := by
      rw [map_intCast, hd]
      push_cast
      ring
    rw [← norm_algebraMap' K, h1]
    calc ‖(s - b) + -(s - a)‖ ≤ max ‖s - b‖ ‖-(s - a)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < _ := by
        rw [norm_neg]
        exact max_lt hsb hsa
  have hdq : (d : ℚ_[l]) ≠ 0 := by exact_mod_cast hd0
  rw [Padic.norm_eq_zpow_neg_valuation hdq] at hK
  have hlt := (zpow_lt_zpow_iff_right₀ hl1).mp hK
  have hle : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hdq]
    apply zpow_le_zpow_right₀ hl1.le
    push_cast
    omega
  have hdvd := (Padic.norm_int_le_pow_iff_dvd d (k + 1)).mp hle
  have hZ := Nat.lt_pow_succ_log_self hlp.one_lt Z
  have habs : d.natAbs ≤ Z := by
    rw [hd]
    omega
  have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact lt_of_le_of_lt habs hZ)
  exact hd0 h0
end

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.exc :
    ∀ (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], ABound l R L₀ →
      ∃ c : ℕ, (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) ∧ ∀ Z : ℕ, ∃ Exc : Finset ℕ, FirstBound l R c L₀ Z Exc := by
  intro l R _ L₀ _ h
  classical
  obtain ⟨⟨K, _, _, hU, c, R', s, hR', hζ, hb⟩, -⟩ := h
  refine ⟨c, hζ, fun Z => ?_⟩
  obtain ⟨near, hnear⟩ : ∃ near : Fin R' → Finset ℕ, near = fun i =>
      (Finset.Icc 1 Z : Finset ℕ).filter
        (fun e : ℕ => ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ))) :=
    ⟨_, rfl⟩
  refine ⟨Finset.univ.biUnion near, ?_⟩
  unfold FirstBound
  refine ⟨?_, ?_⟩
  · have hone : ∀ i : Fin R', (near i).card ≤ 1 := by
      intro i
      rw [Finset.card_le_one]
      intro a ha b hb'
      rw [hnear] at ha hb'
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb'
      exact near1 l K (s i) Z a b ha.1.1 ha.1.2 hb'.1.1 hb'.1.2 ha.2 hb'.2
    calc (Finset.univ.biUnion near).card ≤ ∑ i : Fin R', (near i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin R', 1 := Finset.sum_le_sum (fun i _ => hone i)
      _ = R' := by simp
      _ ≤ R := hR'
  · intro e he1 heZ hne m L₁ _ _ _ hL
    have hfar : ∀ i : Fin R', (l : ℝ) ^ (-(Nat.log l Z : ℤ)) ≤ ‖s i - (e : K)‖ := by
      intro i
      by_contra hlt
      push_neg at hlt
      apply hne
      rw [hnear]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨i, ⟨he1, heZ⟩, hlt⟩
    have h1 := hb e he1 m L₁ hL (Nat.log l Z) hfar
    exact h1.trans (by gcongr)
end
