import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCover
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LogNormEstimates
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup

section
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem siegelSet_entry_bound_of_lattice_min (N : ℕ) (C : ℝ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ) (hS : IsSiegel C k a n) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmin : ∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖)
    (i j : Fin N) : |(k * diagonal a * n) i j| * t ^ N ≤ N * C ^ N := by
  have hN : 0 < N := Fin.pos i
  set i0 : Fin N := ⟨0, hN⟩ with hi0

  have hk : ∀ p q, |k p q| ≤ 1 := by
    intro p q
    have h := congrFun (congrFun hS.orth q) q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have : k p q * k p q ≤ ∑ x, k x q * k x q :=
      Finset.single_le_sum (f := fun x => k x q * k x q) (fun x _ => mul_self_nonneg _) (Finset.mem_univ p)
    rw [h] at this
    have h2 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact this
    nlinarith [abs_nonneg (k p q)]
  have hC1 : 1 ≤ C := by
    have := hS.bdd i i
    rw [hS.diag i, abs_one] at this
    exact this

  have hg : ∀ p q, (k * diagonal a * n) p q = ∑ l, k p l * a l * n l q := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]

  have hcol : ∀ p, (k * diagonal a * n) p i0 = k p i0 * a i0 := by
    intro p
    rw [hg, Finset.sum_eq_single i0]
    · rw [hS.diag i0, mul_one]
    · intro l _ hl
      have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      rw [hS.lower l i0 this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have ha0 : t ≤ a i0 := by
    have h := hmin (Pi.single i0 1) (by
      intro h; have := congrFun h i0; simp at this)
    refine h.trans ?_
    refine (pi_norm_le_iff_of_nonneg (le_of_lt (hS.pos i0))).2 ?_
    intro p
    have : ((k * diagonal a * n) *ᵥ fun i => (((Pi.single i0 (1:ℤ) : Fin N → ℤ) i : ℤ) : ℝ)) p
        = (k * diagonal a * n) p i0 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hcol, Real.norm_eq_abs, abs_mul, abs_of_pos (hS.pos i0)]
    exact mul_le_of_le_one_left (le_of_lt (hS.pos i0)) (hk p i0)
  have hlow : ∀ l, t ≤ C * a l := by
    intro l
    by_cases hl : l = i0
    · subst hl
      nlinarith [hS.pos i0]
    · have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      exact ha0.trans (hS.le i0 l this)
  have hup : ∀ l, a l * t ^ (N - 1) ≤ C ^ (N - 1) := by
    intro l
    have hprod : ∏ x ∈ Finset.univ.erase l, t ≤ ∏ x ∈ Finset.univ.erase l, (C * a x) :=
      Finset.prod_le_prod (fun _ _ => le_of_lt ht0) (fun x _ => hlow x)
    rw [Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin] at hprod
    have h1 : a l * ∏ x ∈ Finset.univ.erase l, a x = 1 := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ l)]; exact hS.prod_eq
    have hal := le_of_lt (hS.pos l)
    calc a l * t ^ (N - 1) ≤ a l * (C ^ (N - 1) * ∏ x ∈ Finset.univ.erase l, a x) :=
          mul_le_mul_of_nonneg_left hprod hal
      _ = C ^ (N - 1) * (a l * ∏ x ∈ Finset.univ.erase l, a x) := by ring
      _ = C ^ (N - 1) := by rw [h1, mul_one]
  have hent : |(k * diagonal a * n) i j| ≤ ∑ l, a l * C := by
    rw [hg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (hS.pos l)]
    have h1 := hk i l
    have h2 := hS.bdd l j
    have hal := le_of_lt (hS.pos l)
    calc |k i l| * a l * |n l j| ≤ 1 * a l * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hal) h2 (abs_nonneg _) (by positivity)
      _ = a l * C := by ring
  have htN : t ^ N = t ^ (N - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have htpow : 0 ≤ t ^ N := by positivity
  calc |(k * diagonal a * n) i j| * t ^ N ≤ (∑ l, a l * C) * t ^ N :=
        mul_le_mul_of_nonneg_right hent htpow
    _ = ∑ l, (a l * t ^ (N - 1)) * C * t := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; rw [htN]; ring
    _ ≤ ∑ l : Fin N, C ^ (N - 1) * C * 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hup l) (by linarith)) ht1 (le_of_lt ht0)
        positivity
    _ = N * C ^ N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_succ,
          Nat.sub_add_cancel hN]

theorem siegel_entry_bound : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    (∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖) →
    ∀ i j, |(k * diagonal a * n) i j| * t ^ N ≤ C' :=
  fun N C => ⟨N * C ^ N, fun k a n hS t ht0 ht1 hmin i j =>
    siegelSet_entry_bound_of_lattice_min N C k a n hS t ht0 ht1 hmin i j⟩

end GlobalTheory
end

section
section
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.ReducedBasisBound

lemma abs_sum_le_card {N : ℕ} (f : Fin N → ℝ) (B : ℝ) (h : ∀ p, |f p| ≤ B) :
    |∑ p, f p| ≤ N * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p, |f p| ≤ ∑ _p : Fin N, B := Finset.sum_le_sum (fun p _ => h p)
    _ = N * B := by simp

lemma entry_eq {N : ℕ} (a : Fin N → ℝ) (n Z P : Matrix (Fin N) (Fin N) ℝ)
    (h : diagonal a * n * P = Z * diagonal a * n) (p j : Fin N) :
    a p * (n * P) p j = ∑ q, Z p q * a q * n q j := by
  have := congrFun (congrFun h p) j
  rw [Matrix.mul_assoc, diagonal_mul] at this
  rw [this, Matrix.mul_apply]
  simp [mul_diagonal]

lemma int_eq_zero {x : ℤ} (h : |(x : ℝ)| < 1) : x = 0 := by
  have : |x| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

lemma integral_entry_eq_zero (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T)
    (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hmn : m * n = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hε : 0 < ε) (hK : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1) :
    ∀ i j, a i ≤ ε * a j → M' j i = 0 := by
  intro i j hij
  apply int_eq_zero
  have hC0 : 0 ≤ C₁ := by linarith
  have hM' : M'.map (Int.cast : ℤ → ℝ) = m * (n * M'.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, j ≤ p → |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ N * (T * C₁ ^ 3 * ε) := by
    intro p hp
    have he := entry_eq a n Zᵀ _ h2 p i
    have hb : |∑ q, Zᵀ p q * a q * n q i| ≤ N * (T * C₁ ^ 3 * ε * a p) := by
      apply abs_sum_le_card
      intro q
      rcases le_or_gt q i with hq | hq
      · have haq : a q ≤ C₁ ^ 2 * ε * a p := by
          calc a q ≤ C₁ * a i := hle q i hq
            _ ≤ C₁ * (ε * a j) := by gcongr
            _ ≤ C₁ * (ε * (C₁ * a p)) := by gcongr; exact hle j p hp
            _ = C₁ ^ 2 * ε * a p := by ring
        rw [abs_mul, abs_mul, transpose_apply, abs_of_pos (ha q)]
        calc |Z q p| * a q * |n q i| ≤ T * (C₁ ^ 2 * ε * a p) * C₁ := by
              have := ha p
              exact mul_le_mul (mul_le_mul (hZ q p) haq (ha q).le hT) (hn q i) (abs_nonneg _) (by positivity)
          _ = T * C₁ ^ 3 * ε * a p := by ring
      · rw [hn_low q i hq]
        have := ha p
        simp only [mul_zero, abs_zero]
        positivity
    have : a p * |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ a p * (N * (T * C₁ ^ 3 * ε)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ ^ 3 * ε * a p) := hb
        _ = a p * (N * (T * C₁ ^ 3 * ε)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M' j i : ℤ) : ℝ) = (M'.map (Int.cast : ℤ → ℝ)) j i := by simp
  rw [hentry, hM', mul_apply]
  refine lt_of_le_of_lt (abs_sum_le_card _ _ (fun p => ?_)) hK
  rcases le_or_gt j p with hp | hp
  · rw [abs_mul]
    exact mul_le_mul (hm j p) (hE p hp) (abs_nonneg _) hCm
  · rw [hm_low j p hp, zero_mul, abs_zero]
    have : (0 : ℝ) ≤ N * (T * C₁ ^ 3 * ε) := by positivity
    positivity

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

lemma conj_entry_eq_zero (hC : 1 ≤ C₁) (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hnm : n * m = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hA : ∀ i j, a i ≤ ε * a j → M' j i = 0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * C₁ ^ 2 = ε) :
    ∀ i j, a i ≤ δ * a j → Z i j = 0 := by
  intro i j hij
  have hC0 : 0 ≤ C₁ := by linarith
  have h := congrArg (· * m) h2
  simp only [Matrix.mul_assoc] at h
  rw [hnm, Matrix.mul_one] at h
  have e := congrFun (congrFun h j) i
  rw [diagonal_mul, mul_diagonal, transpose_apply] at e
  have hz : (n * (M'.map (Int.cast : ℤ → ℝ) * m)) j i = 0 := by
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro p _
    rcases lt_or_ge p j with hp | hp
    · rw [hn_low j p hp, zero_mul]
    · have hin : (M'.map (Int.cast : ℤ → ℝ) * m) p i = 0 := by
        rw [mul_apply]
        apply Finset.sum_eq_zero
        intro q _
        rcases lt_or_ge i q with hq | hq
        · rw [hm_low q i hq, mul_zero]
        · have hq' : a q ≤ ε * a p := by
            calc a q ≤ C₁ * a i := hle q i hq
              _ ≤ C₁ * (δ * a j) := by gcongr
              _ ≤ C₁ * (δ * (C₁ * a p)) := by gcongr; exact hle j p hp
              _ = ε * a p := by rw [← hδ]; ring
          rw [Matrix.map_apply, hA q p hq']
          simp
      rw [hin, mul_zero]
  rw [hz, mul_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_right (ne_of_gt (ha i))

lemma entry_bound_of_vanishing (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T) (ha : ∀ i, 0 < a i)
    (hmn : m * n = 1) (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M : Matrix (Fin N) (Fin N) ℤ)
    (h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n)
    (δ : ℝ) (hδ : 0 < δ) (hB : ∀ i j, a i ≤ δ * a j → Z i j = 0) :
    ∀ i j, |(M i j : ℝ)| ≤ N * (Cm * (N * (T * C₁ / δ))) := by
  intro i j
  have hC0 : 0 ≤ C₁ := by linarith
  have hM : M.map (Int.cast : ℤ → ℝ) = m * (n * M.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ N * (T * C₁ / δ) := by
    intro p
    have he := entry_eq a n Z _ h1 p j
    have hb : |∑ q, Z p q * a q * n q j| ≤ N * (T * C₁ / δ * a p) := by
      apply abs_sum_le_card
      intro q
      have := ha p
      by_cases hz : Z p q = 0
      · rw [hz]
        simp only [zero_mul, abs_zero]
        positivity
      · have hlt : δ * a q < a p := by
          by_contra hc
          exact hz (hB p q (not_lt.mp hc))
        have haq : a q ≤ a p / δ := by rw [le_div_iff₀ hδ]; linarith
        rw [abs_mul, abs_mul, abs_of_pos (ha q)]
        calc _ ≤ T * (a p / δ) * C₁ :=
              mul_le_mul (mul_le_mul (hZ p q) haq (ha q).le hT) (hn q j) (abs_nonneg _) (by positivity)
          _ = T * C₁ / δ * a p := by ring
    have : a p * |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ a p * (N * (T * C₁ / δ)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ / δ * a p) := hb
        _ = a p * (N * (T * C₁ / δ)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M i j : ℤ) : ℝ) = (M.map (Int.cast : ℤ → ℝ)) i j := by simp
  rw [hentry, hM, mul_apply]
  exact abs_sum_le_card _ _ (fun p => by
    rw [abs_mul]; exact mul_le_mul (hm i p) (hE p) (abs_nonneg _) hCm)

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

lemma abs_entry_le_one {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (l i : Fin N) :
    |k l i| ≤ 1 := by
  have e := congrFun (congrFun h i) i
  rw [mul_apply, one_apply_eq] at e
  simp only [transpose_apply] at e
  have : k l i ^ 2 ≤ 1 := by
    rw [← e, sq]
    exact Finset.single_le_sum (f := fun l => k l i * k l i) (fun l _ => mul_self_nonneg _)
      (Finset.mem_univ l)
  exact sq_le_one_iff_abs_le_one _ |>.mp this

lemma conj_bound {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℝ) (hk : ∀ l i, |k l i| ≤ 1) (R : ℝ)
    (hR : 0 ≤ R) (hX : ∀ i j, |X i j| ≤ R) (i j : Fin N) :
    |(kᵀ * X * k) i j| ≤ N * (N * R) := by
  rw [mul_apply]
  apply abs_sum_le_card
  intro q
  rw [abs_mul]
  have hin : |(kᵀ * X) i q| ≤ N * R := by
    rw [mul_apply]
    apply abs_sum_le_card
    intro l
    rw [abs_mul, transpose_apply]
    calc |k l i| * |X l q| ≤ 1 * R := mul_le_mul (hk l i) (hX l q) (abs_nonneg _) zero_le_one
      _ = R := one_mul R
  calc |(kᵀ * X) i q| * |k q j| ≤ (N * R) * 1 := mul_le_mul hin (hk q j) (abs_nonneg _) (by positivity)
    _ = N * R := mul_one _

theorem integral_conj_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ)
    (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n →
    ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) →
    (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) →
    (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) →
    ∀ i j, |(M i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨C₁, hC₁d⟩ : ∃ C₁ : ℝ, C₁ = max C 1 := ⟨_, rfl⟩
  obtain ⟨Cm0, hCm0⟩ := GlobalTheory.unipotent_upper_inv_bounded N C₁
  obtain ⟨Cm, hCmd⟩ : ∃ Cm : ℝ, Cm = max Cm0 0 := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = N * (N * max R 0) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = N * (Cm * (N * (T * C₁ ^ 3))) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = 1 / (K + 1) := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε / C₁ ^ 2 := ⟨_, rfl⟩
  refine ⟨N * (Cm * (N * (T * C₁ / δ))), ?_⟩
  intro k a n hs X M M' hX hM hM'
  have hC : 1 ≤ C₁ := hC₁d ▸ le_max_right _ _
  have hC₁pos : 0 < C₁ := by linarith
  have hCm : 0 ≤ Cm := hCmd ▸ le_max_right _ _
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hT : 0 ≤ T := by rw [hTd]; positivity
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hε : 0 < ε := by rw [hεd]; positivity
  have hKε : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1 := by
    have e : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) = K * (1 / (K + 1)) := by
      rw [← hεd, hKd]; ring
    rw [e, mul_one_div, div_lt_one (by linarith)]
    linarith
  have hδ : 0 < δ := by rw [hδd]; positivity
  have hδε : δ * C₁ ^ 2 = ε := by rw [hδd]; field_simp
  have hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hs.le i j h).trans
        (mul_le_mul_of_nonneg_right (hC₁d ▸ le_max_left _ _) (hs.pos j).le)
    · subst h
      nlinarith [hs.pos i]
  have hn : ∀ i j, |n i j| ≤ C₁ := fun i j => (hs.bdd i j).trans (hC₁d ▸ le_max_left _ _)
  obtain ⟨m, hmn, hnm, hm_low, hm⟩ := hCm0 n hs.diag hs.lower hn
  have hm' : ∀ i j, |m i j| ≤ Cm := fun i j => (hm i j).trans (hCmd ▸ le_max_left _ _)
  have hk := abs_entry_le_one k hs.orth
  obtain ⟨Z, hZd⟩ : ∃ Z : Matrix (Fin N) (Fin N) ℝ, Z = kᵀ * X * k := ⟨_, rfl⟩
  have hZ : ∀ i j, |Z i j| ≤ T := by
    intro i j
    rw [hZd, hTd]
    exact conj_bound k X hk _ hR (fun i j => (hX i j).trans (le_max_left _ _)) i j
  have h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
  have h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM'
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hA := integral_entry_eq_zero hC hCm hT hs.pos hle hmn hs.lower hm_low hn hm' hZ M' h2 ε hε hKε
  have hB := conj_entry_eq_zero hC hs.pos hle hnm hs.lower hm_low M' h2 ε hA δ hδ.le hδε
  exact entry_bound_of_vanishing hC hCm hT hs.pos hmn hn hm' hZ M h1 δ hδ hB

end GlobalTheory.ReducedBasisBound
end

open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedBasis_integral_conj_entries_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) → (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) → (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) → ∀ i j, |(M i j : ℝ)| ≤ C' := by
  atlas_forward_decl GlobalTheory.ReducedBasisBound.integral_conj_bounded
end

section
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  first | exact @GlobalTheory.unipotent_upper_inv_bounded | exact GlobalTheory.unipotent_upper_inv_bounded | (intros; apply GlobalTheory.unipotent_upper_inv_bounded <;> assumption)
end

section
section
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.RedBound

lemma entry_bound {N : ℕ} (P Z Q : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c : ℝ)
    (h : ∀ p q, |P i p * Z p q * Q q j| ≤ c) : |(P * Z * Q) i j| ≤ N * N * c := by
  have e : (P * Z * Q) i j = ∑ q, ∑ p, P i p * Z p q * Q q j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [e]
  calc |∑ q, ∑ p, P i p * Z p q * Q q j| ≤ ∑ q, |∑ p, P i p * Z p q * Q q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Fin N, ∑ _p : Fin N, c := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => h p q)
    _ = N * N * c := by simp [Finset.sum_const, Finset.card_fin]; ring

lemma orth_entry_le {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (p q : Fin N) :
    |k p q| ≤ 1 := by
  have h1 : ∑ r, k r q * k r q = 1 := by
    have := congrFun (congrFun h q) q
    simpa [Matrix.mul_apply] using this
  have h2 : k p q * k p q ≤ ∑ r, k r q * k r q :=
    Finset.single_le_sum (f := fun r => k r q * k r q) (fun r _ => mul_self_nonneg _)
      (Finset.mem_univ p)
  rw [h1] at h2
  have h3 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact h2
  nlinarith [abs_nonneg (k p q)]

lemma le_of_le_idx {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {i p : Fin N} (h : i ≤ p) : a i ≤ Cm * a p := by
  rcases h.lt_or_eq with h | h
  · exact (hS.le i p h).trans (mul_le_mul_of_nonneg_right hC (hS.pos p).le)
  · subst h; exact le_mul_of_one_le_left (hS.pos i).le h1

lemma prod_le {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {p q r s : Fin N} (hr : p ≤ r) (hs : q ≤ s) : a p * a q ≤ Cm ^ 2 * (a r * a s) := by
  have har := le_of_le_idx hS h1 hC hr
  have has := le_of_le_idx hS h1 hC hs
  have h0 : 0 ≤ Cm * a r := mul_nonneg (by linarith) (hS.pos r).le
  calc a p * a q ≤ (Cm * a r) * (Cm * a s) := mul_le_mul har has (hS.pos q).le h0
    _ = Cm ^ 2 * (a r * a s) := by ring

end GlobalTheory.RedBound

namespace GlobalTheory.RedBound

theorem reduced_bound : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) →
    B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) →
    (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X →
    ∀ i j, |(B i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨M, hM⟩ := GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded N C
  obtain ⟨Cm, hCm1, hCC⟩ : ∃ Cm : ℝ, 1 ≤ Cm ∧ C ≤ Cm := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨M₀, hM₀, hMM⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ M ≤ M₀ := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R₀, hR₀, hRR⟩ : ∃ R₀ : ℝ, 0 ≤ R₀ ∧ R ≤ R₀ := ⟨max R 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = N * N * (1 * R₀ * 1) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = N * N * K₁ + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := lt_of_lt_of_le one_pos hCm1
  have hR'0 : 0 ≤ R' := by rw [hR']; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨N * N * (Cm * (Cm ^ 2 * T * R') * Cm), ?_⟩
  intro k a n hS X B B' μ hμ hμR hX hB hB' i j
  obtain ⟨m, hmn, _hnm, hmlow, hmb⟩ := hM n hS.diag hS.lower hS.bdd
  have hmb' : ∀ p q, |m p q| ≤ M₀ := fun p q => (hmb p q).trans hMM
  have hnb : ∀ p q, |n p q| ≤ Cm := fun p q => (hS.bdd p q).trans hCC
  have hμ₀ : |μ| ≤ R₀ := hμR.trans hRR
  have hk : ∀ p q, |k p q| ≤ 1 := orth_entry_le k hS.orth
  obtain ⟨X', hX'def⟩ : ∃ X', X' = kᵀ * X * k := ⟨_, rfl⟩
  have hX' : ∀ p q, |X' p q| ≤ R' := by
    intro p q
    rw [hX'def, hR']
    apply entry_bound
    intro r s
    rw [abs_mul, abs_mul, Matrix.transpose_apply]
    exact mul_le_mul (mul_le_mul (hk r p) ((hX r s).trans hRR) (abs_nonneg _) zero_le_one)
      (hk s q) (abs_nonneg _) (by positivity)
  obtain ⟨Br', hBr'⟩ : ∃ Br', Br' = B'.map (Int.cast : ℤ → ℝ) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = n * Br' * nᵀ := ⟨_, rfl⟩
  have hWeq : diagonal a * W * diagonal a = μ • X' := by
    have h1 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k = μ • X' := by
      rw [hBr', hB', hX'def, Matrix.mul_smul, Matrix.smul_mul]
    rw [← h1, hWdef]
    have h2 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k =
        (kᵀ * k) * (diagonal a * (n * Br' * nᵀ) * diagonal a) * (kᵀ * k) := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [h2, hS.orth, Matrix.one_mul, Matrix.mul_one]
  have hWent : ∀ p q, a p * W p q * a q = μ * X' p q := by
    intro p q
    have := congrFun (congrFun hWeq p) q
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hBm : Br' = m * W * mᵀ := by
    rw [hWdef]
    calc Br' = (m * n) * Br' * (m * n)ᵀ := by rw [hmn]; simp
      _ = m * (n * Br' * nᵀ) * mᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hZ : B.map (Int.cast : ℤ → ℝ) = nᵀ * (diagonal a * X' * diagonal a) * n := by
    rw [hB, hX'def]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hA : ∀ p q, T ≤ a p * a q → B' p q = 0 := by
    intro p q hpq
    have hpos : 0 < a p * a q := mul_pos (hS.pos p) (hS.pos q)
    have hb : |Br' p q| ≤ N * N * (K₁ / (a p * a q)) := by
      rw [hBm]
      apply entry_bound
      intro r s
      rw [le_div_iff₀ hpos, Matrix.transpose_apply]
      by_cases hr : r < p
      · rw [hmlow p r hr]; simp; positivity
      by_cases hs : s < q
      · rw [hmlow q s hs]; simp; positivity
      push_neg at hr hs
      have hWb : |W r s| * (a r * a s) ≤ R₀ * R' := by
        calc |W r s| * (a r * a s) = |a r * W r s * a s| := by
              rw [abs_mul, abs_mul, abs_of_pos (hS.pos r), abs_of_pos (hS.pos s)]; ring
          _ = |μ| * |X' r s| := by rw [hWent r s, abs_mul]
          _ ≤ R₀ * R' := mul_le_mul hμ₀ (hX' r s) (abs_nonneg _) hR₀
      have hapq := prod_le hS hCm1 hCC hr hs
      rw [abs_mul, abs_mul, hK₁]
      calc |m p r| * |W r s| * |m q s| * (a p * a q)
          ≤ |m p r| * |W r s| * |m q s| * (Cm ^ 2 * (a r * a s)) :=
            mul_le_mul_of_nonneg_left hapq (by positivity)
        _ = |m p r| * (Cm ^ 2 * (|W r s| * (a r * a s))) * |m q s| := by ring
        _ ≤ M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ :=
            mul_le_mul (mul_le_mul (hmb' p r) (mul_le_mul_of_nonneg_left hWb (by positivity))
              (mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (mul_pos (hS.pos r) (hS.pos s)).le)) hM₀) (hmb' q s) (abs_nonneg _) (by positivity)
    have hlt : |Br' p q| < 1 := by
      have e : (N : ℝ) * N * (K₁ / (a p * a q)) = (N * N * K₁) / (a p * a q) := by ring
      rw [e] at hb
      exact hb.trans_lt ((div_lt_one hpos).mpr (by linarith))
    have h3 : |((B' p q : ℤ) : ℝ)| < 1 := by rw [hBr'] at hlt; simpa using hlt
    have h4 : |B' p q| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp h4
  have hBz : ∀ p q, Cm ^ 2 * T ≤ a p * a q → W p q = 0 := by
    intro p q h
    rw [hWdef]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_eq_zero
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r < p
    · rw [hS.lower p r hr]; ring
    by_cases hs : s < q
    · rw [hS.lower q s hs]; ring
    push_neg at hr hs
    have hapq := prod_le hS hCm1 hCC hr hs
    have hT' : T ≤ a r * a s := by
      have : Cm ^ 2 * T ≤ Cm ^ 2 * (a r * a s) := h.trans hapq
      exact le_of_mul_le_mul_left this (by positivity)
    have h0 := hA r s hT'
    simp [hBr', h0]
  have hZb : ∀ p q, |a p * X' p q * a q| ≤ Cm ^ 2 * T * R' := by
    intro p q
    by_cases h : Cm ^ 2 * T ≤ a p * a q
    · have e := hWent p q
      rw [hBz p q h] at e
      have h0 : μ * X' p q = 0 := by rw [← e]; ring
      have hx : X' p q = 0 := (mul_eq_zero.mp h0).resolve_left hμ
      rw [hx]; simp; positivity
    · push_neg at h
      calc |a p * X' p q * a q| = (a p * a q) * |X' p q| := by
            rw [abs_mul, abs_mul, abs_of_pos (hS.pos p), abs_of_pos (hS.pos q)]; ring
        _ ≤ (Cm ^ 2 * T) * R' := mul_le_mul h.le (hX' p q) (abs_nonneg _) (by positivity)
  have hBe : (B i j : ℝ) = (nᵀ * (diagonal a * X' * diagonal a) * n) i j := by
    rw [← hZ]; simp
  rw [hBe]
  apply entry_bound
  intro r s
  have hZe : (diagonal a * X' * diagonal a) r s = a r * X' r s * a s := by
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transpose_apply, hZe, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hnb r i) (hZb r s) (abs_nonneg _) hCm0.le) (hnb s j)
    (abs_nonneg _) (by positivity)

end GlobalTheory.RedBound
end

open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelReduced_integral_form_bounded_entries : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) → B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) → (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X → ∀ i j, |(B i j : ℝ)| ≤ C' := by
  atlas_forward_decl GlobalTheory.RedBound.reduced_bound
end

section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.MulCoord

variable (I : AutInst)

def vecHom (y : I.Ginf) : (Fin I.n → I.E) →+ (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun := vec I y
  map_zero' := by
    funext v
    have h0 : (fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0 := by funext i; simp
    change uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0
    rw [h0, mulVec_zero, mulVec_zero]
  map_add' u w := by
    funext v
    have h : (fun i => I.φ v ((u + w) i)) = (fun i => I.φ v (u i)) + fun i => I.φ v (w i) := by
      funext i; simp
    change uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v ((u + w) i)) =
      uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) + uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (w i))
    rw [h, mulVec_add, mulVec_add]

theorem vec_sum_zsmul {N : ℕ} (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (z : Fin N → ℤ) :
    vec I y (∑ k, z k • e k) = ∑ k, z k • vec I y (e k) := by
  calc vec I y (∑ k, z k • e k) = vecHom I y (∑ k, z k • e k) := rfl
    _ = ∑ k, vecHom I y (z k • e k) := map_sum _ _ _
    _ = ∑ k, z k • vecHom I y (e k) := by simp only [map_zsmul]
    _ = _ := rfl

theorem vec_smul (y : I.Ginf) (a : I.E) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y (a • u) v = I.φ v a • vec I y u v := by
  have h : (fun i => I.φ v ((a • u) i)) = I.φ v a • fun i => I.φ v (u i) := by
    funext i; simp
  simp only [vec, h, Matrix.mulVec_smul]

def mulL (c : InfinitePlace I.F → ℂ) :
    (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun x := fun v i => c v * x v i
  map_add' x w := by
    funext v i; simp [mul_add]
  map_smul' r x := by
    funext v i; simp [Complex.real_smul]; ring

variable {I}

def mulMat {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (c : InfinitePlace I.F → ℂ) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ mulL I c ∘ₗ ρ.symm.toLinearMap)

theorem mulMat_mulVec {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (c : InfinitePlace I.F → ℂ) (w : Fin N → ℝ) :
    mulMat ρ c *ᵥ w = ρ (mulL I c (ρ.symm w)) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem mulMat_adj {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (hρ : IsRealCoord I ρ) (c : InfinitePlace I.F → ℂ) (a b : Fin N → ℝ) :
    (mulMat ρ c *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (mulMat ρ (fun v => starRingEnd ℂ (c v)) *ᵥ b) := by
  rw [mulMat_mulVec, mulMat_mulVec]
  have hb : b = ρ (ρ.symm b) := (ρ.apply_symm_apply b).symm
  have ha : a = ρ (ρ.symm a) := (ρ.apply_symm_apply a).symm
  conv_lhs => rw [hb]
  conv_rhs => rw [ha]
  rw [hρ, hρ]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [mulL, LinearMap.coe_mk, AddHom.coe_mk, star_mul', Complex.star_def]
  ring_nf

theorem mulMat_transpose {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (hρ : IsRealCoord I ρ) (c : InfinitePlace I.F → ℂ) :
    (mulMat ρ c)ᵀ = mulMat ρ (fun v => starRingEnd ℂ (c v)) := by
  classical
  ext i j
  have := mulMat_adj ρ hρ c (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, dotProduct_single, single_dotProduct] using this

end MulCoord
end GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo.MulCoord

theorem gm_mul {N : ℕ} {I : AutInst} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (w : I.E) (M : Matrix (Fin N) (Fin N) ℤ)
    (hM : ∀ j, w • e j = ∑ i, M i j • e i) :
    gm I ρ y e * M.map (Int.cast : ℤ → ℝ) = mulMat ρ (fun v => I.φ v w) * gm I ρ y e := by
  ext i j
  have hcol : (fun k => gm I ρ y e k j) = ρ (vec I y (e j)) := by funext k; rfl
  have hR : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j = ρ (vec I y (w • e j)) i := by
    have h1 : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j =
        (mulMat ρ (fun v => I.φ v w) *ᵥ fun k => gm I ρ y e k j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, hcol, mulMat_mulVec, LinearEquiv.symm_apply_apply]
    have h2 : mulL I (fun v => I.φ v w) (vec I y (e j)) = vec I y (w • e j) := by
      funext v k
      rw [vec_smul]
      rfl
    rw [h2]
  rw [hR, hM j, vec_sum_zsmul, map_sum, Finset.sum_apply]
  simp only [map_zsmul]
  simp only [Matrix.mul_apply, Matrix.map_apply, Pi.smul_apply, zsmul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gm, Matrix.of_apply]
  ring

theorem mul_conj_coord : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)),
    IsRealCoord I ρ → ∀ α : I.E, IsIntegral ℤ α → ∃ X : Matrix (Fin N) (Fin N) ℝ,
      ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ M M' : Matrix (Fin N) (Fin N) ℤ,
        gm I ρ y e * M.map (Int.cast : ℤ → ℝ) = X * gm I ρ y e ∧
        gm I ρ y e * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * gm I ρ y e ∧ ∀ j, α • e j = ∑ i, M i j • e i := by
  classical
  intro I N ρ hρ α hα
  refine ⟨mulMat ρ (fun v => I.φ v α), ?_⟩
  intro y e he
  have hint : ∀ j, IntVec I (e j) := fun j => (he.2 _).2 ⟨Pi.single j 1, by
    simp [Pi.single_apply, ite_smul]⟩
  have hα' : IsIntegral ℤ (star α) := by
    exact hα.map (starRingEnd I.E).toIntAlgHom
  have hz : ∀ j, ∃ z : Fin N → ℤ, α • e j = ∑ i, z i • e i := fun j =>
    (he.2 (α • e j)).1 fun i => by simpa [smul_eq_mul] using hα.mul (hint j i)
  have hz' : ∀ j, ∃ z : Fin N → ℤ, star α • e j = ∑ i, z i • e i := fun j =>
    (he.2 (star α • e j)).1 fun i => by simpa [smul_eq_mul] using hα'.mul (hint j i)
  choose z hz using hz
  choose z' hz' using hz'
  have hM : ∀ j, α • e j = ∑ i, (Matrix.of fun i j => z j i) i j • e i := fun j => by
    simpa using hz j
  have hM' : ∀ j, star α • e j = ∑ i, (Matrix.of fun i j => z' j i) i j • e i := fun j => by
    simpa using hz' j
  refine ⟨Matrix.of fun i j => z j i, Matrix.of fun i j => z' j i, gm_mul ρ y e α _ hM, ?_, hM⟩
  rw [mulMat_transpose ρ hρ, gm_mul ρ y e (star α) _ hM']
  congr 2
  funext v
  exact I.cm.cmUnram.2.1 (I.φ v) α

end GlobalTheory.CuspGeo.MulCoord
end
end

section
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.TrReal

variable (I : AutInst)

def signMap : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun x := fun v => Formalism.REAL.Jm (I.ε v) *ᵥ x v
  map_add' x y := by funext v; simp [mulVec_add]
  map_smul' r x := by funext v; simp [mulVec_smul]

theorem signMap_signMap (x) : signMap I (signMap I x) = x := by
  funext v
  simp [signMap, mulVec_mulVec, Formalism.REAL.Jm_mul_self]

theorem hform_eq_hf (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = CompanionTheory.D.gk.RF.hf I.J x y := by
  simp [Formalism.UG.hform, CompanionTheory.D.gk.RF.hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem pair_vec (y : I.Ginf) (u u' : Fin I.n → I.E) :
    2 * ∑ v, ∑ i, (star (vec I y u v i) * signMap I (vec I y u') v i).re = (trForm I u u' : ℝ) := by
  rw [trForm, CompanionTheory.D.gk.RF.PE.trace_eq I (fun v a => CompanionTheory.D.gk.RF.phi_star I v a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Complex.re_sum, hform_eq_hf, ← CompanionTheory.D.gk.RF.hf_atV_atV, ← CompanionTheory.D.gk.RF.PE.hf_uMat (y v)⁻¹]
  rfl

section
variable {I} {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))

def signMat : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ signMap I ∘ₗ ρ.symm.toLinearMap)

theorem signMat_mulVec (x) : signMat ρ *ᵥ ρ x = ρ (signMap I x) := by
  simp [signMat, LinearMap.toMatrix'_mulVec]

theorem signMat_sq : signMat ρ * signMat ρ = 1 := by
  rw [signMat, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  congr 1
  ext w
  simp [signMap_signMap]

theorem mul_apply_dot (A X : Matrix (Fin N) (Fin N) ℝ) (i j) :
    (Aᵀ * X * A) i j = (fun k => A k i) ⬝ᵥ (X *ᵥ fun l => A l j) := by
  rw [dotProduct_mulVec, Matrix.mul_apply]
  simp [vecMul, dotProduct, Matrix.mul_apply]

theorem gm_pair (hρ : IsRealCoord I ρ) (c : ℕ) (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (i j) :
    ((gm I ρ y e)ᵀ * ((2 * c : ℝ) • signMat ρ) * gm I ρ y e) i j = c * (trForm I (e i) (e j) : ℝ) := by
  rw [mul_apply_dot]
  have h1 : (fun k => gm I ρ y e k i) = ρ (vec I y (e i)) := rfl
  have h2 : (fun k => gm I ρ y e k j) = ρ (vec I y (e j)) := rfl
  rw [h1, h2, smul_mulVec, dotProduct_smul, signMat_mulVec, hρ, ← pair_vec I y (e i) (e j), smul_eq_mul]
  ring

theorem adj_formula (G X : Matrix (Fin N) (Fin N) ℝ) (a : ℝ) (ha : a ≠ 0) (hX : X * X = a • 1) :
    G * adjugate (Gᵀ * X * G) * Gᵀ = ((Gᵀ * X * G).det / a) • X := by
  have hadj : adjugate X = (X.det / a) • X := by
    calc adjugate X = adjugate X * (a⁻¹ • (X * X)) := by rw [hX, smul_smul, inv_mul_cancel₀ ha, one_smul, Matrix.mul_one]
      _ = (a⁻¹ • (adjugate X * X)) * X := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [adjugate_mul, smul_smul, Matrix.smul_mul, Matrix.one_mul, div_eq_inv_mul]
  rw [adjugate_mul_distrib, adjugate_mul_distrib, hadj, det_mul, det_mul, det_transpose]
  have e1 : G * (adjugate G * (((X.det / a) • X) * adjugate Gᵀ)) * Gᵀ =
      (G * adjugate G) * ((X.det / a) • X) * (adjugate Gᵀ * Gᵀ) := by simp only [Matrix.mul_assoc]
  rw [e1, mul_adjugate, adjugate_mul, det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  congr 1
  ring
end

section Rat

theorem hform_dot (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = (fun i => starRingEnd I.E (x i)) ⬝ᵥ (I.J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem trForm_sum_right {ι : Type} [Fintype ι] (x : Fin I.n → I.E) (q : ι → ℚ) (y : ι → Fin I.n → I.E) :
    trForm I x (∑ j, q j • y j) = ∑ j, q j * trForm I x (y j) := by
  simp only [trForm, hform_dot, mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, map_sum, map_smul,
    smul_eq_mul]

theorem trForm_sum_left {ι : Type} [Fintype ι] (x : Fin I.n → I.E) (q : ι → ℚ) (y : ι → Fin I.n → I.E) :
    trForm I (∑ j, q j • y j) x = ∑ j, q j * trForm I (y j) x := by
  have e : (fun i => starRingEnd I.E ((∑ j, q j • y j) i)) = ∑ j, q j • fun i => starRingEnd I.E (y j i) := by
    funext i
    simp [Finset.sum_apply, map_sum, map_rat_smul]
  simp only [trForm, hform_dot, e, sum_dotProduct, smul_dotProduct, map_sum, map_smul, smul_eq_mul]

theorem trForm_smul_left (x u : Fin I.n → I.E) (q : ℚ) : trForm I (q • u) x = q * trForm I u x := by
  have := trForm_sum_left I x (fun _ : Fin 1 => q) (fun _ => u)
  simpa using this

theorem intVec_of_basis {N : ℕ} {e : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (i) : IntVec I (e i) :=
  (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩

theorem trForm_int (c : ℕ) (hc : ∀ a b, IsIntegral ℤ ((c : I.E) * I.J a b)) {u u' : Fin I.n → I.E}
    (hu : IntVec I u) (hu' : IntVec I u') : ∃ z : ℤ, (z : ℚ) = c * trForm I u u' := by
  have e1 : (c : ℚ) * trForm I u u' = Algebra.trace ℚ I.E ((c : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J u u') := by
    rw [trForm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, map_natCast]
  have hint : IsIntegral ℤ ((c : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J u u') := by
    rw [Formalism.UG.hform, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun b _ => ?_
    have : (c : I.E) * (starRingEnd I.E (u a) * I.J a b * u' b) = starRingEnd I.E (u a) * ((c : I.E) * I.J a b) * u' b := by ring
    rw [this]
    exact ((map_isIntegral_int (starRingEnd I.E) (hu a)).mul (hc a b)).mul (hu' b)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hint)
  exact ⟨z, by rw [e1, ← hz]; simp⟩

end Rat

section Det
variable {I} {N : ℕ}

theorem det_ne_zero {e : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (c : ℕ) (hc1 : 1 ≤ c)
    (B : Matrix (Fin N) (Fin N) ℤ) (hB : ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j)) : B.det ≠ 0 := by
  intro h0
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set x : Fin I.n → I.E := ∑ j, ((z j : ℚ)) • e j with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hz0
    have e0 : ∑ j, z j • e j = 0 := by rw [← hx, hxdef]; simp [Int.cast_smul_eq_zsmul]
    funext j
    exact Fintype.linearIndependent_iff.1 he.1 z e0 j
  have hc0 : (c : ℚ) ≠ 0 := by positivity
  have hxe : ∀ i, trForm I (e i) x = 0 := by
    intro i
    have h1 := congrFun hz i
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1
    have h2 : ((∑ j, B i j * z j : ℤ) : ℚ) = 0 := by rw [h1]; simp
    push_cast at h2
    simp only [hB] at h2
    rw [hxdef, trForm_sum_right]
    have : (c : ℚ) * ∑ j, (z j : ℚ) * trForm I (e i) (e j) = 0 := by
      rw [Finset.mul_sum, ← h2]; exact Finset.sum_congr rfl fun j _ => by ring
    exact (mul_eq_zero.1 this).resolve_left hc0
  have hJx : I.J *ᵥ x ≠ 0 := fun h => I.J_det (Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx0, h⟩)
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hJx
  set y0 : Fin I.n → I.E := Pi.single k (star ((I.J *ᵥ x) k))⁻¹ with hy0def
  have hh : Formalism.UG.hform (starRingEnd I.E) I.J y0 x = 1 := by
    rw [hform_dot]
    have e2 : (fun i => starRingEnd I.E (y0 i)) = Pi.single k ((I.J *ᵥ x) k)⁻¹ := by
      funext i
      by_cases h : i = k
      · subst h; simp [hy0def, star_inv₀, starRingEnd_apply, star_star]
      · simp [hy0def, Pi.single_apply, h]
    rw [e2]
    simp [dotProduct, Pi.single_apply]
    exact inv_mul_cancel₀ (by simpa using hk)
  have hy0 : trForm I y0 x = Module.finrank ℚ I.E := by
    rw [trForm, hh, ← map_one (algebraMap ℚ I.E), Algebra.trace_algebraMap]; simp
  obtain ⟨d, hd, hdi⟩ := CompanionTheory.D.gk.RF.PE.exists_den y0
  obtain ⟨w, hw⟩ := (he.2 (fun i => (d : I.E) * y0 i)).1 hdi
  have e3 : (fun i => (d : I.E) * y0 i) = (d : ℚ) • y0 := by
    funext i; rw [Pi.smul_apply, Rat.smul_def]; simp
  have h4 : trForm I ((d : ℚ) • y0) x = 0 := by
    rw [← e3, hw]
    have : (∑ i, w i • e i) = ∑ i, ((w i : ℚ)) • e i := by simp [Int.cast_smul_eq_zsmul]
    rw [this, trForm_sum_left]; simp [hxe]
  rw [trForm_smul_left, hy0] at h4
  have hf : (Module.finrank ℚ I.E : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  exact mul_ne_zero hd0 hf h4

theorem change_basis {e e' : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (he' : ∀ i, IntVec I (e' i)) (c : ℕ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (hB : ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j))
    (hB' : ∀ i j, (B' i j : ℚ) = c * trForm I (e' i) (e' j)) : ∃ Z : Matrix (Fin N) (Fin N) ℤ, B' = Z * B * Zᵀ := by
  choose Z hZ using fun i => (he.2 (e' i)).1 (he' i)
  refine ⟨Matrix.of fun i k => Z i k, Matrix.ext fun i j => Int.cast_injective (α := ℚ) ?_⟩
  rw [hB', hZ i, hZ j]
  have hq : ∀ i, ∑ k, Z i k • e k = ∑ k, ((Z i k : ℚ)) • e k := fun i => by simp [Int.cast_smul_eq_zsmul]
  rw [hq, hq, trForm_sum_left]
  simp only [trForm_sum_right]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  push_cast
  simp only [hB, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end Det

theorem det_eq {N : ℕ} {e e' : Fin N → Fin I.n → I.E} (he : IsZBasis I e) (he' : IsZBasis I e') (c : ℕ) (hc1 : 1 ≤ c)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (hB : ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j))
    (hB' : ∀ i j, (B' i j : ℚ) = c * trForm I (e' i) (e' j)) : B'.det = B.det := by
  obtain ⟨Z, hZ⟩ := change_basis he (intVec_of_basis I he') c B B' hB hB'
  obtain ⟨W, hW⟩ := change_basis he' (intVec_of_basis I he) c B' B hB' hB
  have h0 := det_ne_zero he c hc1 B hB
  have e1 : B'.det = Z.det * B.det * Z.det := by rw [hZ, det_mul, det_mul, det_transpose]
  have e2 : B.det = W.det * B'.det * W.det := by rw [hW, det_mul, det_mul, det_transpose]
  have e3 : Z.det * (Z.det * W.det * W.det) = 1 := by
    refine mul_left_cancel₀ h0 ?_
    calc B.det * (Z.det * (Z.det * W.det * W.det)) = W.det * (Z.det * B.det * Z.det) * W.det := by ring
      _ = B.det * 1 := by rw [← e1, ← e2, mul_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one e3 with h | h <;> rw [e1, h] <;> ring

theorem trace_form_real_coord : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)),
    IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧
      ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ,
        B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧
        gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧
        ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  intro I N ρ hρ
  classical
  obtain ⟨c, hc1, hc⟩ := CompanionTheory.D.gk.RF.PE.exists_den fun p : Fin I.n × Fin I.n => I.J p.1 p.2
  have hcJ : ∀ a b, IsIntegral ℤ ((c : I.E) * I.J a b) := fun a b => hc (a, b)
  set X : Matrix (Fin N) (Fin N) ℝ := (2 * c : ℝ) • signMat ρ with hXdef
  have ha : (4 * (c : ℝ) ^ 2) ≠ 0 := by
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    positivity
  have hX : X * X = (4 * (c : ℝ) ^ 2) • 1 := by
    rw [hXdef, Matrix.smul_mul, Matrix.mul_smul, signMat_sq, smul_smul]
    congr 1
    ring
  have hBex : ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e →
      ∃ B : Matrix (Fin N) (Fin N) ℤ, ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := fun e he => by
    choose z hz using fun i j => trForm_int I c hcJ (intVec_of_basis I he i) (intVec_of_basis I he j)
    exact ⟨Matrix.of z, fun i j => hz i j⟩
  let Δ : ℝ := if h : ∃ e : Fin N → Fin I.n → I.E, IsZBasis I e then
    ((hBex h.choose h.choose_spec).choose.det : ℝ) else 4 * (c : ℝ) ^ 2
  have hΔ : Δ ≠ 0 := by
    simp only [Δ]
    split_ifs with h
    · exact_mod_cast det_ne_zero h.choose_spec c hc1 _ (hBex h.choose h.choose_spec).choose_spec
    · exact ha
  refine ⟨X, Δ / (4 * (c : ℝ) ^ 2), c, div_ne_zero hΔ ha, hc1, fun y e he => ?_⟩
  obtain ⟨B, hB⟩ := hBex e he
  have hBr : B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e := by
    ext i j
    rw [hXdef, gm_pair ρ hρ c y e i j, Matrix.map_apply]
    have := congrArg (Rat.cast : ℚ → ℝ) (hB i j)
    push_cast at this
    exact this
  refine ⟨B, adjugate B, hBr, ?_, hB⟩
  have hex : ∃ e : Fin N → Fin I.n → I.E, IsZBasis I e := ⟨e, he⟩
  have hΔe : Δ = (B.det : ℝ) := by
    simp only [Δ, dif_pos hex]
    exact_mod_cast det_eq I he hex.choose_spec c hc1 B _ hB (hBex hex.choose hex.choose_spec).choose_spec
  have hadj : (adjugate B).map (Int.cast : ℤ → ℝ) = adjugate (B.map (Int.cast : ℤ → ℝ)) :=
    (Int.castRingHom ℝ).map_adjugate B
  rw [hadj, hBr, adj_formula _ X _ ha hX, ← hBr, hΔe]
  congr 2
  exact ((Int.castRingHom ℝ).map_det B).symm

end GlobalTheory.CuspGeo.TrReal

end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_real_coordinates_integral_gram : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)), IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧ ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ, B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧ gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧ ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  atlas_forward_decl GlobalTheory.CuspGeo.TrReal.trace_form_real_coord
end

section
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.RedBasisPf

variable (I : AutInst)

theorem vec_add (y : I.Ginf) (u w : Fin I.n → I.E) : vec I y (u + w) = vec I y u + vec I y w := by
  funext v
  simp only [vec, Pi.add_apply]
  rw [← Matrix.mulVec_add, ← Matrix.mulVec_add]
  congr 2
  funext i
  simp

def vecHom (y : I.Ginf) : (Fin I.n → I.E) →+ (InfinitePlace I.F → Fin I.n → ℂ) :=
  AddMonoidHom.mk' (vec I y) (vec_add I y)

theorem vec_sum_zsmul (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ j, z j • e j) = ∑ j, z j • vec I y (e j) := by
  exact MulCoord.vec_sum_zsmul I y e z

theorem gm_mulVec {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) (z : Fin N → ℤ) :
    gm I ρ y e *ᵥ (fun j => (z j : ℝ)) = ρ (vec I y (∑ j, z j • e j)) := by
  rw [vec_sum_zsmul, map_sum]
  funext i
  simp only [map_zsmul]
  simp only [gm, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gm_change {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin N) (Fin N) ℤ) :
    gm I ρ y (fun j => ∑ i, M i j • e i) = gm I ρ y e * M.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [gm, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [vec_sum_zsmul I y (fun k => M k j) e, map_sum]
  simp only [map_zsmul]
  simp only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sum_change {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) (e : Fin N → Fin I.n → I.E) (w : Fin N → ℤ) :
    ∑ j, w j • (∑ i, M i j • e i) = ∑ i, (M *ᵥ w) i • e i := by
  simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem isZBasis_change {N : ℕ} (e : Fin N → Fin I.n → I.E) (he : IsZBasis I e)
    (M : Matrix (Fin N) (Fin N) ℤ) (hM : IsUnit M.det) : IsZBasis I (fun j => ∑ i, M i j • e i) := by
  obtain ⟨hli, hspan⟩ := he
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hinv' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨?_, fun u => ?_⟩
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg i
    rw [sum_change] at hg
    have hMg : M *ᵥ g = 0 := funext (hli _ hg)
    have hg' : g = M⁻¹ *ᵥ (M *ᵥ g) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    rw [hg', hMg, Matrix.mulVec_zero]
    rfl
  · rw [hspan u]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨M⁻¹ *ᵥ z, ?_⟩
      rw [sum_change, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    · rintro ⟨w, rfl⟩
      exact ⟨M *ᵥ w, sum_change I M e w⟩

theorem norm_le_sqrt {N : ℕ} {ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)}
    (hρ : IsRealCoord I ρ) (x : InfinitePlace I.F → Fin I.n → ℂ) : ‖x‖ ≤ Real.sqrt N * ‖ρ x‖ := by
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hsq : ∀ v i, ‖x v i‖ ^ 2 ≤ N * ‖ρ x‖ ^ 2 := by
    intro v i
    have h1 : ‖x v i‖ ^ 2 ≤ ∑ w, ∑ k, (star (x w k) * x w k).re := by
      simp only [hre]
      calc ‖x v i‖ ^ 2 ≤ ∑ k, ‖x v k‖ ^ 2 :=
            Finset.single_le_sum (f := fun k => ‖x v k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ w, ∑ k, ‖x w k‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ∑ k, ‖x w k‖ ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ v)
    rw [← hρ x x] at h1
    refine h1.trans ?_
    unfold dotProduct
    calc ∑ k, ρ x k * ρ x k ≤ ∑ _k : Fin N, ‖ρ x‖ ^ 2 := Finset.sum_le_sum fun k _ => by
            have hk := norm_le_pi_norm (ρ x) k
            rw [Real.norm_eq_abs] at hk
            have h := mul_self_le_mul_self (abs_nonneg _) hk
            rw [abs_mul_abs_self] at h
            nlinarith [h]
      _ = N * ‖ρ x‖ ^ 2 := by simp
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h := Real.sqrt_le_sqrt (hsq v i)
  rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def entSum {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i, ∑ j, |X i j|

theorem abs_le_entSum {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) : |X i j| ≤ entSum X := by
  unfold entSum
  calc |X i j| ≤ ∑ j', |X i j'| :=
        Finset.single_le_sum (f := fun j' => |X i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |X i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |X i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end GlobalTheory.CuspGeo.RedBasisPf

end

noncomputable section

namespace GlobalTheory.CuspGeo.RedBasisPf

theorem smul_conj {N : ℕ} (l c : ℝ) (A X : Matrix (Fin N) (Fin N) ℝ) :
    (l • A)ᵀ * (c • X) * (l • A) = (l * c * l) • (Aᵀ * X * A) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ring_nf

theorem smul_conj' {N : ℕ} (l : ℝ) (A B : Matrix (Fin N) (Fin N) ℝ) :
    (l • A) * B * (l • A)ᵀ = (l * l) • (A * B * Aᵀ) := by
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end GlobalTheory.CuspGeo.RedBasisPf

open GlobalTheory.CuspGeo.RedBasisPf in

theorem GlobalTheory.CuspGeo.redBasis_holds : ∀ I : AutInst, RedBasis I := by
  intro I
  obtain ⟨N, e0, ρ, d, hd, he0, hρ, hdet⟩ := covolume_const I
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨0, 0, 0, fun y => ⟨e0, he0, ⟨fun k j => j.elim0, fun i => i.elim0⟩, fun t _ _ _ j => j.elim0⟩⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨lam, hlam0, hlamN⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ^ N * d = 1 := by
    refine ⟨(d⁻¹) ^ ((N : ℝ)⁻¹), Real.rpow_pos_of_pos (inv_pos.2 hd) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_pos.2 hd).le, inv_mul_cancel₀ hNr.ne', Real.rpow_one,
      inv_mul_cancel₀ hd.ne']
  obtain ⟨c', hc'0, hc'1, hc'2⟩ : ∃ c' : ℝ, 0 < c' ∧ c' ≤ 1 ∧ c' ≤ lam / Real.sqrt N :=
    ⟨min 1 (lam / Real.sqrt N), lt_min one_pos (div_pos hlam0 (Real.sqrt_pos.2 hNr)), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨C0, hC0⟩ := siegel_cover (Fin N)
  obtain ⟨C1, hC1⟩ := siegel_entry_bound N C0
  have hint : ∀ k, IsIntegral ℤ (integralBasis I.E k) := by
    intro k
    rw [integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  choose X hX using fun k => MulCoord.mul_conj_coord I N ρ hρ _ (hint k)
  choose C2 hC2 using fun k => GlobalTheory.T.reducedBasis_integral_conj_entries_bounded N C0 (entSum (X k))
  obtain ⟨Xt, μ, c, hμ, hc, hXt⟩ := GlobalTheory.T.traceForm_real_coordinates_integral_gram I N ρ hρ
  obtain ⟨s, hs⟩ : ∃ s : ℝ, lam * s * lam = 1 := ⟨lam⁻¹ * lam⁻¹, by field_simp⟩
  obtain ⟨μ', hμ'0, hμ'⟩ : ∃ μ' : ℝ, μ' ≠ 0 ∧ lam * lam * μ = μ' * s := by
    refine ⟨lam * lam * μ * lam * lam, by positivity, ?_⟩
    have hs' : s = lam⁻¹ * lam⁻¹ := by
      field_simp
      linarith
    rw [hs']
    field_simp
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.siegelReduced_integral_form_bounded_entries N C0 (max |μ'| (entSum (s • Xt)))
  refine ⟨N, max (∑ k, |C2 k|) C3, Real.sqrt N * (lam⁻¹ * C1 / c' ^ N), fun y => ?_⟩
  have hdy := hdet y
  obtain ⟨S, hSu, hSd⟩ : ∃ S : Matrix (Fin N) (Fin N) ℤ, IsUnit S.det ∧
      (gm I ρ y e0 * S.map (Int.cast : ℤ → ℝ)).det = d := by
    rcases le_or_gt 0 (gm I ρ y e0).det with hpos | hneg
    · refine ⟨1, by simp, ?_⟩
      rw [Matrix.det_mul]
      simp only [Matrix.map_one Int.cast Int.cast_zero Int.cast_one, Matrix.det_one, mul_one]
      rw [← hdy, abs_of_nonneg hpos]
    · let f : Fin N → ℤ := fun i => if i = ⟨0, hN⟩ then -1 else 1
      have hf : ∏ i, f i = -1 := by
        simp [f, Finset.prod_ite_eq']
      refine ⟨Matrix.diagonal f, by rw [Matrix.det_diagonal, hf]; exact isUnit_one.neg, ?_⟩
      rw [Matrix.det_mul, Matrix.diagonal_map Int.cast_zero, Matrix.det_diagonal]
      have hf' : ∏ i, ((f i : ℤ) : ℝ) = -1 := by
        rw [← Int.cast_prod, hf]
        simp
      rw [hf', ← hdy, abs_of_neg hneg]
      ring
  let e1 : Fin N → Fin I.n → I.E := fun j => ∑ i, S i j • e0 i
  have he1 : IsZBasis I e1 := isZBasis_change I e0 he0 S hSu
  have hg1 : gm I ρ y e1 = gm I ρ y e0 * S.map Int.cast := gm_change I ρ y e0 S
  have hdet1 : (lam • gm I ρ y e1).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hg1, hSd, hlamN]
  obtain ⟨γ, hγ, k, a, n, hsieg, hfac⟩ := hC0 _ hdet1
  let e : Fin N → Fin I.n → I.E := fun j => ∑ i, γ i j • e1 i
  have he : IsZBasis I e := isZBasis_change I e1 he1 γ (by rw [hγ]; exact isUnit_one)
  have hK : k * Matrix.diagonal a * n = lam • gm I ρ y e := by
    rw [← hfac, gm_change I ρ y e1 γ, Matrix.smul_mul]
  refine ⟨e, he, ⟨fun kk j => ?_, fun i j => ?_⟩, fun t ht0 ht1 hns j => ?_⟩
  · obtain ⟨M, M', h1, h2, h3⟩ := hX kk y e he
    refine ⟨fun i => M i j, h3 j, fun i => ?_⟩
    have hb := hC2 kk k a n hsieg (X kk) M M' (fun i j => abs_le_entSum (X kk) i j)
      (by rw [hK, Matrix.smul_mul, h1, Matrix.mul_smul])
      (by rw [hK, Matrix.smul_mul, h2, Matrix.mul_smul]) i j
    calc |((M i j : ℤ) : ℝ)| ≤ C2 kk := hb
      _ ≤ |C2 kk| := le_abs_self _
      _ ≤ ∑ k, |C2 k| := Finset.single_le_sum (f := fun k => |C2 k|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ kk)
      _ ≤ _ := le_max_left _ _
  · obtain ⟨B, B', hB1, hB2, hB3⟩ := hXt y e he
    have hb := hC3 k a n hsieg (s • Xt) B B' μ' hμ'0 (le_max_left _ _)
      (fun i j => (abs_le_entSum (s • Xt) i j).trans (le_max_right _ _))
      (by rw [hK, smul_conj, hs, one_smul, hB1])
      (by rw [hK, smul_conj', hB2, smul_smul, smul_smul, hμ']) i j
    have hcast : ((B i j : ℤ) : ℝ) = (c : ℝ) * ((trForm I (e i) (e j) : ℚ) : ℝ) := by
      exact_mod_cast hB3 i j
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have htr : |((trForm I (e i) (e j) : ℚ) : ℝ)| ≤ |((B i j : ℤ) : ℝ)| := by
      rw [hcast, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c)]
      nlinarith [abs_nonneg ((trForm I (e i) (e j) : ℚ) : ℝ)]
    exact htr.trans (hb.trans (le_max_right _ _))
  · have hz : ∀ z : Fin N → ℤ, z ≠ 0 → c' * t ≤ ‖(k * Matrix.diagonal a * n) *ᵥ fun i => (z i : ℝ)‖ := by
      intro z hz
      rw [hK, Matrix.smul_mulVec, gm_mulVec, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
      have hu : (∑ j, z j • e j) ≠ 0 := by
        intro h
        apply hz
        exact funext (Fintype.linearIndependent_iff.1 he.1 z h)
      have hiv : IntVec I (∑ j, z j • e j) := (he.2 _).2 ⟨z, rfl⟩
      have h1 : t ≤ ‖vec I y (∑ j, z j • e j)‖ := hns _ hiv hu
      have h2 := norm_le_sqrt I hρ (vec I y (∑ j, z j • e j))
      have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
      calc c' * t ≤ lam / Real.sqrt N * t := mul_le_mul_of_nonneg_right hc'2 ht0.le
        _ ≤ lam / Real.sqrt N * (Real.sqrt N * ‖ρ (vec I y (∑ j, z j • e j))‖) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = lam * ‖ρ (vec I y (∑ j, z j • e j))‖ := by field_simp
    have hbound := hC1 k a n hsieg (c' * t) (mul_pos hc'0 ht0) (by nlinarith) hz
    have hcol : ∀ i, |ρ (vec I y (e j)) i| * t ^ N ≤ lam⁻¹ * C1 / c' ^ N := by
      intro i
      have hij := hbound i j
      have hKij : (k * Matrix.diagonal a * n) i j = lam * ρ (vec I y (e j)) i := by
        rw [hK]
        simp [gm]
      rw [hKij, abs_mul, abs_of_pos hlam0, mul_pow] at hij
      rw [le_div_iff₀ (pow_pos hc'0 N)]
      calc |ρ (vec I y (e j)) i| * t ^ N * c' ^ N
          = lam⁻¹ * (lam * |ρ (vec I y (e j)) i| * (c' ^ N * t ^ N)) := by field_simp
        _ ≤ lam⁻¹ * C1 := by gcongr
    have hD : 0 ≤ lam⁻¹ * C1 / c' ^ N := (by positivity : (0 : ℝ) ≤ |ρ (vec I y (e j)) j| * t ^ N).trans (hcol j)
    have hρn : ‖ρ (vec I y (e j))‖ ≤ lam⁻¹ * C1 / c' ^ N / t ^ N := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos ht0 N)]
      exact hcol i
    calc ‖vec I y (e j)‖ * t ^ N ≤ Real.sqrt N * ‖ρ (vec I y (e j))‖ * t ^ N :=
          mul_le_mul_of_nonneg_right (norm_le_sqrt I hρ _) (by positivity)
      _ ≤ Real.sqrt N * (lam⁻¹ * C1 / c' ^ N / t ^ N) * t ^ N := by gcongr
      _ = Real.sqrt N * (lam⁻¹ * C1 / c' ^ N) := by field_simp

end
end

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsReducedBasisBoundedType_of_instance : ∀ I : AutInst, RedBasis I := by
  atlas_forward_decl GlobalTheory.CuspGeo.redBasis_holds
end
