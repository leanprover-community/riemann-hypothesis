import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CfgTie

namespace CompanionTheory.WaveGrid.Inhab

open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem int_of_half {k : ℕ} {u v : ℕ → ℝ} (hk : 1 ≤ k)
    (hu : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m)
    (hv : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, v i - ((k : ℝ) - 1) / 2 = m) :
    ∀ i ∈ Icc 1 k, ∃ n : ℤ, v i - u 1 = n := by
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m1, hm1⟩ := hu 1 le_rfl hk
  obtain ⟨m2, hm2⟩ := hv i hi1 hik
  exact ⟨m2 - m1, by push_cast; linarith⟩

theorem ok_diff (P : M.Par) (hk : 1 ≤ P.k) (hT : 0 < P.T) (hT' : 0 < P.T') (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b) :
    P.OK := by
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, int_of_half hk hu.half hu'.half, ?_⟩
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
  obtain ⟨b1, b2⟩ := inter_half hc hu' i hi1 hik
  simp only [M.Par.lo, M.Par.hi]
  have hmax := max_le a2 b2
  have hmin := le_min a1 b1
  linarith

def uP (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l + 1 then u i + n₀ else u i
def uM (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l then u i - n₀ else u i

theorem ok_plus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uP u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l + 1
    · refine ⟨n + n₀, ?_⟩
      simp only [uP, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uP, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uP]
    by_cases h1 : i + 1 = l + 1
    · have hil : i = l := by omega
      subst hil
      have h2 : ¬ (i = i + 1) := by omega
      rw [if_pos h1, if_neg h2, min_self, max_eq_right (by linarith)]
      linarith
    · by_cases h2 : i = l + 1
      · rw [if_neg h1, if_pos h2, max_self, min_eq_left (by linarith)]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith

theorem ok_minus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uM u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l
    · refine ⟨n - n₀, ?_⟩
      simp only [uM, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uM, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uM]
    by_cases h2 : i = l
    · subst h2
      have h1 : ¬ (i + 1 = i) := by omega
      rw [if_neg h1, if_pos rfl, max_self, min_eq_right (by linarith)]
      linarith
    · by_cases h1 : i + 1 = l
      · rw [if_pos h1, if_neg h2, max_eq_left (by linarith), min_self]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith



noncomputable def lamX (x : ℤ) : Fin (2 * 0 + 3 + 1) → ℝ := ![(x : ℝ) + 1 / 2, -79 / 2, -119 / 2, -159 / 2]
noncomputable def uX : ℕ → ℝ := fun i => if i = 1 then 80 else if i = 2 then 0 else -50







noncomputable def cfg₁ : Sz.Cfg := { cfg₀ with a := 801 / 2 }

theorem cfg₁_ok : cfg₁.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cfg₁, cfg₀, Sz.Cfg.v] <;> norm_num

noncomputable def Pc : M.Par := cfgPar cfg₁ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)




end CompanionTheory.WaveGrid.Inhab
