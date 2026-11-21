import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_of_hasQ : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → HasQ N f (fun n => ε (a n)) → ∃ h : HahnSeries ℚ Ω, IsExp ε f h ∧ (∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := by
  intro Ω _ ε N f a hN hf
  obtain ⟨Φ, hΦ1, hΦ0⟩ := GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN
  set h := Φ (PowerSeries.mk a) with hh
  have hc : ∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k := fun k => by
    rw [hh, hΦ1]; simp
  have h0 : ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := fun r hr => hΦ0 _ r hr
  refine ⟨h, ⟨⟨N, hN, fun r hr => ?_⟩, 0, fun z hz => ?_⟩, hc, h0⟩
  · by_contra hne
    push_neg at hne
    exact hr (h0 r fun k hk => hne k (by rw [hk]; push_cast; rfl))
  · have hc' : ∀ k : ℕ, h.coeff (((0 + k : ℤ) : ℚ) / N) = a k := fun k => by
      simpa using hc k
    have h0' : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((0 + k : ℤ) : ℚ) / N) → h.coeff r = 0 := fun r hr =>
      h0 r fun k hk => hr k (by simpa using hk)
    rw [fn_hasSum_reindex_nat Ω ε h N 0 a z (up f z) hN hc' h0']
    have hq := (hasQ_iff N f _).mp hf ⟨z, hz⟩
    simpa [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hq

end GlobalTheory
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → HasQ N f (fun n => ε (a n)) → ∃ h : HahnSeries ℚ Ω, IsExp ε f h ∧ (∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := by
  atlas_forward_decl GlobalTheory.fn_hahnSeries_of_hasQ
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExpD

theorem hasQ_DD_int : HasQ 1 DD fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : ℂ) := by
  rw [hasQ_iff]
  intro τ
  have := ReciprocityTheory.ChartRestriction.L1.isMF_DD.hasSum τ
  rw [← ReciprocityTheory.ChartRestriction.L1.dC_eq] at this
  simpa [ReciprocityTheory.ChartRestriction.L1.qm, ReciprocityTheory.ChartRestriction.L1.dC, PowerSeries.coeff_map] using this

theorem expD : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧
    h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  have hD : HasQ 1 DD fun n => ε ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω) := by
    simpa only [map_intCast] using hasQ_DD_int
  obtain ⟨h, hexp, hk, hz⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε 1 DD
    (fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)) one_pos hD
  have h1 : h.coeff 1 = 1 := by
    have := hk 1
    simpa [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one] using this
  have hlow : ∀ r : ℚ, r < 1 → h.coeff r = 0 := by
    intro r hr
    by_cases hr' : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr'
      have hk1 : (k : ℚ) < 1 := by simpa using hr
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast hk1
        omega
      subst hk0
      rw [hk 0]
      simp [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_zero]
    · push_neg at hr'
      exact hz r hr'
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)
  have hord : h.order = 1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (h1 ▸ one_ne_zero)) ?_
    by_contra hlt
    push_neg at hlt
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hne) (hlow _ hlt)
  refine ⟨h, hexp, hne, ?_, ?_⟩
  · rw [HahnSeries.leadingCoeff_eq, hord, h1]
  · intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr
      exact ⟨_, hk k⟩
    · push_neg at hr
      exact ⟨0, by simpa using hz r hr⟩

end GlobalTheory.FNExpD
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧ h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  atlas_forward_decl GlobalTheory.FNExpD.expD
end
