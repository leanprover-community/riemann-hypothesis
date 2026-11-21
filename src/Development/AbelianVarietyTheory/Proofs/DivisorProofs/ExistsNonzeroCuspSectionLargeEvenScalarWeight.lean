import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe

section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

theorem GlobalTheory.ScalarPoin.exists_cusp_ne_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ N
  obtain ⟨y, hy⟩ := GlobalTheory.FlagSecProbe.dom_nonempty X
  obtain ⟨n, hN, -, hev, P, hP, hPy⟩ := GlobalTheory.ScalarPoin.exists_cusp_ne E r X hp0 hpr hχ y hy N
  exact ⟨n, hN, hev, P, hP, y, hy, hPy⟩
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  atlas_forward_decl GlobalTheory.ScalarPoin.exists_cusp_ne_some
