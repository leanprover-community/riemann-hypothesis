import Mathlib
import Development.WeilBound.CoreStatements.FlagImmersions.DecompositionPowerSumsTopDegree
import BuildAid.ForwardExisting

section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem form_top_succ_eq_sum_pk : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RP Ψ N), 2 ≤ N → F.IsHomogeneous (dimFl Ψ N + 1) → ∃ Q : Ψ → ℕ → RP Ψ N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧ F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k :=
  @RootFieldNumerics.decomposition_power_sums_top_degree

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_power_sum_decomposition : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RP Ψ N), 2 ≤ N → F.IsHomogeneous (dimFl Ψ N + 1) → ∃ Q : Ψ → ℕ → RP Ψ N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧ F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.form_top_succ_eq_sum_pk
