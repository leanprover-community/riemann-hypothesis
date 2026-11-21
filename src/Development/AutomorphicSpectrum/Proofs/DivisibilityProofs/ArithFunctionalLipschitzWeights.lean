import Mathlib
import Development.WeilBound.CoreStatements.FlagImmersions.LinearRootPowerLipschitz
import BuildAid.ForwardExisting

section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linA_pow_continuous_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) :=
  @RootFieldNumerics.linear_root_power_lipschitz

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_functional_lipschitz_weights : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.linA_pow_continuous_lipschitz
