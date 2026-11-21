import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSucc

section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem siegel_weil_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  intro E _ _ _ Ψ hΨ n N hn
  induction N with
  | zero =>
    intro _ M R φ _ Z _
    rw [Base.swd_zero, Base.swDiff_deg_zero]
  | succ N ih =>
    intro h
    exact GlobalTheory.T.siegelWeil_formula_degree_succ E Ψ hΨ n N hn h (ih (by omega))

end GlobalTheory.SW
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  atlas_forward_decl GlobalTheory.SW.siegel_weil_definite
