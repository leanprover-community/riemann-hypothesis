import Mathlib
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta

namespace GlobalTheory.TorusAlg.Test

section General

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
  {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem exists_chart (hL : L.IsLB) (x : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  obtain ⟨y⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  have : x y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨i, fun w _ => ?_⟩
  rw [show w = y from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  exact hi



end General



end GlobalTheory.TorusAlg.Test
