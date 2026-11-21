import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem end_isogeny_algebra_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K),
    Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  intro K _ A
  obtain ⟨hfin, hfree, hrk⟩ := GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A
  haveI : Module.Finite ℤ (End A) := hfin
  haveI : Module.Free ℤ (End A) := hfree
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange]
  exact hrk

end GlobalTheory.AV.AbVar
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.end_isogeny_algebra_finite_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K), Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  first | (exact @GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (exact GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (intros; apply GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le  <;> assumption)
end
