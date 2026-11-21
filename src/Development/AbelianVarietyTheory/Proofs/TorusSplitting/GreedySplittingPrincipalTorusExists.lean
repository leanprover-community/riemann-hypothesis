import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBasisSpanEqOfDiscrete
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PrincipalTorusEqZeroOfImLattice
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIndependentIsU
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIntegersSpan
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThickSplitRealSpanBot
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DivSqLeOfForallDivAddSqLe
import BuildAid.ForwardExisting

section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem greedy_splitting_exists : SplitStatement := by
  intro E _ _ _ X DF P
  by_cases h : X.la1 < P.th
  · exact greedy_splitting_thin exists_short_integers_span
      (exists_short_independent_isU transference_discrete_lattice principalTorus_im_perfect)
      E X DF P h
  · exact ⟨⊥, thickSplit_bot E X DF P h⟩

end GlobalTheory
end

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.GlobalTheory.T.greedy_splitting_principal_torus_exists : SplitStatement := by
  atlas_forward_decl GlobalTheory.greedy_splitting_exists
