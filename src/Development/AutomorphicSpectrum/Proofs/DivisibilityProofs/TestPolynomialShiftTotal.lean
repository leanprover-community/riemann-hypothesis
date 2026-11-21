import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.WeilBound.CoreStatements.FlagImmersions.TestPolynomialShiftValues
import BuildAid.ForwardExisting

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem testPoly_facts : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) ∧ 0 < testDeg Ψ N j ∧ (N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = 0 ∧ Tot τ (testPoly j : RP Ψ N) = ((dimX Ψ N j : ℝ) + 1) * ((N - j : ℕ) : ℝ) * testDeg Ψ N j) ∧ (¬ N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j) ∧ Tot τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j)) := by
  exact @RootFieldNumerics.test_polynomial_shift_values

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_polynomial_shift_total : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) ∧ 0 < testDeg Ψ N j ∧ (N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = 0 ∧ Tot τ (testPoly j : RP Ψ N) = ((dimX Ψ N j : ℝ) + 1) * ((N - j : ℕ) : ℝ) * testDeg Ψ N j) ∧ (¬ N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j) ∧ Tot τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.testPoly_facts
