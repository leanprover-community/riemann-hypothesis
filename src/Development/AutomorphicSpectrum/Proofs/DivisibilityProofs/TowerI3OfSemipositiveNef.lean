import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GapNonnegOfDominant
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefCone

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem RootTower.tower_I3_of_nef_inputs :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  intro Ψ _ _ N T hA1 hM1 hM2 hAN abelian₂
  obtain ⟨s₀, hs₀, h⟩ := hA1 abelian₂
  refine ⟨s₀, hs₀, fun B hB c lam s hl hs hss hd ht => ⟨?_, h B hB c lam s hl hs hss hd⟩⟩
  intro p hp
  have hn := RootTower.nefFib_of_nefThreshold Ψ N T hM1 hM2 B c (T.lamS lam s) hd ht p hp
  exact (GlobalTheory.T.curve_degree_linear_nef_cone Ψ N (T.M B c) (T.lamS lam s) 0 s 0 0).2.2.1 p hs.le hn (hAN B c p hp)

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_I3_of_semipositive_nef : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs
