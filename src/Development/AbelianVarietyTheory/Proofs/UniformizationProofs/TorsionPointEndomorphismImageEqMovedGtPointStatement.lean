module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPoint

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E : EndU U.toUnifPre, Function.Injective E.h → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) x, QkToAkU U.toUnifPre F k p x → ∀ g', E.Act p.g g' → ∃ p' : QkPt D.toPre F k, p'.g = g' ∧ QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  first | exact @GlobalTheory.UT.EndTors.main
