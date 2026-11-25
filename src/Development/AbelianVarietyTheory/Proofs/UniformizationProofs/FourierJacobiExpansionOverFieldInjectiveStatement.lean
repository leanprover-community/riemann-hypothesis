module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.fourierJacobiExpansion_overField_injective : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  first | exact @GlobalTheory.UU.ExpFUniq.main
