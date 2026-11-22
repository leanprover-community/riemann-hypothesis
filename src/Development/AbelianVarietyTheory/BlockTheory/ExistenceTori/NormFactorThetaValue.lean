module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

attribute [local instance] Over.cartesianMonoidalCategory

section TwoLifts

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

end TwoLifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

end GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
