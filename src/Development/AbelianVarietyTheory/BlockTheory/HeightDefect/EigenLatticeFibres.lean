module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} [Field K] [NumberField K]

namespace GenFib

variable {t t' : SAB H (Sp (𝓞 K))} (F : GenFib t) (F' : GenFib t')

attribute [instance] CxFib.grp

end GenFib

section Sum

variable {S : Scheme.{0}}

end Sum

namespace CMObj

variable {ρ : 𝓞 K} {p q : ℕ} (X : CMObj H K ρ p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFibres
