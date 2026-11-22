module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM

section Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R]

end Lie

section Line

variable {K : Type} [Field K] [NumberField K]

end Line

section Pol

variable {K : Type} [Field K] [NumberField K]

end Pol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

attribute [instance] CMObj.field CMObj.numberField CMObj.alg

namespace CMObj

variable {c : Coeff l} {p q : ℕ} (o : CMObj c p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
