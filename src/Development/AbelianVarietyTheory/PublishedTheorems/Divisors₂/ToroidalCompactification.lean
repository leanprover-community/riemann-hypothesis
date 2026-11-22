module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogDR

section Nabla

variable {R : Type} [CommRing R]

variable (A : Over (Sp R)) [GrpObj A]

variable {A}

variable {D : Derivation ℤ R R}

end Nabla

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

attribute [instance] Chart.ring Chart.alg Chart.grp

variable {t : SAB H X} {V : X.Opens}

namespace Chart

variable (c : Chart t V)

end Chart

end GlobalTheory.LogDR

namespace GlobalTheory.Published

open GlobalTheory.LogDR

end GlobalTheory.Published
