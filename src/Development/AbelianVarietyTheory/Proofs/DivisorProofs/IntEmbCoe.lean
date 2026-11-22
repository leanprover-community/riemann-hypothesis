module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

section Lemmas

variable {O : Type} [CommRing O]

end Lemmas

end GlobalTheory.CurveRootGeometry
