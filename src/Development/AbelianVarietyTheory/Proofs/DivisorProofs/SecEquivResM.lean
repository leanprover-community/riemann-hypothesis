module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffGlue

attribute [instance] Data.grp Data.mod

variable {T : Scheme.{0}} (D : Data T)

variable {D}

end GlobalTheory.AffGlue
