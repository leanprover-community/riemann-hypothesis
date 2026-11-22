module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EvLApply

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Numbers

open Formalism.BasicNotions Formalism.MainNotions
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb)

variable (D : D7) (i : Fin D.R.m)

end Numbers

section Geo

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m)

end Geo

end GlobalTheory.CompanionTheory.Ar.Rec
