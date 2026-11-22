module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
public import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
def ratL {D : D7} (L : LocAll (lay0 D)) (S : RatDat D.ntw) : RatDat (withLoc L).ntw := { S with }

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

end GlobalTheory.Mem.Top.Bl

end
