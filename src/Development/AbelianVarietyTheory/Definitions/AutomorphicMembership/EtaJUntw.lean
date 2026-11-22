module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalRingCardinality.DataRRMetric

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.Mem NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sub

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable {R : RealDat D A Ks} {F : Face D A}

end Sub

section Metric

open scoped InnerProductSpace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
  {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

end Metric

attribute [instance] RowT.grp RowT.fin RowT.alg

namespace RowT

variable {D : D7} {fr : CharFrame D} {xi : D.what₂.Tup → HChar D.host.E} (r : RowT D fr xi)

end RowT

end GlobalTheory.Mem.Top

end
