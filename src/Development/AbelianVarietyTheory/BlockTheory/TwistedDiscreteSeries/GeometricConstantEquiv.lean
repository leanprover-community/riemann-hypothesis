module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1))

set_option synthInstance.maxHeartbeats 100000

end GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv
