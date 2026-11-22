module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Satake

end Satake

section Spaces

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.Links.RealDat D A Ks) (F : Face D A)

open Classical in
def badS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Spaces

end GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

end
