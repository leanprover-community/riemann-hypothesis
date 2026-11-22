module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.StepData GlobalTheory.SymBridge
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

section Gen
variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end Gen

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) {d : Dat (I.rec7 l Z) u}
  {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) (I.rec7 l Z).host.E}

end GlobalTheory.LocMod
end
