module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : GlobalTheory.Published.LocalLanglandsGL}

section
variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} (S' : SStage B w.C Z.W)
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

def nchUp (nch : NChoice (w.D Z)) : NChoice (w.D (upL Z S' N h)) := { nch with }

def xdUp (xd : ThData (w.D Z)) : ThData (w.D (upL Z S' N h)) := { xd with }
end

end GlobalTheory.LayerMove
end
