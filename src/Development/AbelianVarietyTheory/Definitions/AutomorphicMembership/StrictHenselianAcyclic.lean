module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev Dof (x : St P) : D7 := (w.st x.o.Z).toD7

abbrev cfOf (x : St P) : CharFrame (Dof x) := TC.cf w.I w.l x.o.Z

open Classical in
def QOf (P : Pre2 K w) (v : B.places.Pl) : Finset (HeightOneSpectrum (𝓞 B.host.E)) := if v ∈ P.Wt then T.Q v else ∅

abbrev AllSt (p : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop) : Prop :=
  StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), p K B f T w P x

variable (hL)

def SMt : Prop := AllSt fun _ _ _ _ w P x => Nonempty (InMt x.r.Y (cfOf x) w.I.xi (QOf P))

structure Kept {D D' : D7} (c : NChoice D) (c' : NChoice D') : Prop where
  gal : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd
  set : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  forms : GlobalTheory.TwistChoice.SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  twI : HEq c.twI c'.twI
  sd : HEq c.sd c'.sd
  Q : HEq c.Q c'.Q
  k : HEq c.k' c'.k'
  psi : HEq c.psi' c'.psi'

end GlobalTheory.HeightCounting.Up

end
