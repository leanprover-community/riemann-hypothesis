module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair (Pair Unif resChar phiOne inX avec)
open GlobalTheory.SplitWeil (HasConductor IsUnitVol)
open GlobalTheory.StepData (XIx Ix latOf box)
open GlobalTheory.SymChain (SymData)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences

variable {D : D7}

attribute [instance] LocF.fld LocF.val LocF.top LocF.loc LocF.ms LocF.bor

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

end Frames

namespace Dbl

variable {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (X : Dbl ψ σ)

namespace Tower

variable {X} {s κ t j : ℕ} {H : j + 1 + 1 + 2 * σ = s} (Y : X.Tower s κ t j H)

end Tower

end Dbl

namespace End

variable {ψ : AddChar (AF D.host.F) ℂ} {X' : HSp D} (X : End ψ X')

attribute [instance] LevPl.lat

namespace Tower

variable {X} {s κ t : ℕ} (Y : X.Tower s κ t)

end Tower

end End

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences

end
