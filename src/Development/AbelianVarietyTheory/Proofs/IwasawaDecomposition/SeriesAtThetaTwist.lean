module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up.SerCp
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ExportSeries hiding Base

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

section L1
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

end L1

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

end L2

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)

section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N}

end

section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N} {ρ : Setup X}
  {Y : NExp (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N X} {i : X.Tw} {j : Fin (lt c a).D.R.m} {s : Bool} {rd : Rd ρ Y i j s}

end

end L2

section L3
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)
  {Γ : Type} [i1 : Group Γ] [i2 : Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 (lt c a).D.what₂.LL Γ Pl0 I0 (List ℕ) T (lt c a).D.R.m} {Ks : Type} [i3 : Field Ks] [i4 : NumberField Ks]
  [iK : Algebra Ks (lt c a).D.what₂.LL] {Rl : RealDat3 (lt c a).D A3 Ks}
  {v₀ : ∀ (j : Fin (lt c a).D.R.m) (σ : (lt c a).D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec} {j : Fin (lt c a).D.R.m}
  {X : ExportSeries.Base (Vc (lt c a).D j) (Wc (lt c a).D j)} {ν : ℂ}

end L3

section L4
open GlobalTheory.SeriesTie
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)

end L4

end GlobalTheory.HeightCounting.Up.SerCp
end
