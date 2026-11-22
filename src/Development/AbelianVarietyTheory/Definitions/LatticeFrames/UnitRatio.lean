module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

def UnitRatio (S : ℕ → Prop) (x y : ℂ) : Prop :=
  y ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ (x / y) ^ n = (r : ℂ) ∧ ∀ p : ℕ, p.Prime → padicValRat p r ≠ 0 → S p

structure Base (c : Comm D) where
  Λ : ∀ j, GlobalTheory.FinPl.Lat (c.V j)
  β : ∀ j, GL (Fin (c.V j).rank) (Lev.EAf D)
  b : ∀ j, GA D (c.V j)

  ΛT : GlobalTheory.FinPl.Lat c.T
  βT : GL (Fin c.T.rank) (Lev.EAf D)
  bT : GA D c.T
  LT : GlobalTheory.FinPl.Lat c.T
  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)
  P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ

variable {c : Comm D}

section Off

open GlobalTheory.FinPl

variable {B : Base c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : Off B k ι)

namespace Off

end Off

end Off

section AtLevel

open GlobalTheory.LocMod

attribute [instance] GAt.fld GAt.val GAt.top GAt.loc GAt.mea GAt.bor

variable {B : Base c} {τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E}

end AtLevel

end GlobalTheory.Fam

end
