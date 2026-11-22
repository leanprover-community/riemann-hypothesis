module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def CombAt (P : Pl D → Prop) {S T : HSp D} (c : WO S T →₀ ℂ) : Prop := ∀ u ∈ c.support, MxAt P u

def extS {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) (c : WO A T →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resS T).symm (u, 0)

def extT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c : WO S A →₀ ℂ) : WO S T →₀ ℂ :=
  c.mapDomain fun u => (o.resT S).symm (u, 0)

def kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w : WO S L'') : WO L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)

def lastBi {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) : WO A S → WO S X → ℂ :=
  fun u => o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))

def BiVacAt (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A') (P : Pl D → Prop)
    (C : WO A S → WO S A' → ℂ) : Prop :=
  (∀ v, Vac ψ A S LA LS P fun u => C u v) ∧ ∀ u, Vac ψ S A' LS LA' P (C u)

variable {u : D.what₂.Word}

variable {d : Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffDat d k ι)

namespace OffDat

end OffDat

variable {o} {Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)}

namespace OffTest

theorem combAt_single_zero (P : Pl D → Prop) {S T : HSp D} (c : ℂ) : CombAt P (Finsupp.single (0 : WO S T) c) := by
  intro u hu
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
  intro i j
  exact Submodule.zero_mem _

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  simp [comb]
  exact GlobalTheory.MixPer.heisO_zero ψ S T f

end OffTest

end GlobalTheory.FinPl

end
