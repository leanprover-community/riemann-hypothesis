module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.MExistsCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def toInfI (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (s : I.Ginf) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J :=
  (Formalism.L2.SG.Measures.splitA I.cm.sig I.J (Formalism.L2.SG.AdBridge.toHA I hb (s, 1))).1

def toFinI (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (x : I.Gf) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.cm.sig I.J :=
  (Formalism.L2.SG.Measures.splitA I.cm.sig I.J (Formalism.L2.SG.AdBridge.toHA I hb (1, x))).2

def MeasTieCore (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (μf : Measure A.I.Gf) [SigmaFinite μf] (muN muH : D.what₂.Word → Measure A.I.Ginf)
    (Mb : MBlk A L) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso A.I) : Prop :=
  Mb.measG.μG = (A.I.muA μf).map (Formalism.L2.SG.AdBridge.toHA A.I hb) ∧
    Mb.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf A.I).map (toInfI A.I hb) ∧
    Mb.measG.μGf = μf.map (toFinI A.I hb) ∧
    ∀ u, Formalism.L2.SG.Measures.amb (Mb.measW u).μNinf = (muN u).map (toInfI A.I hb) ∧
      Formalism.L2.SG.Measures.amb (Mb.measW u).μHinf = (muH u).map (toInfI A.I hb)

variable (D)

def MExistsCore : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (μf : Measure A.I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (muN muH : D.what₂.Word → Measure A.I.Ginf),
    (∀ u, IsHaarOnSet A.I (Ninf A.I (eC A L) (zC A L u)) (muN u)) →
    (∀ u, IsHaarOnSet A.I (Hset A.I (Set.range (eC A L) ∪ Set.range (fC A L) ∪ {zC A L u})) (muH u)) →
    ∃ Mb : MBlk A L, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso A.I, MeasTieCore A L μf muN muH Mb hb

theorem mExists_of_core (h : MExistsCore D) : MExists D := by
  intro A L P Rf Xu Bu Pi Mu Wb
  haveI := Bu.haar
  haveI := Bu.sf
  obtain ⟨Mb, hb, hT⟩ := h A L Bu.μf Mu.muN Mu.muH Mu.muN_haar Mu.muH_haar
  exact ⟨Mb, hb, hT⟩

end Formalism.L2.SG.MExistsCut

namespace Formalism.L2.SG.MExistsCut

open Formalism.L2.SG.Measures

def MGExists : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (r : ℕ),
    ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso I, ∃ M : MeasG I.cm.sig I.J r, M.IsTextNorm ∧
      M.μG = (I.muA μf).map (Formalism.L2.SG.AdBridge.toHA I hb) ∧
      M.μGinf = (Formalism.L2.SG.ProjRows.muInf I).map (toInfI I hb) ∧ M.μGf = μf.map (toFinI I hb)

variable (D)

end Formalism.L2.SG.MExistsCut
