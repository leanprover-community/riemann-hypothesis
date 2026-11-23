module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxAbs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {D : D7}

theorem piH_mem_KvH (X : HidaSetting D) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) (hz : z ∈ KHg X u) :
    piH X u v z ∈ KvH X u v := by
  have h : (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
      Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hz
  rw [Kf, Subgroup.mem_iInf] at h
  exact h v

def SurjH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ f : ∀ p : TypX X, KvH X u p.1,
      ∃ z ∈ KHg X u, ∀ p : TypX X, piH X u p.1 z = f p

def LocH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ z ∈ KHg X u,
      (∀ p : TypX X, ∃ w ∈ unitaryLevelClosureSubgroup X hb u, piH X u p.1 w = piH X u p.1 z) → z ∈ unitaryLevelClosureSubgroup X hb u

theorem idxProdH_of (hS : SurjH) (hL : LocH) : IdxProdH := by
  intro D X hb hK u hT hLv
  exact PI.MassDataKppVolLemmas.IdxAbs_relIndex (KHg X u) (unitaryLevelClosureSubgroup X hb u) (fun p : TypX X => piH X u p.1)
    (fun p : TypX X => KvH X u p.1) (fun p z hz => piH_mem_KvH X u p.1 z hz)
    (hS X hb hK u hT hLv) (hL X hb hK u hT hLv)

end PIW.MassDataColumns
