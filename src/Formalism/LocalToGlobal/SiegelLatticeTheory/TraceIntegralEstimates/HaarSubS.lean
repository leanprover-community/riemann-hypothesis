module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Hu (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Set X.B.I.Ginf :=
  Hset X.B.I (Set.range (fun a => X.eR a) ∪ Set.range (fun a => X.fR a) ∪ {X.zR u})

def SDecomp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsClosed (X.SinfU u) ∧ (1 : X.B.I.Ginf) ∈ X.SinfU u ∧
    (∀ a ∈ X.SinfU u, ∀ b ∈ X.SinfU u, a * b ∈ X.SinfU u) ∧ (∀ a ∈ X.SinfU u, a⁻¹ ∈ X.SinfU u) ∧
    (1 : X.B.I.Ginf) ∈ X.NinfU u ∧ (∀ a ∈ X.NinfU u, ∀ b ∈ X.NinfU u, a * b ∈ X.NinfU u) ∧
    (∀ a ∈ X.NinfU u, a⁻¹ ∈ X.NinfU u) ∧
    IsCompact (Hu X u) ∧ (1 : X.B.I.Ginf) ∈ Hu X u ∧ (∀ a ∈ Hu X u, ∀ b ∈ Hu X u, a * b ∈ Hu X u) ∧
    (∀ a ∈ Hu X u, a⁻¹ ∈ Hu X u) ∧
    (∀ h ∈ Hu X u, ∀ n ∈ X.NinfU u, h * n * h⁻¹ ∈ X.NinfU u) ∧
    (∀ n ∈ X.NinfU u, ∀ h ∈ Hu X u, n * h ∈ X.SinfU u) ∧
    (∀ s ∈ X.SinfU u, ∃ n ∈ X.NinfU u, ∃ h ∈ Hu X u, s = n * h)

def MeasN : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    (∀ K : Set X.B.I.Ginf, IsCompact K → X.muN u K < ⊤) ∧
    (∀ n ∈ X.NinfU u, (X.muN u).map (fun x => x * n) = X.muN u) ∧
    (X.muN u).map (fun x => x⁻¹) = X.muN u ∧
    ∀ h ∈ Hu X u, (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u

def MeasH : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsFiniteMeasure (X.muH u) ∧ (∀ h ∈ Hu X u, (X.muH u).map (fun x => x * h) = X.muH u) ∧
    (X.muH u).map (fun x => x⁻¹) = X.muH u

def NuQSFinite : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), SFinite (X.nuQ u)

end Formalism.L2.S.Pv.HaarSubS
