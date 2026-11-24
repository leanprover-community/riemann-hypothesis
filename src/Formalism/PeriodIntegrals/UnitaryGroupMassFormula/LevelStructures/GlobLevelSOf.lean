module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

def CMInst : Prop :=
  ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J

def FrameStd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ T : X.B.I.F,
    (frameOf X w).IsStd X.B.I.cm.sig X.B.I.J T

def LatAdapted : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ ΛX ΛW ΛY : Set (Fin X.B.I.n → X.B.I.E),
    Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) ΛX ΛW ΛY ∧
    Kf X.B.I.cm.sig X.B.I.J (ΛX ∪ ΛW ∪ ΛY) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def ProdNH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word),
    IsProdNH X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (X.measW w).μSf (X.measW w).μNf (X.measW w).μHf

def GlobFromParts : Prop := LevelSAll → CMInst → FrameStd → LatAdapted → ProdNH → GlobLevelS

end MassDataLevelSSteps
