module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace Formalism.MainNotions.VanishingOnXAndXPlusGluing

export Formalism.MainNotions.S.UnitaryVolumeMass (DefiniteComplementRank Lem1 Lem2 LatticeSpanEquality ThmA HyperplaneEquality ThmB)

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LatS (D : D7) : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev FlS (D : D7) (T : ℕ) : Type := LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)

def Conclusion1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stLem1 D

def Conclusion2 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stLem2 D

def PointsLemma (D : D7) : Prop :=
  S.UnitaryVolumeMass.stThmA D

def Conclusion4 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stThmB D

def GlobalIntegralModelCondition (D : D7) : Prop :=
  S.UnitaryVolumeMass.DefiniteComplementAllWords D

def HyperplaneRank (D : D7) : Prop :=
  S.UnitaryVolumeMass.HyperplaneRankAllWords D

def DefiniteRankOne (D : D7) : Prop :=
  S.UnitaryVolumeMass.DefiniteRankOneAllWords D

end Formalism.MainNotions.VanishingOnXAndXPlusGluing

end
