module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
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

namespace GlobalTheory.Pdv

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def At (ex : Extra D L hT Gi Gl K Y cX) (E : KerEnt D Y ex.tw) : Prop :=
  (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi D ex.tw ∧ OrbitPlaces.Stab0 D) ∧
    ∃ (ep : _) (be : _) (sg : _),
      OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Gi K ∧ OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧
      OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) E ep be sg) Y ∧ OrbitPlaces.Shape D L Gi (OrbitPlaces.ofKer (nuRowOK D) E ep be sg)

variable {ex : Extra D L hT Gi Gl K Y cX}

def IsEntC (t : KerEntTied ex) : Prop :=
  ∃ (P : Examples₂.EntPl D) (B : PlaceMatrixFamily D) (h : KerEntHyp P t.O B Y ex.tw), t.ent = kerEntC P t.O B h

structure Duty (t : KerEntTied ex) : Prop where
  col : GlobalTheory.KerJ.ColSide t
  entC : IsEntC t
  rk : t.RK
  forms : ∃ t' : KerEntTied ex, GlobalTheory.KerJ.ColSide t' ∧ GlobalTheory.KerJ.FormsPin t'

end GlobalTheory.Pdv

end
