module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.UnitaryNorms.CharGal
public import Formalism.LocalToGlobal.HermitianForms.TiedTwAll
public import Formalism.LocalToGlobal.JointCharacters.SameChr
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.EMtLevel
public import Formalism.LocalToGlobal.UnitaryNorms.JointCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure LocalGlobalCompatibilityData (ex : Extra D L hT Gi Gl K Y cX) where

  host : Host.HostTied D

  level : Host.LevelTied D

  cols : Forms.ColsTied D

  full : Forms.ColsFull cols

  extra : Forms.ColumnsExtraCompatible full ex

  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA

  twIn : TwIn D
  n : NormalizedTwistCompatibility D ex.nch twIn

  frameN : Host.SameFrameN host n.gal.fr.jE

  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th

  chrVal : Host.ValLL0 D n.cf

  chrDt : Host.DtTied D n.cf

  chrN : Host.NCharTied D n.cf ex.nch n.tp

  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp

  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp

  tw : Forms.TwistedColumnsCompatible n.tp cols ex.tw

  sameChr : JoinChr.SameChr theta.T thetaChr

  what₂ : Rows.RowsCompatible D host n.cf n.tp

def Tied (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (LocalGlobalCompatibilityData ex)

end

def C2 : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Tied (Fm.ex x hx i)

end Formalism.L2
