module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAltAlt
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M

def stageAOfSwitch (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (N : TwNew D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep)
    (rep' : N.toD7.what₂.FT → NG.FinTyp N.toD7.host.E N.toD7.R.r) (e : HEq rep' rep) :
    _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL N.toD7 (N.cf cf) rep' where
  host := ⟨a.host.fr, a.host.jLL, a.host.embLL⟩
  jE := a.jE
  frame := a.frame
  A := _root_.GlobalTheory.HeightCounting.Up.LiTw.sideA_alt N a.A
  cg := _root_.UpperTheory.One.M.New.cgMk s a.cg.e (_root_.UpperTheory.One.M.New.cgGood s a.cg) (_root_.UpperTheory.One.M.New.cgSurj a.cg) a.cg.zero a.cg.loc a.cg.tw a.cg.inf a.cg.csd
  au := a.au
  row := by obtain rfl : rep' = rep := eq_of_heq e; exact a.row
  fr := ⟨a.fr.jE, a.fr.eOm, a.fr.comm⟩
  fr_jE := a.fr_jE
  pht := { a.pht with }
  depth := by obtain rfl : rep' = rep := eq_of_heq e; exact a.depth
  elem := { a.elem with }
  val := { a.val with }
  labc := a.labc
  zeta := a.zeta
  omax := a.omax
end UpperTheory.One.M
end
end
