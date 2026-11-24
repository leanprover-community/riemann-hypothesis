module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition

@[expose] public section



section
noncomputable section
namespace GlobalTheory.Fc.S0
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
end
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
variable (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition)
def CovolumeBoundThirdPlaceSeries : Prop := Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH _ _ _ b =>
  ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH))
def FunctionalCondition : Prop := Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun Fm => DIVinN Fm) fun C CH _ _ _ b =>
  ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH))
def GeometricWeakCompatibility' : Prop := Row Q Lk (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∃ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧
  GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.BigOn.More (b.part t).pt)
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
structure OpenParameterStatements (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Prop where
  hPA : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition
  hLamP : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition
  hDivG : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotDivisorCondition
  hDcPtG : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition
  selJ : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition
  tie : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.Row_tie_alt
  lab : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowLabelCondition
  good : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowGoodnessCondition
  geo : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility'
  mi : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition
  kap : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowKappaCondition
  df : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowDefectCondition
end GlobalTheory.Fc.S0
end
end
