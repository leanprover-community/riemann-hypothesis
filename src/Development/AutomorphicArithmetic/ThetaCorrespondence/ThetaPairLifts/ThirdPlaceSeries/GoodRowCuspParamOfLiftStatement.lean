module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodRowCuspParamOfLift
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.cuspParam_of_definite_liftAll : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D → (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  first | exact @_root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt | exact _root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt | (intros; apply _root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt <;> assumption)
end
