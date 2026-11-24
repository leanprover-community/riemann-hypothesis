module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
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

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieLift
theorem lift_principal_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
    ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w hw j g0 =>
    GlobalTheory.GalLift.Transl.lifts (R2 p) j (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1.lev g0
end GlobalTheory.TieLift
end
