module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
public import Formalism.SharpRestriction.Divisibility.JumpSets
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtsOk
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

theorem _root_.GlobalTheory.T.weight_lambda_shift_nonneg' : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts (Fm.D x i).what₂.Tau, W.Ok (GlobalTheory.ExpTie.parOf (Fm.L x i) j) ∧
    (∀ τ, ∃ c : ℤ, ∀ a : Fin (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank,
      (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ).w a + c) ∧
    (∀ τ a, a < (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Nr → 0 ≤ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ∧ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf (Fm.L x i) j) : ℤ)) ∧
    W.T2.card ≤ (Fm.D x i).host.T2.card ∧ W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet (Fm.D x i) := by
  first | exact @_root_.GlobalTheory.ExpTie.Lift.wts_ok_alt | exact _root_.GlobalTheory.ExpTie.Lift.wts_ok_alt | (intros; apply _root_.GlobalTheory.ExpTie.Lift.wts_ok_alt <;> assumption)
end
