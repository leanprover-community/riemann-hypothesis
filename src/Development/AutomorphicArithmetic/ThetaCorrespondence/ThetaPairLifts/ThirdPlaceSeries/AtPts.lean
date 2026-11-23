module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
theorem GlobalTheory.LiftWeightForced.atPts_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ,
    Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i)
      (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ j τ => GlobalTheory.LiftWeightForced.isLamPrime_lamLdef (Fm.D x i) j τ⟩⟩
end
end
