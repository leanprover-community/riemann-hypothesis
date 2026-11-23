module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftTwistLevelFormEqUnitMulClassSum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf X.R.toRealDat j B → ∀ (ψ : Twist D Circle) (t : X.T), ψ.Good → B.admitted ψ.Q → IsTupOf X.R.toRealDat B ψ t →
  ∀ ω : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), IsClassSystem (Vc D j) (B.levJ ψ) rep → ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ),
  ∃ (z : GA D (Vc D j)) (a : ℂ), IsCentAt j (X.R.Q t) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime X.R.toRealDat t) a ∧ ∀ y : (X.R.HV j t).H,
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y h)) ∈ B.formsC ψ →
    X.R.thF j t y (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) =
      a • B.classSum ω ψ rep (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * finPt (Vc D j) z))) := by
  first | exact @GlobalTheory.LiftClassSumTwist.thF_eq_classSum | exact GlobalTheory.LiftClassSumTwist.thF_eq_classSum | (intros; apply GlobalTheory.LiftClassSumTwist.thF_eq_classSum <;> assumption)
