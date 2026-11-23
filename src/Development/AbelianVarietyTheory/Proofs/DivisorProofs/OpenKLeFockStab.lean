module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
