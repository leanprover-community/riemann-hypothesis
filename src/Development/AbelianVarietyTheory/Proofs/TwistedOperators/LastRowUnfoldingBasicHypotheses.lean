module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvarianStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestFlippedFiniteTensorRowIsThetaFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHeisenbergCombinationsJointRowGoodStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataJointlySmoothThetaEvenIndexStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowBasic

theorem c3 : Big fun ch => ∀ t (M : Vol ch.G), M.Is t → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t M hM X hX _
  refine (hM.vtx X ?_).haar_fund
  cases X <;> simp only [DefNode, Node.InRange] at hX ⊢ <;> omega

theorem c4 : Big fun ch => ∀ t Φ β M, IsTermVol t ch.S.toGridChoice Φ β M → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t Φ β M hM X hX hne
  cases X with
  | grid i j =>
    obtain ⟨hi, rfl⟩ := hX
    exact (hM.2 i hi).haar_fund
  | top j =>
    have : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
    exact (hM.1 j this).haar_fund
  | core i => exact hX.elim

theorem basicAt : Big fun ch => BasicAt ch := by
  have hall := (((((((GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant.and GlobalTheory.T.gridTopVertexFormFunction_continuous_left_invariant).and c3).and c4).and GlobalTheory.T.unfoldingJointData_jointlySmoothTheta_evenIndex).and GlobalTheory.T.rowTest_flippedFiniteTensor_row_isThetaFunction).and GlobalTheory.T.rowTest_heisenberg_combinations_joint_row_good).and GlobalTheory.T.rowTest_exists_combinations_of_expansion)
  refine GlobalTheory.RowReal.big_mono (fun ch h => ?_) hall
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5a⟩, h5b⟩, h6⟩, h7⟩
  refine ⟨fun a => ⟨(h1 a).2, (h1 a).1⟩, fun t y => ⟨(h2 t y).2, (h2 t y).1⟩, h3, h4, ?_, h6, h7⟩
  intro t Φ τ hτ M hM d hd P hh
  exact ⟨fun j hj hjm => h5a t Φ τ hτ M hM d hd P hh j hj hjm, h5b t Φ τ hτ d hd⟩

end GlobalTheory.RowBasic
