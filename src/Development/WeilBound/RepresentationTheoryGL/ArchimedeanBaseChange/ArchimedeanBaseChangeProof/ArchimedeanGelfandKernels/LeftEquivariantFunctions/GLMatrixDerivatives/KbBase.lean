module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbBase

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat)

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

def entL (a b : Fin n) : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) := (entL a b).contDiff

theorem contDiffAt_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Mat n} {x : E}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun z => F z a b) x) : ContDiffAt ℝ ∞ F x :=
  contDiffAt_pi' fun a => contDiffAt_pi' fun b => h a b

theorem contDiff_det_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → Mat n)
    (h : ∀ a b, ContDiff ℝ ∞ (fun z => F z a b)) : ContDiff ℝ ∞ (fun z => (F z).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_det : ContDiff ℝ ∞ (fun y : Mat n => y.det) := contDiff_det_of id fun a b => contDiff_entry a b

theorem contDiffAt_inv {x : Mat n} (hx : x.det ≠ 0) : ContDiffAt ℝ ∞ (fun y : Mat n => y⁻¹) x := by
  refine contDiffAt_of_entries fun a b => ?_
  have e : (fun y : Mat n => y⁻¹ a b) = fun y => (y.det)⁻¹ * (y.updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  rw [e]
  refine (contDiff_det.contDiffAt.inv hx).mul (contDiff_det_of _ fun i j => ?_).contDiffAt
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry _ _

end PositivityTheory.RgBcC.LfSt.Kchain.KbBase
