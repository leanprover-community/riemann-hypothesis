module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

namespace ChartWirtingerDerivatives

open Filter Topology Set
open scoped ContDiff

noncomputable section

theorem wd_mul' (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) :
    wd n j (fun w => g w * h w) y = wd n j g y * h y + g y * wd n j h y := by
  simp only [wd, fderiv_fun_mul hg hh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem fderiv_conj' (n : ℕ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (starRingEnd ℂ) (g w)) y v = (starRingEnd ℂ) (fderiv ℝ g y v) := by
  have h : (fun w => (starRingEnd ℂ) (g w)) = Complex.conjLIE ∘ g := by
    funext w
    simp [Complex.conjLIE_apply]
  rw [h, LinearIsometryEquiv.comp_fderiv]
  simp

theorem wdb_conj' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wdb n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wd n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem wd_conj' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wdb n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_add (f := _), map_mul, Complex.conj_I, map_ofNat]
  ring

end

end ChartWirtingerDerivatives

end ReciprocityTheory.L2DbarEstimates
