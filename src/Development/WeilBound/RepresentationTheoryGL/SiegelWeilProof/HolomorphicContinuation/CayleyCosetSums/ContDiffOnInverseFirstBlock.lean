module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

private theorem deriv_comp_mul_exp_smul_eq_fderiv (F : M2 n → ℂ) (x W : M2 n) (hF : DifferentiableAt ℂ F x) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) 0 = fderiv ℂ F x (x * W) := by
  have hL : HasDerivAt (fun t : ℝ => x * II.cE W t) (x * W) 0 := by
    let L : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 W)
  have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp [II.cE])
  have he : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) = fun t => F (x * II.cE W t) := by
    funext t
    simp only [II.cE, Complex.coe_smul]
  rw [he]
  exact h.deriv

theorem rC_eq (F : M2 n → ℂ) (x Z : M2 n) (hF : DifferentiableAt ℂ F x) : rC Z F x = fderiv ℂ F x (x * Z) := by
  unfold rC
  rw [deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _),
    ← Matrix.mul_smul, ← Matrix.mul_add, smul_smul]
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [hI, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem contDiffOn_inverse_first_block : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => ub1 x i j) {x | x.det ≠ 0} := by
  intro i j
  exact LVs.contDiffOn_inverse_first_block _ (fun x hx => isUnit_iff_ne_zero.2 hx) i j

theorem isOpen_det_ne : IsOpen {x : M2 n | x.det ≠ 0} :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
