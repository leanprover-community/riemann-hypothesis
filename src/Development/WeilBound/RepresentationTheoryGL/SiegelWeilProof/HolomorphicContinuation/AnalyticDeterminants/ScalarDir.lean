module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolD

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem line2 {H : E → V} {y w : E} {m : E →L[ℂ] E} (hfd : DifferentiableAt ℂ (fderiv ℂ H) y)
    (hz : ∀ t : ℝ, fderiv ℂ H (y + (t : ℂ) • w) (m (y + (t : ℂ) • w)) = 0) :
    fderiv ℂ (fderiv ℂ H) y w (m y) + fderiv ℂ H y (m w) = 0 := by
  have hψ : HasFDerivAt (fun z => fderiv ℂ H z (m z))
      ((fderiv ℂ H y).comp m + (fderiv ℂ (fderiv ℂ H) y).flip (m y)) y :=
    hfd.hasFDerivAt.clm_apply m.hasFDerivAt
  have h := GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently hψ.differentiableAt (s := w)
    (GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
      (p := fun t : ℂ => fderiv ℂ H (y + t • w) (m (y + t • w)) = fderiv ℂ H y (m y))
      (Eventually.of_forall fun t => by
        have h0 := hz 0
        simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
        rw [hz t, h0]))
  rw [hψ.fderiv] at h
  simpa [add_comm] using h

theorem scalar_dir {H : E → V} {y : E} (hd : DifferentiableAt ℂ H y)
    (h : ∀ t : ℝ, H (Complex.exp ((t : ℂ) * Complex.I) • y) = 0) : fderiv ℂ H y y = 0 := by
  have hγ := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).smul_const y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hd.hasFDerivAt.restrictScalars ℝ) hγ (by simp)
  have hc0 := hc.congr_of_eventuallyEq (f₁ := fun _ : ℝ => (0 : V)) (Eventually.of_forall fun t => (h t).symm)
  have := hc0.unique (hasDerivAt_const (0 : ℝ) (0 : V))
  simp only [ContinuousLinearMap.coe_restrictScalars', id, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, map_smul, Complex.ofReal_one] at this
  exact (smul_eq_zero.mp this).resolve_left Complex.I_ne_zero

end PositivityTheory.Rg.Sw.LVs.HolD
