module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem modA_eq_fun (P : M.Par) (ρ : M.Ty P) :
    modA P ρ = fun w => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹ := by
  funext w
  have h : (w * star w : ℂ) = (Complex.normSq w : ℂ) := Complex.mul_conj w
  rw [h]
  simp only [modA, div_eq_mul_inv]

theorem dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2 := by
  have hns : (ζ * star ζ : ℂ) = (Complex.normSq ζ : ℂ) := Complex.mul_conj ζ
  have hlt : P.TT < Complex.normSq ζ := hζ
  have hN0 : ζ * star ζ - (P.TT : ℂ) ≠ 0 := by
    rw [hns, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hlt.ne')
  have hS := (hasFDerivAt_id (𝕜 := ℝ) ζ).star
  have hN := ((hasFDerivAt_id (𝕜 := ℝ) ζ).mul hS).sub_const (P.TT : ℂ)
  have hI := ((hasDerivAt_inv hN0).hasFDerivAt.restrictScalars ℝ).comp ζ hN
  have hF := ((hasFDerivAt_const (𝕜 := ℝ) (M.aC P ρ : ℂ) ζ).mul hS).mul hI
  have hF' : HasFDerivAt (fun w : ℂ => (M.aC P ρ : ℂ) * star w * (w * star w - (P.TT : ℂ))⁻¹) _ ζ := hF
  rw [modA_eq_fun]
  simp only [NF.dZb]
  rw [hF'.fderiv]
  rw [← hns]
  simp [Complex.star_def]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem re_dZb_modA (P : M.Par) (ρ : M.Ty P) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (NF.dZb (modA P ρ) ζ).re = -(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 := by
  rw [dZb_modA P ρ hζ]
  have h : (-(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) =
      ((-(M.aC P ρ * P.TT) / (Complex.normSq ζ - P.TT) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
