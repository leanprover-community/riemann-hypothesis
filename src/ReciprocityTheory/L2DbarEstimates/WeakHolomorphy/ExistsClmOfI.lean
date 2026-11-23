module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffStatement
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open Metric Set Filter Topology Complex
open scoped ContDiff

theorem exists_clm_of_I {n : ℕ} (A : V n →L[ℝ] ℂ) (hA : ∀ w : V n, A (I • w) = I * A w) :
    ∃ g' : V n →L[ℂ] ℂ, g'.restrictScalars ℝ = A := by
  refine ⟨{ toFun := A, map_add' := A.map_add, map_smul' := fun c w => ?_, cont := A.continuous }, ?_⟩
  · simp only [RingHom.id_apply, smul_eq_mul]
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
      A.map_add, A.map_smul, A.map_smul, hA]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [Complex.real_smul]
    ring
  · exact ContinuousLinearMap.ext fun w => rfl

theorem holoDeriv : HoloDerivStatement := by
  intro n Ω f hΩ hf v x hx
  have hs : ContDiffOn ℝ ∞ f Ω := holoSmooth n Ω f hΩ hf
  have hxn : Ω ∈ 𝓝 x := hΩ.mem_nhds hx
  have hloc : ∀ᶠ y in 𝓝 x, ∀ u : V n, fderiv ℝ f y u = fderiv ℂ f y u := by
    filter_upwards [hxn] with y hy u
    rw [((hf y hy).differentiableAt (hΩ.mem_nhds hy)).fderiv_restrictScalars ℝ]
    rfl
  have hD2 : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hs).2.contDiffAt hxn
  have hDd : DifferentiableAt ℝ (fderiv ℝ f) x := hD2.differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    ((contDiffOn_infty.1 hs 2).contDiffAt hxn).isSymmSndFDerivAt (by simp)
  have hder : ∀ u : V n, HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) x := by
    intro u
    simpa using hDd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have hI : ∀ w : V n, fderiv ℝ (fderiv ℝ f) x v (I • w) = I * fderiv ℝ (fderiv ℝ f) x v w := by
    intro w
    have hev : (fun y => fderiv ℝ f y (I • w)) =ᶠ[𝓝 x] fun y => I * fderiv ℝ f y w := by
      filter_upwards [hloc] with y hy
      rw [hy, hy, map_smul, smul_eq_mul]
    have h2 : HasFDerivAt (fun y => I * fderiv ℝ f y w) (I • (fderiv ℝ (fderiv ℝ f) x).flip w) x :=
      (hder w).const_mul I
    have h3 := ((hder (I • w)).congr_of_eventuallyEq hev.symm).unique h2
    have h4 := congrArg (fun L : V n →L[ℝ] ℂ => L v) h3
    simpa using h4
  have hA : ∀ w : V n, (fderiv ℝ (fderiv ℝ f) x).flip v (I • w) =
      I * (fderiv ℝ (fderiv ℝ f) x).flip v w := by
    intro w
    simp only [ContinuousLinearMap.flip_apply]
    rw [hsymm (I • w) v, hI w, hsymm w v]
  obtain ⟨gC, hgC⟩ := exists_clm_of_I _ hA
  have hev2 : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x] fun y => fderiv ℝ f y v := by
    filter_upwards [hloc] with y hy
    exact (hy v).symm
  exact ((hasFDerivAt_of_restrictScalars ℝ (hder v) hgC).congr_of_eventuallyEq hev2).differentiableAt.differentiableWithinAt

end ReciprocityTheory.L2DbarEstimates.C
