module

public import Formalism.UnipotentAdelicQuotients.EllRegCut
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

lemma eF_eq_exp {d : ℕ} (ξ : E d) : eF ξ = fun y => Complex.exp (eL ξ y) := by
  funext y
  simp only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]
  ring_nf

lemma hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp

lemma eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by
  simp only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]
  simp

theorem iteratedPartialFourierChar : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring

end ZetaZeros.D.EllReg
