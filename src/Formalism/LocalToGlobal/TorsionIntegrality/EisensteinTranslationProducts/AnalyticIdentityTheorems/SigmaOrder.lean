module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F

theorem sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hlin : Differentiable ℂ (fun w : ℂ => a * w + b) :=
    (differentiable_id.const_mul a).add_const b
  have hfd : Differentiable ℂ f := (he L).comp hlin
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) (a * z + b)).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  · have h0 : f z = 0 := (hz L (a * z + b)).2 hmem
    have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
      rw [hfa.analyticOrderAt_eq_natCast]
      refine ⟨dslope f z, ?_, ?_, ?_⟩
      · have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
          (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
        exact (differentiableOn_univ.1 hon).analyticAt z
      · rw [dslope_same, hder.deriv]
        exact mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)
      · filter_upwards with w
        rw [pow_one, sub_smul_dslope, h0, sub_zero]
    rw [hord]
    rfl
  · have hne : f z ≠ 0 := fun h => hmem ((hz L (a * z + b)).1 h)
    have hord : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord]
    rfl

end Formalism.L2.Th1.F
