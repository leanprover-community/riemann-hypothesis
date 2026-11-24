module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajXZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem orthonormalChartNormControl_holds : OrthonormalChartNormControl (E := E) := by
  intro r X x hx ho ρ hρ0 hρ1
  refine ⟨fun Z hZ => ⟨OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_le_of_lt hZ (by linarith)),
    fun la w hw => OrthonormalChartBounds.nfac_xZ (X := X) hx ho hρ0 hρ1 hZ la w hw,
    fun τ v => OrthonormalChartBounds.maj_xZ (X := X) hx ho hρ0 hρ1 hZ τ v⟩, ?_⟩
  intro G hG

  have hd : Differentiable ℂ (fun Z : X.Coord => X.xZ x Z) := by
    refine differentiable_pi.mpr fun τ => ?_
    refine differentiable_pi.mpr fun a => ?_
    refine differentiable_pi.mpr fun b => ?_
    simp only [Data.xZ, Matrix.mul_apply, Data.lowBlock, Matrix.of_apply]
    have hsum : ∀ {f : Fin r → X.Coord → ℂ}, (∀ j, Differentiable ℂ (f j)) →
        Differentiable ℂ (fun Z => ∑ j, f j Z) := by
      intro f hf
      first
        | exact Differentiable.fun_sum fun j _ => hf j
    refine hsum fun k => ?_
    refine Differentiable.const_mul ?_ _
    refine (differentiable_const _).add ?_
    by_cases h : X.p0 ≤ (k : ℕ) ∧ (b : ℕ) < X.p0
    · simp only [dif_pos h]
      first
        | fun_prop
    · simp only [dif_neg h]
      exact differentiable_const _
  refine hG.comp hd.differentiableOn ?_
  intro Z hZ
  exact OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_lt_of_le hZ (by linarith))

end ReciprocityTheory.ChartRestriction.G.FD
