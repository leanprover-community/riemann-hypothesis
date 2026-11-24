module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
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

@[expose] public section

namespace GlobalTheory.SumSmulAeEq

open MeasureTheory

theorem coeFn_sum_smul_ae_eq {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (c : ι → ℂ) (y : ι → Lp ℂ (2 : ENNReal) μ) (F : ι → X → ℂ)
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ (2 : ENNReal) μ) : X → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • y a) (∑ i ∈ s, c i • y i), Lp.coeFn_smul (c a) (y a),
      h a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h4, Finset.sum_insert ha, Pi.smul_apply, h3, smul_eq_mul]

end GlobalTheory.SumSmulAeEq
