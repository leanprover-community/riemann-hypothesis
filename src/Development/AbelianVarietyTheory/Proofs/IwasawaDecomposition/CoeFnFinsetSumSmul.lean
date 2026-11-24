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

open MeasureTheory
namespace GlobalTheory.FinsetSumSmulCoe

theorem coeFn_finset_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type}
    (c : ι → ℂ) (u : ι → Lp ℂ (2 : ENNReal) μ) (s : Finset ι) :
    (((∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * (((u i : α →ₘ[μ] ℂ)) : α → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • u a) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c a) (u a), ih]
      with x h1 h2 h3
    rw [Finset.sum_insert ha]
    change (((c a • u a + ∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ)) : α → ℂ) x = _
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by
  intro α _ μ ι _ c u
  exact coeFn_finset_sum_smul c u Finset.univ

end GlobalTheory.FinsetSumSmulCoe
