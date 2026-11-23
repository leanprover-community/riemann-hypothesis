module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaJ
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

theorem tf_ge_abstract {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hiso : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (HP H' : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) (hH'c : IsClosed (H' : Set (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))))
    (hH'P : H' ≤ HP) (hH'st : ∀ g, ∀ v ∈ H', ρ g v ∈ H') (hH'0 : H' ≠ ⊥)
    (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    {d' : ℝ} (hd' : 0 < d')
    (hschur : ∀ x ∈ H', ∀ v ∈ H', ∫ g, ‖inner ℂ x (ρ g v)‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖v‖ ^ 2 / d') :
    d' ≤ ∑ c, ‖w c‖ ^ 2 ∧ (∑ c, ‖w c‖ ^ 2 = d' → HP ≤ H') := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_ge_abstract <;> assumption

end ReciprocityTheory.ChartRestriction.DS.G2
