module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

private lemma d_apply_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hf : f =ᶠ[𝓝 x] 0) : d n z j f x = 0 := by
  unfold d
  split_ifs with h
  · set e := Classical.choose h
    have he := Classical.choose_spec h
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have hc := e.continuousAt_symm (e.map_source he.2)
      rw [ContinuousAt, e.left_inv he.2] at hc
      exact hc
    have hg : (f ∘ e.symm) =ᶠ[𝓝 (e x)] fun _ => (0 : ℂ) :=
      (ht.eventually hf).mono fun y hy => by simpa using hy
    rw [hzx]
    unfold wd
    rw [hg.fderiv_eq]
    simp
  · rfl

theorem locality (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LocalityStatement n M := by
  intro z _ ph ph' ψ U f _ _ hsupp hph
  have hfz : ∀ x, x ∉ U → f x = 0 := by
    intro x hx
    by_contra h
    exact hx (hsupp (subset_tsupport _ h))
  have hfun : ∀ j, (fun y => (Real.exp (-(w2 ph' ψ y)) : ℂ) * f y j) =
      fun y => (Real.exp (-ph y) : ℂ) * f y j := by
    intro j
    funext y
    by_cases hy : y ∈ U
    · simp [w2, (hph y hy).1, (hph y hy).2]
    · simp [hfz y hy]
  refine ⟨?_, ?_⟩
  · intro v
    unfold ipV
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp [w2, (hph x hx).1, (hph x hx).2]
    · simp [hfz x hx]
  · unfold wint
    apply lintegral_congr
    intro x
    unfold tstar
    simp_rw [hfun]
    by_cases hx : x ∈ U
    · have h1 : w1 ph' ψ x = ph x := by simp [w1, (hph x hx).1, (hph x hx).2]
      rw [h1]
    · have hx' : x ∉ tsupport f := fun h => hx (hsupp h)
      have hev : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
      have hS : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0 := fun j =>
        d_apply_eq_zero_of_eventuallyEq_zero n z j _ x (hev.mono fun y hy => by simp [hy])
      rw [Finset.sum_eq_zero (fun j _ => hS j)]
      simp

end

end ReciprocityTheory.L2DbarEstimates.F
