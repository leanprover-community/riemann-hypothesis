module

public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.helly :
    ∀ (l : ℕ) [Fact l.Prime] (x : ℕ → ℤ_[l]) (r : ℕ → ℝ), (∀ a b, ‖x a - x b‖ ≤ max (r a) (r b)) →
      ∃ s : ℤ_[l], ∀ a, ‖s - x a‖ ≤ r a := by
  intro l _ x r hx
  have hne : ∀ u : Finset ℕ,
      ((Set.univ : Set ℤ_[l]) ∩ ⋂ a ∈ u, Metric.closedBall (x a) (r a)).Nonempty := by
    intro u
    rcases u.eq_empty_or_nonempty with hu | hu
    · exact ⟨0, by simp [hu]⟩
    · obtain ⟨a0, ha0, hmin⟩ := u.exists_min_image r hu
      refine ⟨x a0, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm]
      intro a ha
      exact (hx a0 a).trans (max_le (hmin a ha) le_rfl)
  obtain ⟨s, -, hs⟩ := isCompact_univ.inter_iInter_nonempty
    (fun a => Metric.closedBall (x a) (r a)) (fun a => Metric.isClosed_closedBall) hne
  refine ⟨s, fun a => ?_⟩
  have h1 := Set.mem_iInter.1 hs a
  rw [Metric.mem_closedBall, dist_eq_norm] at h1
  exact h1
