module

public import Mathlib.RingTheory.Valuation.ValuationSubring
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

theorem UpperTheory.Reformulated.B.ValuationSubringDominantCoordinate.main.{u_1} :
    ∀ {Ω : Type} [inst : Field Ω] (W : ValuationSubring Ω) {κ : Type u_1} [Finite κ] (x : κ → Ω),
      (∃ (j : κ), x j ≠ (0 : Ω)) → ∃ (c : κ), x c ≠ (0 : Ω) ∧ ∀ (j : κ), x j / x c ∈ W := by
  intro Ω _ W κ _ x ⟨j0, hj0⟩
  have : Nonempty κ := ⟨j0⟩
  obtain ⟨c, hc⟩ := Finite.exists_max (fun j => W.valuation (x j))
  have hc0 : x c ≠ 0 := by
    intro h
    have h1 := hc j0
    simp only [h, map_zero] at h1
    exact hj0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))
  refine ⟨c, hc0, fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  have hpos : W.valuation (x c) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  exact (div_le_one₀ (zero_lt_iff.2 hpos)).2 (hc j)
