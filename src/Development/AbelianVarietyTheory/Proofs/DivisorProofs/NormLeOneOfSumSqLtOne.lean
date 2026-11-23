module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.NormBoundSumSquares

theorem norm_le_one_of_sum_sq_lt_one :
    (let d1 : {E : Type} → [inst : Field E] → [NumberField E] → {a : ℕ} → GlobalTheory.CuspRep.Lie E a → ℝ := @(fun {E : Type} [Field E] [NumberField E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a) ↦ ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ)); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a), d1 x < (1 : ℝ) → ‖x‖ ≤ (1 : ℝ)) := by
  intro d1 E _ _ _ a x hx
  have hsum : ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ) < 1 := hx
  have entry : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E), ‖x i j w‖ ≤ 1 := by
    intro i j w
    by_contra hcon
    have hgt : 1 < ‖x i j w‖ := lt_of_not_ge hcon
    have hsq : 1 < ‖x i j w‖ ^ (2 : ℕ) := one_lt_pow₀ hgt (by norm_num)
    have h₃ : ‖x i j w‖ ^ (2 : ℕ) ≤ ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun j' => ‖x i j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h₂ : ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ)
        ≤ ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h₁ : ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ)
        ≤ ∑ w' : NumberField.InfinitePlace E, ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun w' => ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ w)
    linarith
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => entry i j w

end GlobalTheory.NormBoundSumSquares
