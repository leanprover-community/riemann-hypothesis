module

public import Mathlib.Analysis.CStarAlgebra.Classes
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

theorem UpperTheory.Reformulated.B.DYka1.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j : Fin n => ‖x a j‖ ^ (2 : ℕ))
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b : Fin m => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun b _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
        gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS
