module

public import ReciprocityTheory.DualLattices.TensorSpan
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.HopfOrderCheck

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem vdet_le_of_span_le (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det ≤ v B'.det := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => B' x i) = fun x => B x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  have hB : B = B' * (Matrix.of fun i j => c j i).map (algebraMap R C) := by
    ext x j
    have := congrFun (hc j) x
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hd : ((Matrix.of fun i j => c j i).map (algebraMap R C)).det
      = algebraMap R C (Matrix.of fun i j => c j i).det := ((algebraMap R C).map_det _).symm
  rw [hB, Matrix.det_mul, map_mul, hd]
  exact mul_le_of_le_one_right' (hv _)

theorem hasColen_unique (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)} {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M c') : c = c' := by
  obtain ⟨B, hB, rfl⟩ := h
  obtain ⟨B', hB', rfl⟩ := h'
  exact le_antisymm (vdet_le_of_span_le v hv B B' (by rw [← hB, ← hB']))
    (vdet_le_of_span_le v hv B' B (by rw [← hB, ← hB']))

end GlobalTheory.HopfOrderCheck
