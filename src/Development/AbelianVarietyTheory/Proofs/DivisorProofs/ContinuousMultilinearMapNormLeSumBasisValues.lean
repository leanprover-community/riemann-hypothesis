module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

theorem GlobalTheory.continuousMultilinear_norm_le_basis_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  intro E _ _ ι _ b j
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖ := by
    intro x c
    have h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c := rfl
    rw [h1]
    exact (norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)
  refine ⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun r => ∑ c, b.repr (v r) c • b c := funext fun r => (b.sum_repr (v r)).symm
  have key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r)) := by
    conv_lhs => rw [hv]

    rw [M.map_sum]
    refine Finset.sum_congr rfl fun cs _ => ?_
    exact M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))
  rw [key]
  calc ‖∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖
      ≤ ∑ cs : Fin j → ι, ‖(∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖ := norm_sum_le _ _
    _ ≤ ∑ cs : Fin j → ι, (C ^ j * ∏ r, ‖v r‖) * ‖M (fun r => b (cs r))‖ := by
      refine Finset.sum_le_sum fun cs _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)
    _ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cs _ => ?_
      ring
