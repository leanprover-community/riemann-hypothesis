module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.det_natAbs_le_prod_l1_norms :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
      M.det.natAbs ≤ ∏ i, ∑ k, (M i k).natAbs := by
  intro ι _ _ M
  have key : |M.det| ≤ ∏ i, ∑ k, |M i k| := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    let e : Equiv.Perm ι ↪ (ι → ι) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
    calc |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i|
        ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |M i (σ i)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod, Matrix.transpose_apply]
      _ = ∑ f ∈ (Finset.univ : Finset (Equiv.Perm ι)).map e, ∏ i, |M i (f i)| := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
      _ = ∏ i, ∑ k, |M i k| := (Fintype.prod_sum (fun i k => |M i k|)).symm
  have h2 : ((M.det.natAbs : ℕ) : ℤ) ≤ ((∏ i, ∑ k, (M i k).natAbs : ℕ) : ℤ) := by
    push_cast
    simpa [Int.natCast_natAbs] using key
  exact_mod_cast h2
