module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.psdcone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), IsClosed (Psd L N) ∧ (∀ c : ℝ, 0 < c → ∀ k ∈ Psd L N, c • k ∈ Psd L N) ∧
    Pos L N ⊆ Psd L N ∧ (ConeExtensionAcyclic.posDual (Psd L N)).Nonempty := by
  intro L _ _ N
  have hc : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous (fun h : HS L N => mat h w i j) := by
    intro w i j
    exact (continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val))
  have htr : ∀ k ∈ Psd L N, ∀ w, 0 ≤ (mat k w).trace := by
    intro k hk w
    exact Finset.sum_nonneg fun i _ => (hk w).diag_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hP : Psd L N = ⋂ w : InfinitePlace L, ⋂ x : Fin N →₀ ℂ,
        {h : HS L N | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * mat h w i j * xj} := by
      ext h
      simp only [Psd, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hh w x
        exact (hh w).2 x
      · intro hh w
        exact ⟨mat_herm h w, hh w⟩
    rw [hP]
    refine isClosed_iInter fun w => isClosed_iInter fun x => ?_
    refine isClosed_le continuous_const ?_
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (hc w i j)).mul continuous_const
  · intro c hc k hk w
    show (mat (c • k) w).PosSemidef
    rw [mat_smul]
    exact (hk w).smul hc.le
  · intro k hk w
    exact (hk w).posSemidef
  · let f : HS L N →ₗ[ℝ] ℝ :=
      { toFun := fun h => ∑ w, ((mat h w).trace).re
        map_add' := by
          intro h k
          simp only [← Finset.sum_add_distrib, ← Complex.add_re, ← Matrix.trace_add]
          rfl
        map_smul' := by
          intro c h
          simp only [mat_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp }
    have hf : Continuous f := by
      show Continuous (fun h : HS L N => ∑ w, ((mat h w).trace).re)
      exact continuous_finsetSum _ fun w _ =>
        Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => hc w i i)
    refine ⟨⟨f, hf⟩, ?_⟩
    intro k hk hk0
    have hw : ∃ w, mat k w ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hk0 (HS_ext fun w => by rw [hne w, mat_zero])
    obtain ⟨w, hw⟩ := hw
    show 0 < ∑ w, ((mat k w).trace).re
    have hpos : 0 < ((mat k w).trace).re := by
      have h1 : 0 ≤ (mat k w).trace := htr k hk w
      have h2 : (mat k w).trace ≠ 0 := fun h0 => hw (((hk w).trace_eq_zero_iff).mp h0)
      exact (Complex.lt_def.mp (lt_of_le_of_ne h1 (Ne.symm h2))).1
    refine lt_of_lt_of_le hpos ?_
    refine Finset.single_le_sum (f := fun w => ((mat k w).trace).re) (fun v _ => ?_) (Finset.mem_univ w)
    exact (Complex.le_def.mp (htr k hk v)).1
