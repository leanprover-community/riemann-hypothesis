module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma energy_entry_sq_le {ι : Type} [Fintype ι] (x : Matrix ι ι ℂ) (i j : ι) :
    ‖x i j‖ ^ 2 ≤ (Matrix.trace (xᴴ * x)).re := by
  have h : (Matrix.trace (xᴴ * x)).re = ∑ b, ∑ a, ‖x a b‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [h]
  calc ‖x i j‖ ^ 2 ≤ ∑ a, ‖x a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ‖x a j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun b => ∑ a, ‖x a b‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

private lemma energy_trace_conj {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (d : ι → ℝ) : (Matrix.trace (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)).re = ∑ i, d i := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.trace_mul_cycle, hU', one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem entries_le_of_energy_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by
  intro ι _ _ E
  refine ⟨max (√E) (√(Fintype.card ι * Real.exp (√E))), ?_⟩
  rintro x H ⟨U, d, hU, hH, hA⟩ hE i j
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hherm : Hᴴ = H := by
    rw [hH]
    simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]
  have hHH : H * H = U * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hH]
    calc U * diagonal (fun i => (d i : ℂ)) * Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)
        = U * (diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          congr 3
          funext k
          push_cast
          ring
  have hd : ∀ k, d k ≤ √E := by
    intro k
    have h1 : ∑ k, d k ^ 2 ≤ E := by
      rw [hHH, energy_trace_conj U hU] at hE
      exact hE
    have h2 : d k ^ 2 ≤ ∑ k, d k ^ 2 :=
      Finset.single_le_sum (f := fun k => d k ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
    exact Real.le_sqrt_of_sq_le (h2.trans h1)
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le x i j).trans ?_
    rw [hA, energy_trace_conj U hU (fun i => Real.exp (d i))]
    calc ∑ k, Real.exp (d k) ≤ ∑ _k : ι, Real.exp (√E) :=
          Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (hd k)
      _ = _ := by simp
  · refine le_trans ?_ (le_max_left _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le H i j).trans ?_
    rwa [hherm]

end GlobalTheory.ClassFin
