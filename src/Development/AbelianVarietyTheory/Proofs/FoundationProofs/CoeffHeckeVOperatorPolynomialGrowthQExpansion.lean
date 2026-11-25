module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem Vo_polyB_qs : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a →
    PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  intro l a hl ha
  refine ⟨?_, ?_⟩
  · obtain ⟨C, A, h⟩ := ha
    have hC : 0 ≤ C := by
      have := h 0
      simp at this
      exact le_trans (norm_nonneg _) this
    refine ⟨C, A, fun n => ?_⟩
    unfold Vo
    split_ifs with hd
    · refine (h (n / l)).trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self n l
    · simp only [norm_zero]; positivity
  · intro τ σ hσ
    unfold qs
    have hinj : Function.Injective (fun m : ℕ => l * m) :=
      fun x y hxy => Nat.eq_of_mul_eq_mul_left hl hxy
    have hsupp : Function.support (fun n : ℕ => Vo l a n * cexp (2 * π * Complex.I * n * τ)) ⊆
        Set.range (fun m : ℕ => l * m) := by
      intro n hn
      by_contra hr
      apply hn
      have : ¬ l ∣ n := by
        rintro ⟨m, rfl⟩
        exact hr ⟨m, rfl⟩
      simp [Vo, this]
    rw [← hinj.tsum_eq hsupp]
    congr 1
    ext m
    have hl' : l ≠ 0 := hl.ne'
    simp only [Vo, dvd_mul_right, ite_true, Nat.mul_div_cancel_left m hl, hσ]
    congr 2
    push_cast
    ring

end GlobalTheory.EisM
