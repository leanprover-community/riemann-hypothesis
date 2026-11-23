module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.CasBasis

theorem unitE_apply_eq_zero_of_sign {n : ℕ} {ε : Fin n → Bool} {i j a b : Fin n}
    (h : (ε i = ε j) ≠ (ε a = ε b)) : unitE i j a b = 0 := by
  rw [unitE, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

theorem kList_entry_zero {n : ℕ} {ε : Fin n → Bool} {X : Mx n} (hX : X ∈ kList ε) {a b : Fin n}
    (hab : ε a ≠ ε b) : X a b = 0 := by
  unfold kList at hX
  rcases List.mem_append.1 hX with h | h
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
    have h1 : unitE c c a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab])
    simp only [Matrix.smul_apply, h1, smul_zero]
  · obtain ⟨p, hp, hX⟩ := List.mem_flatMap.1 h
    have hpe : ε p.1 = ε p.2 := by
      have := (List.mem_filter.1 hp).2
      simp at this
      exact this.2
    have h1 : unitE p.1 p.2 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    have h2 : unitE p.2 p.1 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem pList_entry_zero {n : ℕ} {ε : Fin n → Bool} {Y : Mx n} (hY : Y ∈ pList ε) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  unfold pList at hY
  obtain ⟨p, hp, hY⟩ := List.mem_flatMap.1 hY
  have hpe : ε p.1 ≠ ε p.2 := by
    have := (List.mem_filter.1 hp).2
    simp at this
    exact this.2
  have h1 : unitE p.1 p.2 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
  have h2 : unitE p.2 p.1 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, Ne.symm hpe])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem re_trace_kB_mul_pB : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length),
    (trace (kB ε i * pB ε b)).re = 0 := by
  intro n ε i b
  have hX : kB ε i ∈ kList ε := List.get_mem _ _
  have hY : pB ε b ∈ pList ε := List.get_mem _ _
  have : trace (kB ε i * pB ε b) = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ε a = ε c
    · rw [pList_entry_zero hY h.symm, mul_zero]
    · rw [kList_entry_zero hX h, zero_mul]
  rw [this, Complex.zero_re]

end GlobalTheory.TypeSum.CasBasis
