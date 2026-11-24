module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin

theorem foldr_iterate_of_kills {A ι : Type} [Zero A] (ds : ι → A → A) (α : ι → ℕ) (c : A)
    (hc : ∀ i, ds i c = 0) (h0 : ∀ i, ds i 0 = 0) (l : List ι) :
    ((∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = c) ∧
    (¬ (∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = 0) := by
  induction l with
  | nil => exact ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩
  | cons j l ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [List.foldr_cons, h j (by simp), ih.1 (fun i hi => h i (by simp [hi]))]
      rfl
    · rw [List.foldr_cons]
      by_cases hl : ∀ i ∈ l, α i = 0
      · rw [ih.1 hl]
        have hj : α j ≠ 0 := by
          intro hj
          apply h
          intro i hi
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hj
          · exact hl i hi
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [hk, Function.iterate_succ_apply, hc j]
        exact Function.iterate_fixed (h0 j) k
      · rw [ih.2 hl]
        exact Function.iterate_fixed (h0 j) _

theorem taylor_const :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  intro A B _ _ _ n ev ds c hc
  ext α
  rw [MvPowerSeries.coeff_C]
  change (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) α c) = _
  split_ifs with h
  · subst h
    rw [iterOp_zero]
    simp
  · have : iterOp (fun i => ⇑(ds i)) α c = 0 := by
      refine (foldr_iterate_of_kills (fun i => ⇑(ds i)) α c hc (fun i => map_zero _) _).2 ?_
      intro h'
      apply h
      ext i
      exact h' i (List.mem_finRange i)
    rw [this, map_zero, smul_zero]

end GlobalTheory.FormalOrigin
