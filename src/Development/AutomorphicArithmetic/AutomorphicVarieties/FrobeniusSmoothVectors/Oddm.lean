module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.oddm :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (a g : ℕ) (G : MvPowerSeries (Fin a ⊕ Fin g) O), G ∈ wtPart O (Space.Loc.par a g) 1 → (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) G ∈ maximalIdeal O) → ∃ M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O, (∀ j, MvPowerSeries.constantCoeff (M j) ∈ maximalIdeal O) ∧ G = ∑ j, M j * MvPowerSeries.X (.inr j) := by
  classical
  intro O _ _ a g G hG hlin
  let M : Fin g → MvPowerSeries (Fin a ⊕ Fin g) O := fun j m =>
    if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
      MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0
  have hM : ∀ j m, MvPowerSeries.coeff m (M j) =
      if ∀ k : Fin g, k < j → m (Sum.inr k) = 0 then
        MvPowerSeries.coeff (m + Finsupp.single (Sum.inr j) 1) G else 0 := fun _ _ => rfl
  refine ⟨M, ?_, ?_⟩
  · intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hM]
    simpa using hlin (Sum.inr j)
  · ext n

    rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one, hM]
    by_cases hex : ∃ j : Fin g, n (Sum.inr j) ≠ 0
    · let S := Finset.univ.filter (fun j : Fin g => n (Sum.inr j) ≠ 0)
      have hS : S.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, by simp [S, hj]⟩
      have hj0 : n (Sum.inr (S.min' hS)) ≠ 0 := by
        have := S.min'_mem hS
        simpa [S] using this
      have hmin : ∀ k : Fin g, n (Sum.inr k) ≠ 0 → S.min' hS ≤ k := fun k hk =>
        S.min'_le k (by simp [S, hk])
      have hle : ∀ j : Fin g, n (Sum.inr j) ≠ 0 → Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        rw [Finsupp.single_le_iff]
        omega
      rw [Finset.sum_eq_single (S.min' hS)]
      · rw [if_pos (hle _ hj0), if_pos, tsub_add_cancel_of_le (hle _ hj0)]
        intro k hk
        by_contra hne
        have := hmin k (by simpa [Finsupp.tsub_apply, Finsupp.single_apply, ne_of_gt hk] using hne)
        exact absurd hk (not_lt.mpr this)
      · intro j _ hj
        by_cases hjl : Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n
        · rw [if_pos hjl]
          have hnj : n (Sum.inr j) ≠ 0 := by
            have := hjl (Sum.inr j)
            simp at this
            omega
          have hlt : S.min' hS < j := lt_of_le_of_ne (hmin j hnj) (Ne.symm hj)
          rw [if_neg]
          intro hall
          have := hall _ hlt
          simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm (ne_of_lt hlt)] at this
          exact hj0 this
        · rw [if_neg hjl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hex
      have hz : ∀ j : Fin g, ¬ Finsupp.single (Sum.inr j : Fin a ⊕ Fin g) 1 ≤ n := by
        intro j hj
        have := hj (Sum.inr j)
        simp [hex j] at this
      simp only [hz, if_false, Finset.sum_const_zero]
      apply hG
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero]
      · decide
      · intro i _
        rcases i with i | i
        · simp [Space.Loc.par]
        · simp [hex i]
