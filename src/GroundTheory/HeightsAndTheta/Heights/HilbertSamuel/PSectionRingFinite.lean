module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSpanStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SectionRingFinite.proof (hL : SectionLatticeFinite.Statement) (hS : SectionSpanStep.Statement) :
    SectionRingFinite.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  classical
  obtain ⟨n₀, hn₀⟩ := hS K ι Ω y a q w hy hw hgen
  choose G hG using fun m : ℕ => _root_.AddSubgroup.isAddFG_iff.mp (hL K ι Ω y a m hy)
  set P : Finset (ℕ × Ω) :=
    (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP
  have memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P := by
    intro m g hm hg
    rw [hP, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1 := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨m, _, hx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [← hG m]
    exact AddSubgroup.subset_closure hg
  let f : Fin P.card → ℕ × Ω := fun i => (P.equivFin.symm i).1
  let T : ℕ → Set Ω := fun n =>
    {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}
  have base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n) := by
    intro n hn
    rw [← hG n, AddSubgroup.closure_le]
    intro g hg
    apply AddSubgroup.subset_closure
    refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]
  have step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n),
      s * w j ∈ AddSubgroup.closure (T (n + 1)) := by
    intro n j s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, μ, hdeg, rfl⟩ := hx
      apply AddSubgroup.subset_closure
      refine ⟨i, μ + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [← hdeg, Finset.sum_pi_single']
        simp [add_assoc]
      · have hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j := by
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Fintype.prod_eq_single j]
          · simp
          · intro k hk
            simp [hk]
        rw [hprod, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  refine ⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩
  intro n
  induction n with
  | zero => exact base 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ n₀
    · exact base _ h
    · have hn : n₀ ≤ n := by omega
      refine (hn₀ n hn).trans ?_
      rw [AddSubgroup.closure_le]
      rintro t ⟨s, hs, j, rfl⟩
      exact step n j s (ih hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
