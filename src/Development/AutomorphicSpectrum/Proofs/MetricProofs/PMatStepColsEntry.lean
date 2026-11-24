module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep

theorem stepCols_subset_of_le {N j : ℕ} (hj : j ≤ N) {m i b x : Fin N} (hmi : m ≤ i)
    (hb : b ∈ stepCols N j m) (hb' : b ∈ stepCols N j i) (hx : x ∈ stepCols N j m) : x ∈ stepCols N j i := by
  have h1 := m.2
  have h2 := i.2
  have h3 := b.2
  have h4 := x.2
  have h5 : (m : ℕ) ≤ i := hmi
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb' hx ⊢
  split_ifs at hb hb' hx ⊢ <;> omega

theorem pStep_reads (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) (hj : j ≤ N) :
    keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧
        ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 →
          pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  obtain ⟨⟨⟨τ, a, b⟩, hlt, hblk⟩, hsep⟩ := q
  obtain ⟨i, hk, hp, hb, ha⟩ := id hsep
  dsimp only at hk hp hb ha hlt hblk ⊢
  have hne : (pSteps j keep τ b).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩⟩
  have hm : pStep j keep τ b ∈ pSteps j keep τ b := by
    unfold pStep
    rw [dite_eq_left hne]
    exact Finset.min'_mem _ _
  have hmin : ∀ i' ∈ pSteps j keep τ b, pStep j keep τ b ≤ i' := by
    intro i' hi'
    unfold pStep
    rw [dite_eq_left hne]
    exact Finset.min'_le _ _ hi'
  obtain ⟨hmk, hmp, hmb⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨hmk, hmp, hmb, fun hx => ha (stepCols_subset_of_le hj (hmin i ?_) hmb hb hx), fun c => ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩
  · unfold pMat lowMat
    rw [dite_eq_left (⟨hlt, hblk⟩ : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))]
    unfold cExt
    rw [dite_eq_left hsep]
  · intro x hx hxb
    unfold pMat lowMat
    by_cases hc : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [dite_eq_left hc]
      unfold cExt
      refine dif_neg ?_
      rintro ⟨i', hk', hp', hb', hx'⟩
      exact hx' (stepCols_subset_of_le hj
        (hmin i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk', hp', hb'⟩)) hmb hb' hx)
    · rw [_root_.dite_eq_right hc, if_neg hxb]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep
