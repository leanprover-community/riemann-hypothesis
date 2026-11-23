module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.InterlacesULt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.RsParLamMinus
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.WalkEnds

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem walk : WalkStatement := by
  intro k r u v b h t P hk hpar hint hhalf hlow hstep hP
  obtain ⟨e1, e2, e3⟩ := walkEnds k r u v b t
  have hR : ∀ j, 1 ≤ j → j ≤ 2 * r + 2 → P (raisePar k r u b t j) := by
    intro j
    induction j with
    | zero => intro h1; omega
    | succ j ih =>
      intro h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h3 | h3
      · have hj : j = 0 := by omega
        subst hj
        rw [← e1]
        exact hP
      · exact raiseStep k r u v b h t P hk hpar hint hhalf hlow hstep j (by omega) (by omega)
          (ih (by omega) (by omega))
  have key : ∀ m, m ≤ k → P (walkPar k r u v b (k - m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, ← e2]
      exact hR (2 * r + 2) (by omega) le_rfl
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have heq : k - m = (k - (m + 1)) + 1 := by omega
      rw [heq] at h1
      exact lowerStep k r u v b h P hk hpar hint hhalf hlow hstep (k - (m + 1)) (by omega) h1
  have h0 := key k le_rfl
  rw [Nat.sub_self, e3] at h0
  exact h0

end ReciprocityTheory.ChartRestriction.DS.Lap
