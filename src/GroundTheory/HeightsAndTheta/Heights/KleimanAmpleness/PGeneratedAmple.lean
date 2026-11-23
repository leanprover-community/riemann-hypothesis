module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmple
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem GeneratedAmple.proof (hCover : AmpleCover.Statement.{u, w})
    (hLocal : AmpleTwistLocal.Statement.{u, w}) : GeneratedAmple.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q
  choose n₀ hn₀ using fun (b : Fin A.m) (j : Fin (A.r + 1)) => hLocal S Ω N x H A Q b j
  let M : ℕ := Finset.univ.sup fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2
  refine ⟨A.m * M, fun c hc => hCover S Ω N x H A _ fun j I y hy => ?_⟩
  have hm := A.m_pos
  have hc' : c % A.m + A.m * (c / A.m) = c := Nat.mod_add_div c A.m
  have hM : M ≤ c / A.m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hc)
  have hn : n₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j ≤ c / A.m :=
    le_trans (Finset.le_sup (f := fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2)
      (Finset.mem_univ (⟨c % A.m, Nat.mod_lt c hm⟩, j))) hM
  have key := hn₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j (c / A.m) hn I y
  simp only [hc'] at key
  exact key hy

end

end GroundTheory.Heights₂.Heights.Kleiman
