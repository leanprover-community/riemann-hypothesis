module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jA_eq_depth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  intro D L l hl hlA
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1 : ℝ) < (l : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < LevelStarExponents.lA L := by linarith
  have key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j := by
    intro j
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]
  have hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L) := by
    rw [Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]; linarith
  have hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_Ici]; exact key j
  unfold jA depth
  rw [hset, csInf_Ici, max_eq_right hc]

end GlobalTheory.HTW.Rec
