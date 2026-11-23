module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.LocalHensel

theorem stHensel_holds : StHensel := by
  intro L _ _ _ s hs c d hsc hsd hc hd
  obtain ⟨-, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have hXc : IsClosed {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    (isClosed_eq hcont continuous_id).inter (isClosed_le continuous_norm continuous_const)
  haveI : CompleteSpace {u : L | s u = u ∧ ‖u‖ ≤ 1} := hXc.completeSpace_coe
  haveI : Nonempty {u : L | s u = u ∧ ‖u‖ ≤ 1} := ⟨⟨0, map_zero s, by simp⟩⟩
  have hmaps : ∀ u : L, s u = u ∧ ‖u‖ ≤ 1 → s (-d - c * u ^ 2) = -d - c * u ^ 2 ∧
      ‖-d - c * u ^ 2‖ ≤ 1 := by
    rintro u ⟨hu, hu1⟩
    refine ⟨by simp only [map_sub, map_neg, map_mul, map_pow, hu, hsc, hsd], ?_⟩
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simpa using hd) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h2 : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    exact mul_le_one₀ hc.le (by positivity) h2
  let F : {u : L | s u = u ∧ ‖u‖ ≤ 1} → {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    fun u => ⟨-d - c * (u : L) ^ 2, hmaps u u.2⟩
  have hF : ContractingWith ‖c‖₊ F := by
    refine ⟨by exact_mod_cast hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hxy : ‖(x : L) + y‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le x.2.2 y.2.2)
    have key : (-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)
        = -(c * (((x : L) + y) * ((x : L) - y))) := by ring
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖(-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)‖ ≤ _
    rw [key, norm_neg, norm_mul, norm_mul, coe_nnnorm]
    have h0 : 0 ≤ ‖(x : L) - y‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left h0 hxy) (norm_nonneg _)
  have hfix := hF.fixedPoint_isFixedPt
  set u := ContractingWith.fixedPoint F hF with hu
  have hval : -d - c * (u : L) ^ 2 = u := congrArg Subtype.val hfix
  refine ⟨u, u.2.1, u.2.2, ?_⟩
  linear_combination -hval

end GlobalTheory.CompanionTheory.LocalHensel
