module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsPowerMulUnitNorm
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar

@[expose] public section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable (l : ℕ) [Fact l.Prime]

theorem kur_val {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (l : ℝ) ^ m := by
  obtain ⟨y, hy, hd⟩ := kur_approx l hx ‖x‖ (norm_pos_iff.2 h0)
  have h2 : ‖x‖ = ‖y‖ :=
    norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hd (le_max_left _ _))
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    exact h0 (norm_eq_zero.1 h2)
  obtain ⟨m, a, -, b, -, ha, hb, e⟩ := kmu_shape l hy hy0
  refine ⟨-m, ?_⟩
  rw [h2, e, norm_mul, norm_div, ha, hb, div_one, mul_one, norm_zpow, norm_l_Cl, inv_zpow, zpow_neg]

end ReciprocityTheory.ChartRestriction.L1
