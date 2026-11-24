module

public import Formalism.GrowthSums.StatementG
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem summable_min_div_pow_two_mul_add_one {n : ℕ} (p : ℝ) (hp : 1 < p) (a : ℝ) (ha : 0 ≤ a)
    (cap : ZMod n → ℝ) (hcap : ∀ s, 0 ≤ cap s) (s : ZMod n) :
    Summable (fun e : ℕ => min (a / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 ≤ (p ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  have hq1 : (p ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp two_ne_zero)
  have hgeom : Summable (fun e : ℕ => a / p * ((p ^ 2)⁻¹) ^ e) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (a / p)
  refine Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (pow_nonneg hp0.le _)) (hcap _))
    (fun e => (min_le_left _ _).trans (le_of_eq ?_)) hgeom
  rw [inv_pow, ← pow_mul, pow_succ]
  field_simp

theorem cappedGainSubLE : CappedGainSubLE := by
  intro n p TT TTodd al cap de v i₀ i E hp hsub hal hcap hi hiE h1 h2 h3
  unfold gainG
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e =
      ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e :=
    (Finset.sum_sdiff hsub).symm
  have hodd : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤
      ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) := by
    refine Finset.sum_le_sum fun s hs => ?_
    refine (Finset.sum_le_sum fun e _ => h3 s hs e).trans ?_
    exact Summable.sum_le_tsum E
      (fun e _ => le_min (div_nonneg (hal s) (pow_nonneg hp0.le _)) (hcap _))
      (summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s)
  linarith

end Formalism.GrowthSums
