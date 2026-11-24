module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem PhiMod.exists_X_pow_smul_eq_l_pow_smul (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)
    (n : ℕ) : ∀ w ∈ P.MM, ∃ w' ∈ P.MM,
      (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  intro w hw
  have hl0 := l_ne_zero (K := K) l
  have hlp := (Fact.out : l.Prime).pos
  have hm : monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹) ∈ S O K e := by
    refine monomial_mem_S ?_
    rw [norm_inv, norm_pow, inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _), wS,
      Nat.mul_div_cancel_left _ (NeZero.pos e)]
    refine (norm_factorial_le l _).trans (le_of_eq ?_)
    rw [pow_succ, Nat.mul_div_cancel _ hlp]
  refine ⟨_, P.MM.smul_mem ⟨_, hm⟩ hw, ?_⟩
  change _ = (l : K) ^ (l ^ n) • ((monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹)) • w)
  rw [← smul_assoc, monomial_eq_C_mul_X_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
