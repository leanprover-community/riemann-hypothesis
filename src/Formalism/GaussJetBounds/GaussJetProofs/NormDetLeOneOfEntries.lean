module

public import Formalism.GaussJetBounds.StatementD
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem oddExponentCount : JCount := by
  intro l a hl ha
  set L := Nat.log l a with hLdef
  have hsub : (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a) ⊆
      Finset.Icc (-(L : ℤ)) L := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    have h1 : j.natAbs ≤ L := Nat.le_log_of_pow_le (by omega) hj.2.2
    rcases Int.natAbs_eq j with h | h <;> omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have h2 : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [h2] at hcard
  have hL : (L : ℝ) ≤ Real.logb l a := Real.natLog_le_logb a l
  have h3 : ((((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℕ) : ℝ)
      ≤ ((2 * L + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at h3
  linarith

section DegProdSec

variable {σ κ : Type} [DecidableEq κ] (blk : σ → Option κ)

end DegProdSec

section BasisSec

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_det_le_one_of_entries {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro p _
  have hp : ‖∏ i, M (p i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => h _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;> rw [hs]
  · rw [one_smul]; exact hp
  · rw [Units.neg_smul, one_smul, norm_neg]; exact hp

lemma norm_inv_entry_le_one {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) (hd : ‖M.det‖ = 1) (i j : n) : ‖M⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hd, inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one_of_entries
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact h _ _

end BasisSec

end Formalism.DworkPowerSeriesWeights
