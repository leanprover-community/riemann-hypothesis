module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem generic_ratio_bound : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
