import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfRefinedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Module

namespace GlobalTheory.Survey.NumericBoundConstants

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem f_le_r (D : D7) : D.R.f ≤ D.R.r := by
  have h1 := D.R.f_le_k
  have h2 := D.R.two_le_m
  unfold Ranks.f Ranks.n Ranks.r
  omega


theorem row_rd (D : D7) : (D.R.f : ℝ) ^ 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  set a : ℝ := 4 * (D.R.t : ℝ) * D.R.r + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  have hq : a ≤ D.host.q := by
    have := D.host.qd_big.1.le
    rw [ha]; exact_mod_cast this
  have hd : a ≤ D.host.d := by
    have := D.host.qd_big.2.le
    rw [ha]; exact_mod_cast this
  have hs : a ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by rw [sq]; exact mul_le_mul hq hd ha0 (by positivity))
  have hfr : (D.R.f : ℝ) ≤ D.R.r := by exact_mod_cast f_le_r D
  have hm : (D.R.f : ℝ) ^ 2 ≤ a := by
    have h2 := Num.Pm.r_le_alt_alt D
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have h3 : (D.R.f : ℝ) * D.R.f ≤ (D.R.t : ℝ) * D.R.r :=
      mul_le_mul (hfr.trans h2) hfr hf0 (Nat.cast_nonneg _)
    rw [ha]
    nlinarith
  exact hm.trans (hs.trans h1)







variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}






end GlobalTheory.Survey.NumericBoundConstants
