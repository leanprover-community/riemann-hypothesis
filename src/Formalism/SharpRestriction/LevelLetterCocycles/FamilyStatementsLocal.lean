import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller

noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

def kF (c : ℝ) : ℝ := (1 + Real.exp (-(c * Real.log 6))) / (1 - Real.exp (-(c * Real.log 6)))

theorem exp_neg_log_six_lt_one {c : ℝ} (hc : 0 < c) : Real.exp (-(c * Real.log 6)) < 1 := by
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

theorem kF_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ kF c := by
  have h := exp_neg_log_six_lt_one hc
  have h0 := Real.exp_pos (-(c * Real.log 6))
  unfold kF
  exact div_nonneg (by linarith) (by linarith)


theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]


end Formalism.MainNotions.FamilyNumericLemmas
