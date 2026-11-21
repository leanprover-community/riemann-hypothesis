import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.LogEightBound.ProgTwo

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions


def zPr (D : D7) : ℕ := LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK




theorem log_cond_le {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : Real.log (LevelStarExponents.condE D : ℝ) ≤
    Real.log 4 + 2 * (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x + 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) := by
  obtain ⟨hN, -, -, -, -, -, hQD, -⟩ := hS
  obtain ⟨-, -, hq, -, hd, -, -, -⟩ := hQD
  unfold Formalism.MainNotions.szTh at hq hd
  have hx1 := L.sc.one_lt_alt
  have hn0 : (0 : ℝ) < (D.R.n : ℝ) := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.pos
  have hd0 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  have hlogn : Real.log (D.R.n : ℝ) ≤ (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x := by
    have := Real.log_le_log hn0 hN.2
    unfold Formalism.MainNotions.szTh at this
    rwa [Real.log_rpow (by linarith)] at this
  have hcond : (LevelStarExponents.condE D : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
    unfold LevelStarExponents.condE; push_cast; ring
  have hQ0 : (0 : ℝ) < (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
  have hQ : Real.log (D.host.QS : ℝ) ≤ 2 * Real.log (D.R.n : ℝ) := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 := Real.log_le_log hQ0 h1
    rw [Real.log_pow] at h2
    exact_mod_cast h2
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hcond, Real.log_mul (by positivity) hd0.ne', Real.log_mul hQ0.ne' hq0.ne']
  linarith




end Formalism.MainNotions.J

end
