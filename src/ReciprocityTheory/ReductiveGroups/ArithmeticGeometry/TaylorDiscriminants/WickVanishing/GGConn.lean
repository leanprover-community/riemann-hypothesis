module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConnA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma sgn_cast_eq (p0 r : ℕ) : (fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) = sv p0 := by
  funext a
  unfold sgn sv
  split_ifs <;> simp

lemma pos_conj_mul {s : ℝ} {c d : ℂ} (hc : c ≠ 0) (h : 0 < s * d.re) : 0 < s * (c * d * conj c).re := by
  have hn := Complex.normSq_pos.mpr hc
  rw [mul_comm c d, mul_assoc, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h2 : s * (d.re * Complex.normSq c) = (s * d.re) * Complex.normSq c := by ring
  rw [h2]
  exact mul_pos h hn

theorem flag_domain_frames_connected : GGConnStatement (E := E) := by
  apply GlobalTheory.frames_isConnected

end

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
