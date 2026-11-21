import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValid
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale

section
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField

open Classical in

def BadOfBase (B : Arith.Base) (h : ℕ → B.H) (Cb : ℝ) : Prop :=
  let PR := (Finset.range ⌈B.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ))
  ∑ p ∈ PR, Real.log p / p *
      ((B.TT.filter (fun t => ¬ Arith.Loc.Good B (h p) (Arith.bsH (Arith.Loc.stepP B (h p) p) t))).card : ℝ) ≤
    4 * (Cb * B.sc.x ^ (-2 : ℝ)) * B.sc.delta1 * B.R.n * ∑ p ∈ PR, Real.log p / p

theorem badOK_iff_badOfBase {R : Ranks} (s : Scale) (Cb : ℝ) (H : Host R) :
    BadOK s Cb H ↔ BadOfBase (baseOf s 0 0 H) (hPH H) Cb := Iff.rfl

theorem chBad_iff_badOfBase {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (hX : ∀ h t, X.bs h t = Arith.bsH h t) (Cb : ℝ) :
    ChBad_at X Cb ↔ BadOfBase (baseOf L.sc 0 0 D.host) (G.hP D) Cb := by
  have hb : X.bs = fun h t => Arith.bsH h t := funext fun h => funext fun t => hX h t
  unfold ChBad_at badTops
  obtain ⟨bs, h1, h2, off, h3, h4, h5, kap, ep⟩ := X
  dsimp only at hb
  subst hb
  exact Iff.rfl

theorem badOfBase_of_host {R R' : Ranks} (hR : R' = R) (s : Scale) (H : Host R) (H' : Host R')
    (h : ℕ → R.A) (h' : ℕ → R'.A) (Cb : ℝ)
    (hT : H'.TT.image Formalism.HC.Frame.A.val = H.TT.image Formalism.HC.Frame.A.val) (hq : H'.q = H.q) (hd : H'.d = H.d)
    (hc : H'.cls = H.cls)
    (hh : ∀ l, (h' l).val = (h l).val) (hb : BadOfBase (baseOf s 0 0 H) h Cb) :
    BadOfBase (baseOf s 0 0 H') h' Cb := by
  subst hR
  have hT' : H'.TT = H.TT := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hT
  have hh' : h' = h := funext fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  subst hh'
  unfold baseOf at hb ⊢
  rw [hT', hq, hd, hc]
  exact hb

theorem chBad_of_from : ∀ (C : FC) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ)
    (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ) (Cb : ℝ),
    p.From H a b c u0 → CanonInst p.ta.Gx → BadOK p.L.sc Cb H → ChBad_at p.ta.Gx Cb := by
  intro C p R H a b M c u0 Cb hF hC hB
  have hc := hF.cls_eq
  obtain ⟨hR, hT, -, hq, hd, -, -, -, -, -, hh, -⟩ := hF
  exact (chBad_iff_badOfBase _ hC.1 Cb).2
    (badOfBase_of_host hR p.L.sc H p.D.host (hPH H) (G.hP p.D) Cb hT hq hd hc hh ((badOK_iff_badOfBase _ _ _).1 hB))

end GlobalTheory.EX

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bad_character_bound : ∀ (C : FC) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ) (Cb : ℝ), p.From H a b c u0 → CanonInst p.ta.Gx → BadOK p.L.sc Cb H → ChBad_at p.ta.Gx Cb := by
  first | exact @GlobalTheory.EX.chBad_of_from | exact GlobalTheory.EX.chBad_of_from | (intros; apply GlobalTheory.EX.chBad_of_from <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_requirement_of_valid : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  first | exact @GlobalTheory.EX.wreq_of_wok | exact GlobalTheory.EX.wreq_of_wok | (intros; apply GlobalTheory.EX.wreq_of_wok <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem small_prime_lt (eps C8 : ℝ) (he : 0 < eps) (h8 : 1 ≤ C8) : ∃ x0 : ℝ, ∀ (s : Scale) (N q0 : ℝ), s.eps = eps → x0 ≤ s.x →
    0 < N → Real.log N ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 → q0 ≤ N ^ C8 → q0 < s.X' := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.scale_poly_comparison eps (2 * C8) (1 / 2) he (by norm_num)
  refine ⟨x0, fun s N q0 hs hx hN hlog hq => ?_⟩
  have h := (hx0 s hs hx).2.2.2.2.2.2
  have hx1 := s.one_lt_alt
  have h1 : 1 ≤ s.x ^ (2 * C8) := Real.one_le_rpow hx1.le (by linarith)
  have hX : 1 < s.X' := Real.one_lt_exp_iff.2 (Real.rpow_pos_of_pos (by linarith) _)
  have h2 : s.X' ^ (1 / 2 : ℝ) < s.X' := by
    calc s.X' ^ (1 / 2 : ℝ) < s.X' ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
      _ = s.X' := Real.rpow_one _
  have h3 : N ^ C8 ≤ Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ C8)
    linarith
  have h4 : Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
      Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ (2 * C8) :=
    le_mul_of_one_le_right (Real.exp_pos _).le h1
  linarith

theorem X'_le_b (s : Scale) : s.X' ≤ s.b := by
  have := s.eps_pos
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith))


end GlobalTheory.EX
end
