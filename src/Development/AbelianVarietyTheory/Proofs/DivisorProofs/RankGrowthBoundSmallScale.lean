import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPrincipalisationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSection

section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

private theorem choose_succ_mul_succ_eq_mul_choose (c n : ℕ) :
    (((c + (n + 1)).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((c : ℝ) + n + 1) * (((c + n).choose n : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (c + n) n
  have h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n := by
    rw [show c + (n + 1) = c + n + 1 by ring]
    linarith
  exact_mod_cast h'

theorem choose_add_le_pow_mul_choose_add (a b : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (a : ℝ) ≤ b + y * (b + 1)) (n : ℕ) :
    (((a + n).choose n : ℕ) : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA := choose_succ_mul_succ_eq_mul_choose a n
    have hB := choose_succ_mul_succ_eq_mul_choose b n
    have hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hCb : (0 : ℝ) ≤ (((b + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1) := by
      nlinarith [mul_nonneg hy hn]
    have hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have hpow : (0 : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) :=
      mul_nonneg (pow_nonneg (by linarith) n) hCb
    rw [← mul_le_mul_iff_of_pos_right hpos]
    rw [hA, mul_assoc, hB]
    calc ((a : ℝ) + n + 1) * (((a + n).choose n : ℕ) : ℝ)
        ≤ ((1 + y) * ((b : ℝ) + n + 1)) * ((1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)) :=
          mul_le_mul hlin ih hCa hfac
      _ = (1 + y) ^ (n + 1) * (((b : ℝ) + n + 1) * (((b + n).choose n : ℕ) : ℝ)) := by ring

theorem exp_le_one_add_of_le_tenth (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10) :
    Real.exp x ≤ 1 + 53 / 50 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.mp hb).2
  rw [abs_of_nonneg h0] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have hx2 : x ^ 2 ≤ x / 10 := by nlinarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith
  nlinarith

theorem choose_rank_ratio_le :
    ∀ (D T a : ℕ) (ρ : ℝ), 2 ≤ D → 20 * D ≤ T → 0 ≤ ρ → ρ ≤ 1 / 4 → (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ 1 / 10 → (((a + D).choose D : ℕ) : ℝ) ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) := by
  intro D T a ρ hD hT hρ0 hρ1 ha hε
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hT' : (20 : ℝ) * D ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hbD : (T - 1 - D) + D = T - 1 := by omega
  have hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D := by
    have h3 : (T - 1 - D) + D + 1 = T := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast at h
    linarith
  have hρ' : 0 < 1 - ρ := by linarith
  have hTD : 0 < (T : ℝ) - D := by linarith
  have hden : 0 < (1 - ρ) * ((T : ℝ) - D) := mul_pos hρ' hTD
  have hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T := by nlinarith [mul_nonneg hρ0 hTpos.le]
  have hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := div_nonneg hnum0 hden.le
  have hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)
      = (2 * D + 5 + ρ * T) / (1 - ρ) := by
    rw [hbR]
    field_simp
    ring
  have hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ)
      + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) := by
    rw [hyb, hbR]
    have key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ) := by
      rw [div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']
      nlinarith [mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]
    linarith
  have h1 := choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D
  rw [hbD] at h1
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))
      = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by ring
  have hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by
    rw [← hDy]; exact mul_nonneg (Nat.cast_nonneg _) hy0
  have hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) := by
    rw [← hDy, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D
  have hexp := exp_le_one_add_of_le_tenth _ hε0 hε
  have hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]
  have hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) := mul_nonneg (Nat.cast_nonneg _) hnum0
  have h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))
      ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) :=
    div_le_div_of_nonneg_left hnum (by positivity) hu
  have e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)
      = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ) := by
    field_simp
  have e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hTpos.le
  have e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T) := by ring
  have hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T := by positivity
  have hdr : (0 : ℝ) ≤ (D : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
  have hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ) := by
    rw [e3]
    nlinarith
  calc (((a + D).choose D : ℕ) : ℝ)
      ≤ (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D * (((T - 1).choose D : ℕ) : ℝ) := h1
    _ ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hfin hC

end GlobalTheory
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.HodgeSteps

theorem exists_jet_order (d T : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hT : 1000 * (d : ℝ) ^ 2 ≤ T) (h0 : 0 ≤ ρ)
    (hz : 7 * ((d : ℝ) ^ 2 / T + d * ρ) ≤ 1 / 2) :
    ∃ a : ℕ, ((T + d + 4 : ℕ) : ℝ) < (a + 1) * (1 - ρ) ∧
      (((a + d).choose d : ℕ) : ℝ) ≤ (1 + 7 * ((d : ℝ) ^ 2 / T + d * ρ)) * (((T - 1).choose d : ℕ) : ℝ) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hTd : 2000 * (d : ℝ) ≤ T := by nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : 0 ≤ (d : ℝ) ^ 2 / T := by positivity
  have h2 : (d : ℝ) * ρ ≤ 1 / 14 := by linarith
  have h3 : ρ ≤ 1 / 28 := by nlinarith
  have h4 : 0 < 1 - ρ := by linarith
  refine ⟨⌊((T : ℝ) + d + 4) / (1 - ρ)⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (((T : ℝ) + d + 4) / (1 - ρ))
    rw [div_lt_iff₀ h4] at this
    push_cast
    exact this
  · refine (GlobalTheory.choose_rank_ratio_le d T _ ρ hd (by exact_mod_cast (by linarith : 20 * (d : ℝ) ≤ T)) h0 (by linarith)
      (Nat.floor_le (by positivity)) ?_).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    · rw [div_le_iff₀ (mul_pos h4 (by linarith))]
      have a1 : (d : ℝ) * ρ * T ≤ 1 / 14 * T := mul_le_mul_of_nonneg_right h2 hT0.le
      have a2 : 27 / 28 * (1999 / 2000 * (T : ℝ)) ≤ (1 - ρ) * (T - d) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) h4.le
      nlinarith
    · have : 0 ≤ (d : ℝ) * ρ := by positivity
      rw [mul_div_assoc]
      linarith

theorem goodAt_shiftG (hP : Hypotheses2) (D : D7) (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (Y : Deep T.toCore j) (e : ℕ)
    (o : ℝ) (hY : Y.Good e o) (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict) (hl : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q)
    (hF : GlobalTheory.FlatLine.FlatExists Y.U (xiR D)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ) (hn : Even n)
    (h : Y.GoodAt (wtOf _ (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) 0)) : Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  obtain ⟨m, rfl⟩ := hn
  have h1 := (((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U _ Y.dict hC hY.geo hpq hl hF
    (GlobalTheory.T.unramified_points_deep_level hP D T j Y e o hL hj hY) (anchor (T.Q.Dw j) a (m + m) kc) m).2 _ 0).2 h).1
  have e1 : uWt (T.Q.Dw j) a (m + m) kc + s • hodgeWt (T.Q.Dw j) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a (m + m) kc) =
      laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j) := by
    rw [add_right_comm, uWt_add_anchor]
  rw [e1, add_comm (0 : ℤ), AllWt.wtOf_add] at h1
  have e2 : exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      exZ (T.Q.Dw j) (shiftG (T.Q.Dw j) a (m + m) s) := by
    rw [shiftG, FlatTw.exZ_add_eq, FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) m
    rw [AllWt.exOf] at this
    rw [laOf, show (m + m) / 2 = m by omega, this, wtZ]
    push_cast
    rw [two_mul]
  have e3 : cuspW Y.d.Xo₂ Y.d.c₂ Y.U
      (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      cuspW Y.d.Xo₂ Y.d.c₂ Y.U (shiftG (T.Q.Dw j) a (m + m) s) := by
    ext f
    rw [AllWt.mem_cuspW, AllWt.mem_cuspW, e2]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by
      rw [AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) e2]
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C : Set C) = ⊤) →
      (AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C' : Set C') = ⊤ := by
    rintro C _ rfl h
    exact h
  exact ⟨hasGram_nrm_of_good D _ j Y e o hY _, key _ _ e3 h1.2⟩

theorem le_gap_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (u : AllWt.Weight Dw) (τ : Psi H) (hu : Antitone (u τ)) (t : ℤ) :
    t ≤ gap (u τ + t • hodgeWt Dw τ) (Dw.p - 1) := by
  have h := hu (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1 + 1, by omega⟩ from Nat.le_succ _)
  rw [gap, dif_pos (by omega)]
  simp only [hodgeWt, CompHt.barWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [if_pos (by omega), if_neg (by omega)]
  linarith

theorem bir_gap_le (d N : ℕ) (hd : 3 ≤ d) : (d + 3) ^ 2 + 2 * N ≤ (d + 3) * ((d + 1).choose 2 + 4 * N + d + 3) := by
  nlinarith [Nat.zero_le ((d + 1).choose 2), Nat.zero_le N]

theorem rk_le : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hX hP hSi hTo hG hQ hN hDG hS hFD hDeg hSh
  refine ((((((((((hDG.and hS).and hFD).and hDeg).and hSh).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and (GlobalTheory.T.size_bounds_for_family hS)).and
    (GlobalTheory.T.valuation_multiplicity_weight hP hG hQ hSi hTo hN hDG hS hFD)).and (GlobalTheory.T.flat_line_c1_log_bound hFD)).and wtBig_run).and WtShape.wtN).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, -, a1⟩, A, -, a2⟩, _, -, a3⟩, _, -, a4⟩, _, -, a5⟩, _, -, a6⟩, _, -, a7⟩, _, -, a8⟩, _, -, a9⟩,
    _, -, a10⟩, _, -, a11⟩ := h
  obtain ⟨x0, h⟩ := (((((((((a1.and a2).and a3).and a4).and a5).and a6).and a7).and a8).and a9).and a10).and a11
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY s hs1 hs2 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩ := h x hx hle ι p hp
  clear h a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  obtain ⟨-, g1, -, -, -, hfin, -, -⟩ := b1 i hi Y hY
  obtain ⟨hb1, -, -, -, -, hbk, hq⟩ := b2 i
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨-, hρ0, hρ1, -⟩ := hq u1 hu
  obtain ⟨δ, hδ, hdg⟩ := b4 i hi Y hY u1 hu
  have hsh := b5 i hi Y hY u1 hu
  obtain ⟨hp1, hq1, hf, hu1, hA, -, hanti⟩ := b6 i hi
  obtain ⟨hL, hj, hL1, -, -, -, -, -, hf8, hr100, -, -, hPP, -, hz1, hz2, -⟩ := b7 i hi Y hY
  have hval := b8 i hi Y hY
  obtain ⟨hC, hl, hF, -⟩ := b9 i hi Y hY
  have hgap := (b10 i hi).gaps
  have hdom := (b11 i).dom
  have hfl := b3 i hi Y hY
  clear b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 hq
  rw [← hu1 u1 hu] at hA hanti hz1 hz2 hval hgap
  clear hu1
  generalize (Fm.parT x hx ι).PP = PP at *
  rw [← CompHS.dimFlag_eq] at hgap
  have hd3 : 3 ≤ CompHt.dimFlag (dat p i) := by
    rw [CompHS.dimFlag_eq, FlagTan.dimFlag]
    exact le_trans hf (Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega)))

  have hPP100 : 100 ≤ PP := by
    refine le_trans ?_ hPP
    have c1 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have c2 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c3 : (8 * 100 * 1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      gcongr
    exact le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
  have hT : 1000 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ lenT p i PP := by
    refine le_trans ?_ (Nat.le_ceil _)
    have c1 := (Fm.D x ι).R.two_le_m
    have c2 := (Fm.D x ι).R.m_add_three_le_k
    have c3 : (0 : ℝ) < (Fm.D x ι).R.m := by exact_mod_cast (by omega : 0 < (Fm.D x ι).R.m)
    have c4 : ((Fm.D x ι).R.m : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : (Fm.D x ι).R.m ≤ (Fm.D x ι).R.k)
    have c5 : 1000 ≤ PP ^ 2 := by nlinarith
    rw [le_div_iff₀ c3]
    gcongr
  obtain ⟨a, ha1, ha2⟩ := exists_jet_order _ _ _ (by omega) hT hρ0 hz2

  have hbir := GlobalTheory.T.weight_principalisation_bound hX hG hQ hSi (GlobalTheory.T.stronger_published_hypotheses_imply hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hY.1 u1 fun τ a b hb => by
    rw [← gap_eq _ hb]
    refine le_trans ?_ (hgap τ a (hb ▸ b.2))
    exact_mod_cast bir_gap_le _ _ hd3
  have hboth := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf (GlobalTheory.T.proportional_positive_volumes hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1).1
    (GlobalTheory.T.equal_volume_deep_level hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1) u1 (fun τ => (hA τ).1) (fun τ => (hA τ).2) hbir hval

  have hc0 : 1 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    have := (cZeroN_isLeast (Fm.D x ι) ((i : ℕ) + 1)).1.2.2
    unfold cZero
    omega
  have ew : uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) =
      fun τ => uM p i τ + (((s + 1 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ := by
    funext τ k
    simp only [uM, uW, uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have em : uW p i + (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) • hodgeWt (dat p i) = uM p i := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hl1 : ∀ τ, Antitone ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    exact (hanti (s + 1) (by omega) τ).1
  have hl2 : ∀ τ, Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + 4 : ℕ) : ℤ) • u1 τ -
      (uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    have := (hanti (s + 1) (by omega) τ).2
    rwa [if_neg (Nat.succ_ne_zero s)] at this
  have hl3 : ∀ τ, 1 ≤ gap ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) ((dat p i).p - 1) :=
    fun τ => by
      rw [ew]
      refine le_trans ?_ (le_gap_bar (dat p i) hp1 hq1 (uM p i) τ ?_ _)
      · push_cast
        nlinarith [Int.natCast_nonneg s]
      · simpa using (hanti 0 (by omega) τ).1
  have hev : Even (p.κ i).n := (p.κ i).n_even
  have g2 : Y.GoodAt (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    goodAt_shiftG hP _ p.T hL _ hj Y _ _ hY.1 (le_add_right hp1) hC hl hF _ _ ((Fm.D x ι).R.k - 1) _ hev
      (GlobalTheory.T.good_weight_antitone_gap hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hl1 hl3).1
  have htw := ((GlobalTheory.T.flat_line_rank_shift_invariant hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hfl).2 _ (p.κ i).n ((Fm.D x ι).R.k - 1) · hdom hev)
  rw [htw _ g1, htw _ g2]
  have hk : 0 < PP * kap p i := by linarith
  have hz : zed p i PP u1 ≤ min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i)) := le_min hz2 ((le_div_iff₀ hk).2 hz1)
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  first
    | have hJ := GlobalTheory.T.rank_component_weight_invariance hX hP hSi hTo hG hQ hN
    | have hJ := GlobalTheory.T.rank_component_weight_invariance hP hSi hTo hG hQ hN
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun Z _ => ?_
  have d0 : 0 < Y.dg u1 Z := hδ.trans_le (hdg Z).1
  have d1 : (1 - CompHt.rhoB (dat p i) u1) * CompHt.topDeg Y.U Z u1 ≤ Y.dg u1 Z :=
    (CompHt.delPrime_eq Y.U Z (CompHt.vdm_pos fun τ => (hA τ).1).ne').ge.trans (hboth Z Z).1
  have d2 := hJ _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 Z u1 _ _ a hgap hl1 hl2 (by
    have h1 : 0 < 1 - CompHt.rhoB (dat p i) u1 := by linarith
    refine lt_of_mul_lt_mul_left ?_ h1.le
    have e1 := mul_le_mul_of_nonneg_left d1 (Nat.cast_nonneg (lenT p i PP + CompHt.dimFlag (dat p i) + 4))
    have e2 := mul_lt_mul_of_pos_right ha1 d0
    linarith)
  calc _ ≤ _ := d2
    _ ≤ (1 + zed p i PP u1) * binT p i PP * Y.dg u1 Z := mul_le_mul_of_nonneg_right ha2 d0.le
    _ ≤ (1 + zed p i PP u1) * Y.rkC (uM p i) Z := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsh Z).1 (by linarith)
    _ ≤ _ := by
      rw [← em]
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end GlobalTheory.CovTop.HodgeSteps
end
end
