import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModulesStatement
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundAtPlaceOfLatticeColengthBound
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFive
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusStatementOfFontaine
import BuildAid.ForwardExisting
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesFinal
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralStatementHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.RowBLong

theorem logb_le_self {l : ℕ} (hl : 11 ≤ l) {y : ℝ} (hy : 0 < y) : Real.logb l y ≤ y := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := Real.log_le_sub_one_of_pos hy
  unfold Real.logb
  rcases le_or_gt 0 (Real.log y) with h | h
  · calc Real.log y / Real.log l ≤ Real.log y := div_le_self h hlog
      _ ≤ y := by linarith
  · have : Real.log y / Real.log l < 0 := div_neg_of_neg_of_pos h (by linarith)
    linarith

theorem logb_le_split {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    Real.logb l H ≤ H / ((l : ℝ) - 1) ^ (j + 1) + ((j : ℝ) + 1) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := pow_pos (by linarith) _
  have hl1 : (1 : ℝ) < l := by linarith
  rcases hH.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  have hsplit : Real.logb l H = Real.logb l (H / ((l : ℝ) - 1) ^ (j + 1)) + Real.logb l (((l : ℝ) - 1) ^ (j + 1)) := by
    rw [Real.logb_div hpos.ne' hm.ne']; ring
  have h2 : Real.logb l (((l : ℝ) - 1) ^ (j + 1)) ≤ (j : ℝ) + 1 := by
    rw [Real.logb_pow]
    have h3 : Real.logb l ((l : ℝ) - 1) ≤ 1 := by
      have := Real.logb_le_logb_of_le hl1 (by linarith : (0:ℝ) < l - 1) (by linarith : (l:ℝ) - 1 ≤ l)
      rwa [Real.logb_self_eq_one hl1] at this
    push_cast
    have : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith
  rw [hsplit]
  have := logb_le_self hl (div_pos hpos hm)
  linarith

theorem bracket_le {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H G0 hB GP large₂ : ℝ} (hH0 : 0 ≤ H) (hG0 : 0 ≤ G0)
    (hGP : G0 ≤ GP) (hB0 : 0 ≤ hB) (hLg : 0 ≤ large₂) (hH : H ≤ hB ∨ H ≤ G0) :
    H / ((l : ℝ) - 1) ^ (j + 1) + (G0 + 1) * ((j : ℝ) + 1) + Real.logb l H ≤
      3 * (hB / ((l : ℝ) - 1) ^ (j + 1) + (GP + 1) * ((j : ℝ) + 1) + large₂) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm1 : 1 ≤ ((l : ℝ) - 1) ^ (j + 1) := one_le_pow₀ (by linarith)
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := by linarith
  have hlog := logb_le_split hl j hH0
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hBm : 0 ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_nonneg hB0 hm.le
  have hGj : (G0 + 1) * ((j : ℝ) + 1) ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  have hj1 : (j : ℝ) + 1 ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  rcases hH with h | h
  · have : H / ((l : ℝ) - 1) ^ (j + 1) ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_le_div_of_nonneg_right h hm.le
    nlinarith
  · have h1 : H / ((l : ℝ) - 1) ^ (j + 1) ≤ H := div_le_self hH0 hm1
    have h2 : 2 * G0 + (j : ℝ) + 1 ≤ 2 * (G0 + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

open Formalism.MainNotions.N in
theorem nLet_eq_nLam {D : D7} {L : SizeData₂ D} {HW : HWOf D.loc} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL} {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) : nLet i w hw = Formalism.MainNotions.TwistedPlaces.nLam D w := by
  have hK : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
  have h1 : nLet i w hw = Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    (IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq
  rw [h1]
  exact hb.deg

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  intro D L P HW C₂ i r ρ π dc hA hC _ h11 hJ
  intro w hw _ C hCg
  obtain ⟨hur, hWd⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hCg.good_one (by omega) (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hb, hB⟩ := hWd C hg
  have hrow := GlobalTheory.Survey.InertPlacesGoodSet.rowL_of_wordsB hA h11 hb hB
  refine GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow ?_
  have hn : ((nLet i w hw : ℕ) : ℝ) = (Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast nLet_eq_nLam hb
  have hl' : (11 : ℝ) ≤ D.nd.l i := by exact_mod_cast h11
  have hbr := bracket_le h11 (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i))
    (H := (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) (G0 := ((Wd.w + Wd.S + Wd.η : ℕ) : ℝ))
    (hB := Formalism.MainNotions.TwistedPlaces.hB L) (GP := Formalism.MainNotions.TwistedPlaces.GP L) (large₂ := Formalism.MainNotions.TwistedPlaces.large₂ L)
    (by positivity) (by positivity)
    (by
      unfold Formalism.MainNotions.TwistedPlaces.GP
      have := hb.w_le; have := hb.S_le; have := hb.η_le
      push_cast; linarith)
    (by linarith [Formalism.MainNotions.TwistedPlaces.one_le_hB L]) (Formalism.MainNotions.TwistedPlaces.Lg_nonneg L)
    (by
      unfold WachCoordinates.hCor
      split_ifs
      · left; have := hb.h_le; push_cast; linarith
      · right; exact le_rfl)
  have key : C₂ * (((nLet i w hw : ℕ) : ℝ) + 1) * D.R.r *
      ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
        (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) +
        Real.logb (D.nd.l i) (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤
      3 * C₂ * coreB L (D.nd.l i) w := by
    unfold coreB
    rw [hn]
    have h0 : 0 ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r := by
      have : (0:ℝ) ≤ C₂ := by linarith
      positivity
    calc _ ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r *
          (3 * (Formalism.MainNotions.TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
            (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
          mul_le_mul_of_nonneg_left hbr h0
      _ = _ := by ring
  unfold lenRowB ratIn
  split_ifs with hlt
  · have := (exists_rat_btwn hlt).choose_spec
    linarith [this.1]
  · push_neg at hlt
    have hc0 : coreB L (D.nd.l i) w ≤ 0 := by linarith
    have : 3 * C₂ * coreB L (D.nd.l i) w ≤ 0 := by
      have : (0:ℝ) ≤ 3 * C₂ := by linarith
      nlinarith
    simp only [Rat.cast_zero]
    linarith

end GlobalTheory.RowBLong
end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.longOrbits_rowColength_inertLocalisation : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  atlas_forward_decl GlobalTheory.RowBLong.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.RowsThick

theorem logb_le_of_log_le {l x A : ℝ} (hl : 1 ≤ Real.log l) (hx : Real.log x ≤ A) (hA : 0 ≤ A) :
    Real.logb l x ≤ A := by
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem one_le_log_of_eleven {l : ℝ} (hl : 11 ≤ l) : 1 ≤ Real.log l := by
  have h1 : Real.exp 1 ≤ l := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log l := Real.log_le_log (Real.exp_pos 1) h1

theorem colBd_le_row {l n r m S η H H' e e' hB eta₃ wP Sc large₂ flt : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m) (hS0 : 0 ≤ S) (hS : S ≤ Sc) (hη0 : 0 ≤ η)
    (hη : η ≤ eta₃) (hH0 : 0 ≤ H) (hH : H ≤ hB + eta₃) (hetaB : eta₃ ≤ hB) (hB1 : 1 ≤ hB)
    (hBb : hB ≤ 2 * Real.exp large₂) (hLg : 1 ≤ large₂) (hwP : 0 ≤ wP)
    (hflt : (wP + eta₃) / l + Sc + large₂ ≤ flt)
    (he : e ≤ 32 * H / l ^ 2 + 4 * S + 10 * η / (l - 1) + 25 * (Real.logb l (2 * H) + 1))
    (hH'0 : 0 ≤ H') (hH' : H' ≤ H)
    (he' : e' ≤ 23 * (1 + H' / l + (1 + Real.logb l (H' + 1)))) :
    (n + 1) * r * e + 4 * n * m * e' + 3 / 2 * n * (r * S + 2 * m * ((H + 1) / (l - 1) + 1)) ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) + 2082 * ((n + 1) * r * flt) +
        22365 * (n * m * (1 + hB / l + Real.logb l hB)) := by
  have hlog := one_le_log_of_eleven hl
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < l - 1 := by linarith
  have hetaP0 : 0 ≤ eta₃ := hη0.trans hη
  have hSc0 : 0 ≤ Sc := hS0.trans hS
  have hlB : 0 < Real.log l := by linarith

  have hlam : Real.logb l (2 * H) ≤ 7 + large₂ := by
    apply logb_le_of_log_le hlog _ (by linarith)
    rcases hH0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; linarith
    · have h8 : 2 * H ≤ 8 * Real.exp large₂ := by linarith
      calc Real.log (2 * H) ≤ Real.log (8 * Real.exp large₂) := Real.log_le_log (by linarith) h8
        _ = Real.log 8 + large₂ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        _ ≤ 7 + large₂ := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]

  have hlogB : 0 ≤ Real.logb l hB := Real.logb_nonneg (by linarith) hB1
  have hlamB : Real.logb l (H' + 1) ≤ 1 + Real.logb l hB := by
    have h3 : Real.log (H' + 1) ≤ Real.log l + Real.log hB := by
      calc Real.log (H' + 1) ≤ Real.log (3 * hB) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log hB := Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log l + Real.log hB := by
          have := Real.log_le_log (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≤ l by linarith)
          linarith
    unfold Real.logb
    calc Real.log (H' + 1) / Real.log l ≤ (Real.log l + Real.log hB) / Real.log l :=
          div_le_div_of_nonneg_right h3 hlB.le
      _ = 1 + Real.log hB / Real.log l := by rw [add_div, div_self hlB.ne']

  have hu0 : 0 ≤ eta₃ / l := div_nonneg hetaP0 hl0.le
  have hv0 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have hw0 : 0 ≤ wP / l := div_nonneg hwP hl0.le
  have hE0 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hHl : 32 * H / l ^ 2 ≤ 32 * (hB / l ^ 2) + 3 * (eta₃ / l) := by
    have a1 : H / l ^ 2 ≤ (hB + eta₃) / l ^ 2 := div_le_div_of_nonneg_right hH (by positivity)
    have a2 : eta₃ / l ^ 2 = (eta₃ / l) / l := by rw [div_div, sq]
    have a3 : (eta₃ / l) / l ≤ (eta₃ / l) / 11 := div_le_div_of_nonneg_left hu0 (by norm_num) hl
    have a4 := add_div hB eta₃ (l ^ 2)
    rw [mul_div_assoc]
    linarith
  have hηl : 10 * η / (l - 1) ≤ 11 * (eta₃ / l) := by
    rw [div_le_iff₀ hl1]
    have a1 : 11 * (eta₃ / l) * (l - 1) = 11 * eta₃ - 11 * (eta₃ / l) := by field_simp
    have a2 : eta₃ / l ≤ eta₃ / 11 := div_le_div_of_nonneg_left hetaP0 (by norm_num) hl
    rw [a1]; linarith
  have hwe : (wP + eta₃) / l = wP / l + eta₃ / l := add_div _ _ _
  set E1 := hB / l ^ 2 with hE1
  set M1 := 1 + hB / l + Real.logb l hB with hM1
  set cD := (H + 1) / (l - 1) + 1 with hcD
  have hflt0 : 0 ≤ flt := by linarith
  have he1 : e ≤ 32 * E1 + 225 * flt := by linarith
  have he2 : e' ≤ 69 * M1 := by
    have a1 : H' / l ≤ 2 * (hB / l) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hl0.le
    linarith
  have hcD4 : cD ≤ 4 * M1 := by
    have a1 : (H + 1) / (l - 1) ≤ 4 * (hB / l) := by
      rw [div_le_iff₀ hl1]
      have b1 : 4 * (hB / l) * (l - 1) = 4 * hB - 4 * (hB / l) := by field_simp
      have b2 : hB / l ≤ hB / 11 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hl
      rw [b1]; linarith
    rw [hcD]; linarith
  have hM0 : 0 ≤ M1 := by linarith
  have h1 : (n + 1) * r * e ≤ (n + 1) * r * (32 * E1 + 225 * flt) :=
    mul_le_mul_of_nonneg_left he1 (by positivity)
  have h2 : n * m * e' ≤ n * m * (69 * M1) := mul_le_mul_of_nonneg_left he2 (by positivity)
  have h3 : n * r * S ≤ (n + 1) * r * flt := by
    have : S ≤ flt := by linarith
    calc n * r * S ≤ n * r * flt := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (n + 1) * r * flt := by
        have q1 : (n + 1) * r * flt = n * r * flt + r * flt := by ring
        have q2 := mul_nonneg hr hflt0
        linarith
  have h4 : n * m * cD ≤ n * m * (4 * M1) := mul_le_mul_of_nonneg_left hcD4 (by positivity)
  have p1 : 0 ≤ (n + 1) * r * E1 := by positivity
  have p2 : 0 ≤ (n + 1) * r * flt := by positivity
  have p3 : 0 ≤ n * m * M1 := by positivity
  linarith

attribute [local instance] nLet_neZero

section Facts

variable {D : D7} (L : SizeData₂ D)

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem Lg_ge_one : 1 ≤ TwistedPlaces.large₂ L := by
  unfold TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem placeWeight_nonneg : 0 ≤ TwistedPlaces.wP L := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := one_le_b L
    positivity
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    positivity
  have hB : 0 ≤ TwistedPlaces.wB L := by
    unfold TwistedPlaces.wB
    have := L.etaSz_pos
    exact le_max_of_le_left (by linarith)
  unfold TwistedPlaces.wP
  positivity

theorem one_le_hB : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_le_hB : TwistedPlaces.eta₃ L ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.eta₃ TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  linarith

end Facts

theorem Hmax_le {n : ℕ} [NeZero n] (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) :
    LiftingTheory.Hmax n (RamifiedCoefficientChains.MiW d b S η) (RamifiedCoefficientChains.hiW d b S η) ≤ RamifiedCoefficientChains.hpar n b S + η := by
  unfold LiftingTheory.Hmax
  apply Finset.sup_le
  intro k _
  have : b (k : ZMod n) ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ _)
  unfold RamifiedCoefficientChains.MiW RamifiedCoefficientChains.hiW RamifiedCoefficientChains.hpar
  split_ifs <;> omega

theorem hpar_le_of_thick {n : ℕ} [NeZero n] {b0 η : ℕ} {sz : ZMod n → ℕ} (S : ℕ)
    (h : ∀ a, TruncatedSeriesCountingBounds.Thick b0 η sz a) : RamifiedCoefficientChains.hpar n sz S ≤ b0 + η + S := by
  unfold RamifiedCoefficientChains.hpar
  have : Finset.univ.sup sz ≤ b0 + η := Finset.sup_le fun a _ => (h a).2
  omega

theorem rowL_of_allThick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd d bd hP04 hP54 hPar h11 hb hbox hC hA
  intro T₁ T₂ F' h2 h1 hF
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hl' : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by rw [hp]
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setCS_of_wordsAT h11 hb hC hA T₁ T₂ F' h2 h1 hF
  obtain ⟨e, he, hcol, -⟩ :=
    hP04 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG d T₁ T₂ F' Wd.sz Wd.S Wd.η Wd.m hS trivial
  have hO := (hP54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁
    (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) hS.2.2.2.2.2.1.1
    (RamifiedCoefficientChains.jumpsLet_win _ hS)).1 hS.1
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hn : nLet i w hw = TwistedPlaces.nLam D w := by
    have h0 : Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
    unfold nLet
    rw [h0]
    exact hb.deg
  have hnR : ((nLet i w hw : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by exact_mod_cast hn
  obtain ⟨mm, k, hmm, hk, hle⟩ := hcol
  refine ⟨mm, k, hmm, hk, hle.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))⟩
  have hK : (rowC C₂).K₁ = 368 ∧ (rowC C₂).K₂ = 2082 ∧ (rowC C₂).K₃ = 22365 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃] <;> norm_num
  rw [hK.1, hK.2.1, hK.2.2]
  unfold RamifiedCoefficientChains.colBd RamifiedCoefficientChains.cD bdCD coreH coreF coreM coreE
  rw [hl', hrk, hb.m_eq, hnR]
  unfold RamifiedCoefficientChains.eBd RamifiedCoefficientChains.lam at he
  rw [hl'] at he hO
  have hHn := Hmax_le d Wd.sz Wd.S Wd.η
  have hth := hpar_le_of_thick Wd.S hA.thick
  have hHle : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ TwistedPlaces.hB L + TwistedPlaces.eta₃ L := by
    have a1 : RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η ≤ Wd.b + Wd.η + Wd.S + Wd.η := by omega
    have a2 : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ ((Wd.b + Wd.η + Wd.S + Wd.η : ℕ) : ℝ) := by
      exact_mod_cast a1
    push_cast at a2 ⊢
    linarith [hb.h_le, hb.η_le]
  have hBb : TwistedPlaces.hB L ≤ 2 * Real.exp (TwistedPlaces.large₂ L) := by
    change TwistedPlaces.hB L ≤ 2 * L.sc.b
    unfold TwistedPlaces.hB
    unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar
    linarith
  have hflt : (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / (D.nd.l i : ℝ) + L.Sc + TwistedPlaces.large₂ L ≤ flat L bd (D.nd.l i) := by
    unfold flat
    have h0 : 0 ≤ TwistedPlaces.eta₃ L := by have := L.etaSz_pos; unfold TwistedPlaces.eta₃; positivity
    split_ifs <;> linarith
  exact GlobalTheory.RowsThick.colBd_le_row (η := (Wd.η : ℝ))
    (H' := ((LiftingTheory.Hmax (nLet i w hw) (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) : ℕ) : ℝ))
    (eta₃ := TwistedPlaces.eta₃ L) (wP := TwistedPlaces.wP L) (Sc := L.Sc) (large₂ := TwistedPlaces.large₂ L)
    (by exact_mod_cast h11) (by positivity) (by positivity) (by positivity) (by positivity) hb.S_le
    (by positivity) hb.η_le (by positivity) hHle (etaP_le_hB L) (one_le_hB L) hBb (Lg_ge_one L)
    (placeWeight_nonneg L) hflt he (by positivity) (by exact_mod_cast hHn) hO

end GlobalTheory.RowsThick
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBounds_of_all_letters_thick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  atlas_forward_decl GlobalTheory.RowsThick.rowL_of_allThick
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowNT

theorem logb_le_of_le_four_exp {l x large₂ : ℝ} (hl : 11 ≤ l) (hLg : 0 ≤ large₂) (hx0 : 0 ≤ x)
    (hx : x ≤ 4 * Real.exp large₂) : Real.logb l x ≤ 3 + large₂ := by
  rcases hx0.eq_or_lt with h | hpos
  · subst h; simp; linarith
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h4 : Real.log x ≤ Real.log 4 + large₂ := by
    have := Real.log_le_log hpos hx
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have h43 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  unfold Real.logb
  rcases le_or_gt (Real.log x) 0 with hn | hp
  · have : Real.log x / Real.log l ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (by linarith)
    linarith
  · have : Real.log x / Real.log l ≤ Real.log x := div_le_self hp.le hlogl
    linarith

theorem lift_shape_le {l H hB e : ℝ} (hl : 11 ≤ l) (hB1 : 1 ≤ hB) (hH0 : 0 ≤ H) (hH : H ≤ 2 * hB)
    (he : e ≤ 23 * (1 + H / l + (1 + Real.logb l (H + 1)))) :
    e ≤ 69 * (1 + hB / l + Real.logb l hB) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have h1 : H / l ≤ 2 * hB / l := div_le_div_of_nonneg_right hH hl0.le
  have h2 : Real.logb l (H + 1) ≤ Real.logb l (3 * hB) :=
    Real.logb_le_logb_of_le hl1 (by linarith) (by linarith)
  have h3 : Real.logb l (3 * hB) = Real.logb l 3 + Real.logb l hB :=
    Real.logb_mul (by norm_num) (by linarith)
  have h4 : Real.logb l 3 ≤ 1 := by
    have := Real.logb_le_logb_of_le hl1 (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ l by linarith)
    rwa [Real.logb_self_eq_one hl1] at this
  have h5 : 0 ≤ Real.logb l hB := Real.logb_nonneg hl1 hB1
  have h6 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have h7 : 2 * hB / l = 2 * (hB / l) := by ring
  linarith

theorem bound_real {l n r m h w η S lg band e' hB wP eta₃ Sc large₂ ind cE : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hh : h ≤ hB) (hw : w ≤ wP) (hη : η ≤ eta₃) (hS : S ≤ Sc) (h0w : 0 ≤ w) (h0η : 0 ≤ η)
    (h0S : 0 ≤ S) (h0h : 0 ≤ h) (hlg : lg ≤ 3 + large₂) (hLg : 1 ≤ large₂) (hband : band ≤ ind)
    (hind0 : 0 ≤ ind) (he : e' ≤ 69 * cE) (hcE : 0 ≤ cE) :
    320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) + 320 * n * m * e' ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) +
        2082 * ((n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) + 22365 * (n * m * cE) := by
  have hl0 : 0 < l := by linarith
  have hA : 0 ≤ (n + 1) * r := mul_nonneg (by linarith) hr
  have e1 : h / l ^ 2 ≤ hB / l ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
  have e2 : (w + η) / l ≤ (wP + eta₃) / l := div_le_div_of_nonneg_right (by linarith) hl0.le
  have e3 : η * band ≤ eta₃ * ind := by
    have hb0 : 0 ≤ band ∨ band < 0 := le_or_gt 0 band
    rcases hb0 with hb0 | hb0
    · exact mul_le_mul hη hband hb0 (by linarith)
    · have : η * band ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0η hb0.le
      have : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
      linarith
  have e4 : 0 ≤ (wP + eta₃) / l := div_nonneg (by linarith) hl0.le
  have e5 : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
  have e6 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hbr : h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band ≤
      hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) := by
    nlinarith
  have k1 : 320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) ≤
      320 * ((n + 1) * r) * (hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) := by
    rw [mul_assoc 320 (n + 1) r]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have k2 : 320 * n * m * e' ≤ 320 * n * m * (69 * cE) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hf : 0 ≤ (n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) :=
    mul_nonneg hA (by linarith)
  have hH : 0 ≤ (n + 1) * r * (hB / l ^ 2) := mul_nonneg hA e6
  have hM : 0 ≤ n * m * cE := by positivity
  nlinarith

end GlobalTheory.NLink.RowNT

namespace GlobalTheory.NLink.RowNT

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd h17 h54 hpar h11 hπ hb hbox hN
  intro T₁ T₂ Fm h2 h1 hF
  classical
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hcA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)
  have hT := h17 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG hb.unram
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setting_of_wordsNT (by omega) hb hN inferInstance T₁ T₂ Fm h2 h1 hF
  have hX := (hT (by rw [hp]; exact h11) T₁ T₂ Fm Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi hS
    hN.w20 hN.η20 hN.twenty_words_le_b hN.some_nt).1 hN.alt
  rw [hp] at hX
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hnl : Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) = TwistedPlaces.nLam D w := by
    have e : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.2 hb.unram
    rw [e]
    exact hb.deg
  have hO := h54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ Wd.Mi Wd.hi
    (hb.t1 T₁ h1).1 (hb.t1 T₁ h1).2.2
  have hl : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hb1 : (1 : ℝ) ≤ L.sc.b := TwistedPlaces.one_le_b L
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hB1 : (1 : ℝ) ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hB2 : TwistedPlaces.hB L ≤ 2 * L.sc.b := by unfold TwistedPlaces.hB; unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hpar; linarith
  have hHm : (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ 2 * TwistedPlaces.hB L := by
    have hfl : LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi ≤ ⌊2 * TwistedPlaces.hB L⌋₊ := by
      unfold LiftingTheory.Hmax
      apply Finset.sup_le
      intro k _
      apply Nat.le_floor
      exact hbox.box_le _
    calc (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ (⌊2 * TwistedPlaces.hB L⌋₊ : ℝ) := by exact_mod_cast hfl
      _ ≤ 2 * TwistedPlaces.hB L := Nat.floor_le (by linarith)
  have he : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
      69 * coreE L (D.nd.l i) := by
    have hO' : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
        23 * (1 + (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) / ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p +
          (1 + Real.logb ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p
            ((LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) + 1))) := hO.1 hcA
    rw [hp] at hO'
    unfold coreE
    exact GlobalTheory.NLink.RowNT.lift_shape_le hl hB1 (Nat.cast_nonneg _) hHm hO'
  have hh : (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) ≤ TwistedPlaces.hB L := by
    have hwb : (Wd.w : ℝ) ≤ Wd.b := by have := hN.w20; exact_mod_cast (by omega : Wd.w ≤ Wd.b)
    have hle := hb.h_le
    unfold TruncatedSeriesCountingBounds.hB
    split_ifs
    · push_cast; linarith
    · push_cast; have : (0:ℝ) ≤ Wd.η := Nat.cast_nonneg _; linarith
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤ 3 + TwistedPlaces.large₂ L := by
    apply GlobalTheory.NLink.RowNT.logb_le_of_le_four_exp hl (by linarith [TwistedPlaces.L_ge_one L]) (by positivity)
    rw [← TwistedPlaces.b_eq]; linarith
  have hband : ((if TruncatedSeriesCountingBounds.Band (D.nd.l i) Wd.b Wd.S Wd.η Wd.sz
        (Real.logb (↑(D.nd.l i)) (2 * ↑(TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz))) 320 then 1 else 0) : ℝ) ≤
      (if bandOf L HW 320 i r ρ w then 1 else 0) := by
    split_ifs with hx hy
    · exact le_rfl
    · exact absurd ⟨h11, π, hπ, hw, Cx, hG, Wd, hb, hbox, hN, hx⟩ hy
    · norm_num
    · exact le_rfl
  have key := GlobalTheory.NLink.RowNT.bound_real (l := (D.nd.l i : ℝ)) (n := (TwistedPlaces.nLam D w : ℝ))
    (r := (D.R.r : ℝ)) (m := (D.R.m : ℝ)) hl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hh hb.w_le hb.η_le hb.S_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hlg (TwistedPlaces.L_ge_one L) hband (by split_ifs <;> norm_num) he
    (by unfold coreE; have := Real.logb_nonneg (by linarith : (1:ℝ) < D.nd.l i) hB1
        have : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) := div_nonneg (by linarith) (by linarith)
        linarith)
  obtain ⟨mm, k, e1, e2, e3⟩ := hX
  refine ⟨mm, k, e1, e2, e3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
  have hnlR : ((Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast hnl
  have hrkR : ((Module.finrank ↥Cx.LL.1 T₂.V : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  have hmR : ((Wd.m : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast hb.m_eq
  rw [hnlR, hrkR, hmR]
  simp only [bdCD, coreH, coreF, coreM, flat, rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃]
  refine le_trans key (le_of_eq ?_)
  norm_num

end GlobalTheory.NLink.RowNT
end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBounds_of_nonThick_letter : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  atlas_forward_decl GlobalTheory.NLink.RowNT.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowsCD

theorem lt_ratIn {x y : ℝ} (h : x < y) : x < ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dif_pos h]
  exact (exists_rat_btwn h).choose_spec.1

theorem flat_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 < Formalism.MainNotions.N.flat L bd l := by
  unfold Formalism.MainNotions.N.flat
  have hE : 0 < Formalism.MainNotions.TwistedPlaces.eta₃ L := by
    unfold Formalism.MainNotions.TwistedPlaces.eta₃; have := L.etaSz_pos; positivity
  have hW : 0 ≤ Formalism.MainNotions.TwistedPlaces.wP L := by
    unfold Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.wB
    have h1 := Formalism.MainNotions.TwistedPlaces.w''_nonneg L
    have h2 := L.etaSz_pos
    have h3 := le_max_left (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)
    have h4 : (0 : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by positivity
    linarith
  have h1 : 0 ≤ (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / (l : ℝ) :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h3 := Formalism.MainNotions.TwistedPlaces.L_ge_one L
  have h4 := L.Sc_pos
  by_cases hb : bd
  · rw [if_pos hb]; linarith
  · rw [if_neg hb]; linarith

theorem coreF_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreF L bd l lam := by
  unfold Formalism.MainNotions.N.coreF
  have hr : (0 : ℝ) < D.R.r := by linarith [Formalism.MainNotions.TwistedPlaces.k_le_r D, Formalism.MainNotions.TwistedPlaces.k_ge_five D]
  have hn : (0 : ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  exact mul_pos (mul_pos hn hr) (flat_pos L bd l)

theorem bdCD_lt {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E))
    (K₁ K₂ K₃ : ℝ) : Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ < Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ := by
  have e : Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ =
      Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ + Formalism.MainNotions.N.coreF L bd l lam := by
    unfold Formalism.MainNotions.N.bdCD; ring
  rw [e]
  linarith [coreF_pos L bd l lam]

end GlobalTheory.NLink.RowsCD

theorem GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  intro D L P HW F C₂ i r ρ π dc h17 h04 h54 h67 hl hπ hJ w hw _ C hC
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨hur, hW⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hB, hBox, hcase⟩ := hW C hg
  have hrow : RowL i r ρ π w hw C (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w
      (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
    rcases hcase with hNT | ⟨hC', d, hAT⟩
    · exact GlobalTheory.T.rowBounds_of_nonThick_letter D L P HW F C₂ i r ρ π w hw C hg Wd h17 h54 h67 hl hπ hB hBox hNT
    · exact GlobalTheory.T.rowBounds_of_all_letters_thick D L P HW F C₂ i r ρ π w hw C hg Wd d _ h04 h54 h67 hl hB hBox hC' hAT
  exact GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow
    (GlobalTheory.NLink.RowsCD.lt_ratIn (GlobalTheory.NLink.RowsCD.bdCD_lt L _ _ w _ _ _)).le
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsCD_rowCondition_localBounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  atlas_forward_decl GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_of_admitted_inputs :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F →
      Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap :=
  fun D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4 =>
    Formalism.MainNotions.N.Ln17.frobenius_statement_of_fontaine D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_of_localFilteredHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := by
  atlas_forward_decl GlobalTheory.theoremB_of_admitted_inputs
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissibility

theorem intersectionNumber_baseChange : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D :=
  fun D l _ K LL hb V _ _ _ _ _ ρ _ _ _ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.FontaineAdmissibility
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dDeRham_eq_dCris_of_unramified : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D := by
  atlas_forward_decl GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem dcris_exact_strict_elementwise : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  intro D l _ K LL
  have hA := (GlobalTheory.T.ramifiedCoefficientChains_adm11 D l K LL).1
  intro hbij V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ _ _ _ _ _ _ hιe hπe hinj hsurj
    hker c₀ c₁ c₂
  obtain ⟨h1, h2, h3, h4⟩ :=
    hA hbij V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π hιe hπe hinj hsurj hker.symm c₀ c₁ c₂
  refine ⟨h1, ?_, h3, fun a => (h4 a).1, ?_⟩
  · intro x hx hπx
    exact Submodule.mem_map.mp (h2.ge ⟨hx, hπx⟩)
  · intro a y hy hyF
    exact (h4 a).2.ge ⟨hy, hyF⟩

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dcris_exact_strict_elementwise_crystalline : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  atlas_forward_decl GlobalTheory.dcris_exact_strict_elementwise
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem admissibleArcDatum_gives_arcProperty : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm :=
  fun D HW F Cm hA h1f h11 => UnusedSlot80.arc_coordinates_final D HW F Cm hA h1f h11

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm := by
  atlas_forward_decl GlobalTheory.admissibleArcDatum_gives_arcProperty
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NQ

theorem relay_and_arc_inputs : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨_, _, p3, p4, p5, _, _, _, p9, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨_, _, hW1, _, _, hH, hTr, _⟩ := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨hSat, _, _, _, _, _, _, hF1, _, hF2, _⟩ := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  exact ⟨UnusedSlot80.relay_general_statement D HW F ⟨p5, p9, hH, hTr, hSat, hF1, hF2⟩,
    ⟨p3, p4, p5, p9, hH, hTr, hW1, hSat⟩⟩

end GlobalTheory.NQ
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  atlas_forward_decl GlobalTheory.NQ.relay_and_arc_inputs
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem classSplitAlongArcs : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm :=
  UnusedSlot80.split_case_A_final

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSplitting_along_arcs_of_admissible : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm := by
  atlas_forward_decl GlobalTheory.classSplitAlongArcs
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem universalPart_caseA :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D →
      UnusedSlot80.UniversalComponentCaseA D HW F Cm :=
  fun D HW F Cm hAdm h9 hH h15 => Formalism.MainNotions.UnusedSlot80.universal_general_statement_holds D HW F Cm hAdm h9 hH h15

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineUniversalPart_caseA : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D → UnusedSlot80.UniversalComponentCaseA D HW F Cm := by
  atlas_forward_decl GlobalTheory.universalPart_caseA
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremBAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  intro hBK hTD hEC D HW F Cm
  have hN1 := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨hP1, -, -, -, -, hP6, -, hP8, hP9, -⟩ := hN1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨-, ⟨hWX, -⟩, hW1, -, -, hH, -, -⟩ := h54
  have hB := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨hSat, -, hSatP, hPi0, hKL, hKill, -, hF1, -⟩ := hB
  obtain ⟨hRelay, hArcAdm⟩ := GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses hBK hTD hEC D HW F Cm
  have hA11 := GlobalTheory.T.ramifiedCoefficientChains_adm11 D
  have hArc := GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 D HW F Cm hArcAdm hP1 hA11
  have hJ := (GlobalTheory.jumps_exact_adm D HW F).2
  have hExt := GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F
  have hAdm9 := GlobalTheory.T.dcris_exact_strict_elementwise_crystalline D
  have hSplit := GlobalTheory.T.classSplitting_along_arcs_of_admissible D HW F Cm ⟨hP8, hP9, hW1, hJ, hExt, hF1, hRelay, hArc⟩ hArcAdm hP1 hP6 hWX
    (GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F) hJ hAdm9 hA11
  have hUniv := GlobalTheory.T.crystallineUniversalPart_caseA D HW F Cm ⟨hSat, hKL, hPi0, hArc⟩ hP9 hH (GlobalTheory.T.dDeRham_eq_dCris_of_unramified D)
  exact ⟨(GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1, GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm, hSat, hSatP, hKill,
    ArcLiftingSetup.content_divisibility_clause D, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hRelay, hArc, hSplit, hUniv, hAdm9, GlobalTheory.T.blochKato_crystalline_extension_criterion D⟩

end GlobalTheory.TheoremBAdm
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremB_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  atlas_forward_decl GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum
end

section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  intro hBK hTD hEC D HW F Cm C hC
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have h23 : CrystallineLiftingBounds.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).1
  have hN1 : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm hN1
  exact GlobalTheory.T.theoremB_of_localFilteredHypotheses D HW F Cm C 10 23 32 32 8 hC h22 h23 hC4 (GlobalTheory.T.localLifting_theoremB_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLiftingTheoremB_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  atlas_forward_decl GlobalTheory.theoremB_closing
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.InertStep

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  intro hP D L P nch HW F Cm X C₂ hS hC hconds2 hBCD i htw hg hR hin π hπ
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hCont, hSS, hDec, hEps, hTie, hShape, hFont, hH2, hCFT⟩ :=
    GlobalTheory.T.set_point_good hP D L P nch HW F Cm X C₂ hS i hg π hπ

  have hcB : ∀ i', GlobalTheory.HubLoc.cBnum (D.nd.l i') ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i' := by
    intro i'
    rw [hS.canon.cB]
    exact le_rfl
  have hX := GlobalTheory.closingFamilyX hP.font hP.fin D HW F L X (GlobalTheory.JumpStatement.holds_all D)
    (hS.facts.admJ L hS.par) hS.par67 hS.facts.Conclusion1.1 hS.facts.large.2.1 hS.canon.fam hcB
  obtain ⟨M0, h0, hJ⟩ := hX.2.1 i hR π
  have hTB : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    GlobalTheory.T.localBlochKatoCondition_of_wachModules D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hP.bk hP.tate hP.euler D HW F Cm) (GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) hFont hJ

  have h11 : 11 ≤ D.nd.l i := by
    have := D.nd.lPrime i
    exact GlobalTheory.Survey.InertPlacesGoodSet.eleven_le this.out hin (le_trans (by norm_num) hS.split)
  have hD := hS.canon.data
  have hROW : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) := by
    by_cases hB : KillingConditions.IsRowB L (D.nd.l i)
    · rw [hD.rowB i hin hB]
      exact GlobalTheory.T.longOrbits_rowColength_inertLocalisation D L P HW C₂ i (X.r i) (X.ρ i) π (X.dc i) hconds2 hC hS.par67 h11
        ((hBCD i htw hin π hπ).1 hB)
    · have hband : X.band i = fun lam => bandOf L HW 320 i (X.r i) (X.ρ i) lam := by
        funext lam
        exact propext (hD.band i lam)
      rw [hD.rowCD i hin hB, hband]
      exact GlobalTheory.T.rowsCD_rowCondition_localBounds D L P HW F C₂ i (X.r i) (X.ρ i) π (X.dc i)
        (GlobalTheory.T.localLiftingTheoremB_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm 320 le_rfl)
        (GlobalTheory.T.prv_twenty_five_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm)
        (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm) hS.par67 h11 hπ ((hBCD i htw hin π hπ).2 hB)

  have hLIFT : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (X.r i) (X.dc i) (X.e' i) := by
    intro w hw hwc
    rw [hD.col i hin] at hwc
    simp at hwc
  exact ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hTB, hROW, hLIFT, hCont, hSS, hDec, hEps, hTie, hShape, hFont,
    hH2, hCFT⟩

end GlobalTheory.NLink.InertStep
end
