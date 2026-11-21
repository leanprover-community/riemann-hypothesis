import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadratiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFitFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTripleCoherence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidificationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialHeckeLFunction_square_eq_primitive : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  first | exact @GlobalTheory.SqStep.charL_chs_eq | exact GlobalTheory.SqStep.charL_chs_eq | (intros; apply GlobalTheory.SqStep.charL_chs_eq <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base HasExp SplitsFully Chars)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spW spW₁ alpha beta)

private theorem standing_of_rec {D : D7} {large₂ : SizeData₂ D} (hR : Rec large₂) {T : Type} {Lc : LevCh D T} {μ₀ : T} (hL : Lc.Is μ₀)
    {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) : SquareStanding G t := by
  classical
  have hx : 11 ≤ D.host.splitBound := hR.size.2.1.eleven_le
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact GlobalTheory.SquareConv.natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

section

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {μ₀ : T}

private theorem rank_weight_component_eq (hL : Lc.Is μ₀) (i j : Fin D.R.m) : (spW G i j).rank = rankV D (i + 1) (j + 1) :=
  (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩).rank

private theorem rank_W₁ (hL : Lc.Is μ₀) (i j : Fin D.R.m) : (spW₁ G i j).rank = rankV D i j :=
  (node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩).rank

private theorem chs_α (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) : (GlobalTheory.SqStep.chs G i j t).α = alpha G t i j := by
  unfold alpha GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [rank_W₁ hL]
  rfl

private theorem chs_β (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) : (GlobalTheory.SqStep.chs G i j t).β = beta G i j := by
  unfold beta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [rank_W₁ hL]
  rfl

private theorem exps (hL : Lc.Is μ₀) (i j : Fin D.R.m) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding) :
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      (∀ t, HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα) ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) < mα w - mβ w := by
  choose mα hα eα using fun t => GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα μ₀, mβ, fun t => ?_, hβ, fun w => ?_⟩
  · have e : mα μ₀ = mα t := funext fun w => by
      have := (eα μ₀ w).trans (eα t w).symm
      exact_mod_cast this
    rw [e]
    exact hα t
  · have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
    have h1 := eα μ₀ w
    have h2 := eβ w
    have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα μ₀ w - mβ w : ℤ) : ℚ) := by
      push_cast at h1 h2 key ⊢
      rw [h1, h2]
      linarith
    exact_mod_cast this

private theorem under_notMem (hL : Lc.Is μ₀) (t : T) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ twPl G t) :
    P ∈ Lc.Q t ∧ P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hP
  refine ⟨(Finset.mem_union.1 h1).resolve_left h2, fun h => h2 ?_⟩
  have hw : G.pl.w (P.under (𝓞 D.host.F)) ∈ G.pl.W0 := Finset.mem_image_of_mem _ h
  have hw' : G.pl.w (P.under (𝓞 D.host.F)) ∈ locPl G t := Finset.mem_union_left _ hw
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t hw' h1 (G.pl.under_w h)
  rw [← e]
  exact hw

private theorem chars_good (hL : Lc.Is μ₀) (t : T) (i j : Fin D.R.m) (B : Base D.host.F D.host.E)
    (hsub : (GlobalTheory.SqStep.chs G i j t).T ⊆ B.P) (hv₁ : B.v₁ ∉ (GlobalTheory.SqStep.chs G i j t).T) (hsp : SplitsFully D.host.E B.v₁)
    (hα : HasExp B.emb (alpha G t i j) B.mα) (hβ : HasExp B.emb (beta G i j) B.mβ) :
    (GlobalTheory.SqStep.chs G i j t).IsGood B (rankV D (i + 1) (j + 1)) (rankV D i j) := by
  classical
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank (G := G) hL t i j
  rw [rank_W₁ hL] at rα
  rw [rank_weight_component_eq hL] at rβ
  have eα := chs_α (G := G) hL i j t
  have eβ := chs_β (G := G) hL i j t
  have eν : (GlobalTheory.SqStep.chs G i j t).ν = alpha G t i j / beta G i j := by
    unfold Chars.ν
    rw [eα, eβ]
  refine ⟨?_, ?_, eα ▸ GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rα, eβ ▸ GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rβ, eα ▸ hα, eβ ▸ hβ, ?_, hsub, ?_, ?_, ?_,
    ⟨hv₁, hsp⟩⟩
  · have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show Lc.mu0 ((j : ℕ) + 1) _ * Lc.xi t _ * (Lc.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (Lc.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  · refine Finset.disjoint_right.2 fun v hv hv0 => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hv
    exact (under_notMem hL t hP).2 hv0
  · intro w hw
    rw [eν]
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
      · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
      · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hw
      obtain ⟨h1, h2⟩ := under_notMem hL t hP
      exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P h1 e (e ▸ h2)
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ (GlobalTheory.SqStep.chs G i j t).T := hw
    rw [eα]
    have h0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (Finset.mem_union_left _ h)
    refine GlobalTheory.T.alpha_unramified_outside hL t i j w h0 fun P hP e => hw' ?_
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨P, Finset.mem_filter.2 ⟨Finset.mem_union_right _ hP, fun h => ?_⟩, e⟩)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    rw [G.pl.under_w hv] at e
    exact h0 (e ▸ hv)
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ (GlobalTheory.SqStep.chs G i j t).T := hw
    rw [eβ]
    exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end

private theorem fit_down_left_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a' : ℕ} :
    ∀ (k b : ℕ), Fit G W i j t μ₀ Bs (b + 2 * k) a' → Fit G W i j t μ₀ Bs b a'
  | 0, _, h => by simpa using h
  | k + 1, b, h => fit_down_left_mul k b (Fit.down_left (by rw [show b + 2 * k + 2 = b + 2 * (k + 1) by ring]; exact h))

private theorem fit_down_right_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a : ℕ} :
    ∀ (k b : ℕ), Fit G W i j t μ₀ Bs a (b + 2 * k) → Fit G W i j t μ₀ Bs a b
  | 0, _, h => by simpa using h
  | k + 1, b, h => fit_down_right_mul k b (Fit.down_right (by rw [show b + 2 * k + 2 = b + 2 * (k + 1) by ring]; exact h))

theorem _root_.GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w, ∀ t : T,
        ∃ Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E, Bs.emb = emb ∧ GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank := by
  classical
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ he hx hR T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j p q A A' WW X hX
  choose τf hτf using (GlobalTheory.T.exists_conj_tauE_comp_algebraMap_eq_embedding (D := D))
  refine ⟨fun w => ⟨_, hτf w⟩, fun t => ?_⟩
  have hst := standing_of_rec hR hL G t
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := exps (G := G) hL i j τf hτf
  have hloc : ∀ v ∈ (GlobalTheory.SqStep.chs G i j t).T, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv), G.pl.under_w hv⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hv
      exact ⟨P, (Finset.mem_filter.1 hP).1, e⟩
  have hτ := fun v : ((GlobalTheory.SqStep.chs G i j t).T : Finset (HeightOneSpectrum (𝓞 D.host.F))) =>
    GlobalTheory.LocPlTau.exists_splitPrime_locPl hL t v.1 (hloc v.1 v.2)
  choose τP hτP using hτ
  obtain ⟨v₁, hv₁P, hv₁s, -, ⟨τ₁⟩⟩ := GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset (G := G) hL t (GlobalTheory.SqStep.chs G i j t).T
  let B : Base D.host.F D.host.E := ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, (GlobalTheory.SqStep.chs G i j t).T, τP, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding hL W t hst B rfl hloc
  have hsub₀ : (GlobalTheory.SqStep.chs G i j μ₀).T ⊆ (GlobalTheory.SqStep.chs G i j t).T := by
    rw [GlobalTheory.SqStepArith.chs_T_base G hL i j]
    exact Finset.subset_union_left
  have hfit : Fit G W i j t μ₀ B (rankV D (i + 1) (j + 1)) (rankV D i j) := by
    refine ⟨⟨rfl, subset_rfl, hB.psiP, fun v hv => ?_⟩, hB, fun w => ⟨τf w, fun _ => rfl⟩,
      chars_good hL t i j B subset_rfl hv₁P hv₁s (hα t) hβ,
      chars_good hL μ₀ i j B hsub₀ (fun h => hv₁P (hsub₀ h)) hv₁s (hα μ₀) hβ, hκ⟩
    obtain ⟨w, hw, e⟩ := hloc v.1 hv
    rw [hτP v w hw e]
    exact hw
  refine ⟨B, rfl, ?_⟩
  obtain ⟨hp, hq, hA, hA', -⟩ := hX
  have e1 : rankV D (i + 1) (j + 1) = A.rank + 2 * (pp D j - p) := by omega
  have e2 : rankV D i j = A'.rank + 2 * (qq D j - q) := by omega
  rw [e1, e2] at hfit
  exact fit_down_right_mul _ _ (fit_down_left_mul _ _ hfit)

end GlobalTheory.SqStepBig

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B₀ B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.emb = B₀.emb → ∀ (n n₁ : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (H₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁) (i₀ i₁ : ℕ), i₀ < i₁ → i₁ < n → Y.L.IsLattice E → Y₁.L.IsLattice E →
    H₀.IsAdapted σ B₀ Y Y₁ i₀ i₁ → ∃ (Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁),
      Y'.θ = Y.θ ∧ Y₁'.θ = Y₁.θ ∧ (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) ∧
      (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L (Y₁'.bas v)) ∧
      H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') (GlobalTheory.ThK.reS Y₁ Y₁') i₀ i₁ := by
  intro F E _ _ _ _ _ σ hcm B₀ B hemb n n₁ Y Y₁ H₀ i₀ i₁ h01 h1n hL hL₁ hH
  classical
  have hss : ∀ a : E, σ (σ a) = a := fun a => by
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  have fsl : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (s • a) b = s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b := fun J s a b => by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct]
  have fsr : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b (s • a) = σ s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun J s a b => by
    have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hx0 : H₀.x ≠ 0 := by
    intro h; have := hH.xy; rw [h] at this; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at this
  have hy0 : H₀.y ≠ 0 := by
    intro h
    have h1 := hH.xy
    have h2 := fsr Y.J 0 H₀.y H₀.x
    rw [zero_smul, map_zero, zero_mul, ← h, h1] at h2
    exact one_ne_zero h2
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.PlaneSkewScale.exists_rescale_primAt F E σ hcm n Y.L hL H₀.x H₀.y hx0 hy0 B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc0 (by rw [← hss c, h, map_zero])
  set x : Fin n → E := c • H₀.x with hxdef
  set y : Fin n → E := (σ c)⁻¹ • H₀.y with hydef
  have ex : ∀ s : E, (s * c⁻¹) • x = s • H₀.x := fun s => by
    rw [hxdef, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have ey : ∀ t : E, (t * σ c) • y = t • H₀.y := fun t => by
    rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
  let 𝔟 : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ c⁻¹ * H₀.𝔟
  have h𝔟 : ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ Y.L := by
    intro s
    rw [FractionalIdeal.mem_singleton_mul, hxdef, smul_smul]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mul_comm c⁻¹ t, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      exact (hH.ideal t).1 ht
    · intro h
      refine ⟨s * c, (hH.ideal _).2 h, ?_⟩
      rw [mul_comm s c, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧
      z = s • x + H₀.ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split z hz
    exact ⟨s * c⁻¹, t * σ c, u, by rw [ex]; exact hs, by rw [ey]; exact ht, hu, by rw [ex, ey]⟩
  haveI : Y₁.L.IsLattice E := hL₁
  have hcomap : Y.L.comap ((Matrix.mulVecLin H₀.ι).restrictScalars (𝓞 E)) = Y₁.L :=
    Submodule.ext fun u => (hH.low u).symm
  have hb₁ : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L β := fun v =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Y₁.L hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else Y₁.bas v
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.skip i₀ i₁ j → ∀ r, β.1 r i = (H₀.ι.map (B.τ v) * (β₁ v).1) r j) ∧
      GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y H₀.ι (β₁ v) i₀ i₁ hH.rank h01 h1n hL
      (fun z hz => by
        obtain ⟨s, t, u, hs, ht, hu, hz'⟩ := hsplit z hz
        exact ⟨s, t, u, hs, ht, (hH.low u).1 hu, hz'⟩)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).1)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).2)
      (by rw [hcomap]; exact hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n := ⟨Y.J, Y.L, Y.θ, bas⟩
  let Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁ := ⟨Y₁.J, Y₁.L, Y₁.θ, bas₁⟩
  refine ⟨Y', Y₁', ⟨x, y, H₀.ι, 𝔟⟩, rfl, rfl, fun v => ?_, fun v => ?_, ?_⟩
  · rw [show Y'.bas v = β v from hbas v]; exact (hβ v).2
  · rw [show Y₁'.bas v = β₁ v from hbas₁ v]; exact hβ₁ v
  · exact
      { rank := hH.rank
        xx := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x x = 0
          rw [hxdef, fsl, fsr, hH.xx, mul_zero, mul_zero]
        yy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J y y = 0
          rw [hydef, fsl, fsr, hH.yy, mul_zero, mul_zero]
        xy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x y = 1
          rw [hxdef, hydef, fsl, fsr, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hc0]
        orth := fun u => by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) x = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) y = 0
          rw [hxdef, hydef, fsr, fsr, (hH.orth u).1, (hH.orth u).2, mul_zero, mul_zero]
          exact ⟨rfl, rfl⟩
        gram := hH.gram
        low := hH.low
        split := hsplit
        ideal := h𝔟
        cartan := fun w => by
          obtain ⟨hθι, c₀, hc₀, he⟩ := hH.cartan w
          rw [hemb]
          refine ⟨hθι, (B₀.emb w).1 (σ c)⁻¹ * c₀ * ((B₀.emb w).1 c)⁻¹, ?_, ?_⟩
          · have h1 : (B₀.emb w).1 (σ c)⁻¹ ≠ 0 := (map_ne_zero _).2 (inv_ne_zero hσc)
            have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            exact mul_ne_zero (mul_ne_zero h1 hc₀) (inv_ne_zero h2)
          · have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            have hx' : (fun i => (B₀.emb w).1 (x i)) = (B₀.emb w).1 c • fun i => (B₀.emb w).1 (H₀.x i) :=
              funext fun i => by simp [hxdef]
            have hy' : (fun i => (B₀.emb w).1 (y i)) = (B₀.emb w).1 (σ c)⁻¹ • fun i => (B₀.emb w).1 (H₀.y i) :=
              funext fun i => by simp [hydef]
            show (fun i => (B₀.emb w).1 (y i)) = _ • Y.θ w *ᵥ fun i => (B₀.emb w).1 (x i)
            rw [hx', hy', he, Matrix.mulVec_smul, smul_smul, smul_smul]
            congr 1
            field_simp
        bas := fun v i => by
          rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show (GlobalTheory.ThK.reS Y₁ Y₁').bas v = β₁ v from hbas₁ v]
          exact (hβ v).1 i }

end
end

section
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x


end GlobalTheory.IdxAll
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSpace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc HasSig)
open scoped Matrix

variable {D : D7}

def cO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)

instance surj_cO : RingHomSurjective (cO D) :=
  ⟨fun o => ⟨cO D o, by ext; simp [cO]⟩⟩

instance surj_star : RingHomSurjective (starRingEnd D.host.E) :=
  ⟨fun o => ⟨star o, by rw [starRingEnd_apply, star_star]⟩⟩

def cvO (D : D7) (n : ℕ) : (Fin n → D.host.E) →ₛₗ[cO D] (Fin n → D.host.E) where
  toFun z i := star (z i)
  map_add' x y := by ext i; simp
  map_smul' o z := by
    ext i
    simp only [Pi.smul_apply, cO]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [smul_eq_mul, star_mul', mul_eq_mul_left_iff, map_mul, Pi.smul_apply]
    first
      | exact Or.inl rfl
      | (simp [mul_comm]; exact Or.inl rfl)

def cvE (D : D7) (n : ℕ) : (Fin n → D.host.E) →ₛₗ[starRingEnd D.host.E] (Fin n → D.host.E) where
  toFun z i := star (z i)
  map_add' x y := by ext i; simp
  map_smul' o z := by
    funext i
    show star (o * z i) = star o * star (z i)
    exact star_mul' _ _

def conjLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  L.map (cvO D n)

theorem mem_conjLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (z : Fin n → D.host.E) :
    z ∈ conjLat L ↔ (fun i => star (z i)) ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : (fun i => star ((cvO D n) y i)) = y := by ext i; simp [cvO]
    rw [e]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    ext i; simp [cvO]

theorem isLattice_conjLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : L.IsLattice D.host.E) :
    (conjLat L).IsLattice D.host.E := by
  refine ⟨hL.fg.map _, ?_⟩
  have h1 : ((conjLat L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = cvE D n '' (L : Set _) := by
    rw [conjLat, Submodule.map_coe]; rfl
  rw [h1, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  intro z
  exact ⟨fun i => star (z i), by ext i; simp [cvE]⟩

theorem isIntegral_star_iff (a : D.host.E) : IsIntegral ℤ (star a) ↔ IsIntegral ℤ a := by
  constructor
  · intro h
    have := map_isIntegral_int (starRingEnd D.host.E) h
    rwa [starRingEnd_apply, star_star] at this
  · intro h
    exact map_isIntegral_int (starRingEnd D.host.E) h

theorem form_conj {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : ∀ i j, D.sp.cm.sig (J j i) = J i j)
    (a b : Fin n → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J (fun i => star (a i)) b =
      star (∑ i, ∑ j, star (star (b i)) * J i j * a j) := by
  have hs : ∀ i j, star (J i j) = J j i := fun i j => hJ j i
  have hσ : ∀ x, D.sp.cm.sig x = star x := fun _ => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, hσ, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {B : Base D.host.F D.host.E} {n r s : ℕ} {V : Spc D.host.F D.host.E n}

theorem mem_conjLat_iff (hV : V.IsHerm D.sp.cm.sig B r s) (z : Fin n → D.host.E) :
    z ∈ conjLat V.L ↔ ∀ x ∈ conjLat V.L, IsIntegral ℤ (∑ i, ∑ j, star (x i) * V.J i j * z j) := by
  rw [mem_conjLat, hV.dual]
  constructor
  · intro h x hx
    rw [mem_conjLat] at hx
    have h1 := h _ hx
    rw [form_conj V.J hV.herm] at h1
    simpa only [star_star, isIntegral_star_iff] using h1
  · intro h y hy
    have hx : (fun i => star (y i)) ∈ conjLat V.L := by
      rw [mem_conjLat]; simpa only [star_star] using hy
    have h1 := h _ hx
    rw [form_conj V.J hV.herm, isIntegral_star_iff]
    exact h1

theorem sesq_herm (hV : V.IsHerm D.sp.cm.sig B r s) : (GlobalTheory.WeilSchrodinger.sesq D V.J).IsSymm := by
  have hs : ∀ i j, star (V.J i j) = V.J j i := fun i j => hV.herm j i
  refine ⟨fun x y => ?_⟩
  simp only [GlobalTheory.WeilSchrodingerHerm.sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
    star_star, Pi.star_apply, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_nondeg (hV : V.IsHerm D.sp.cm.sig B r s) : (GlobalTheory.WeilSchrodinger.sesq D V.J).Nondegenerate := by
  have hdet : V.J.det ≠ 0 := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D B V hV
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : star x ᵥ* V.J = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← GlobalTheory.WeilSchrodingerHerm.sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  · have h1 : V.J *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [GlobalTheory.WeilSchrodingerHerm.sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1

theorem sesq_unimod (hV : V.IsHerm D.sp.cm.sig B r s) :
    Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D V.J) (conjLat V.L) := by
  show Formalism.E.hdual _ (conjLat V.L) = conjLat V.L
  ext x
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [mem_conjLat_iff hV x]
  refine forall₂_congr fun y _ => ?_
  rw [GlobalTheory.WeilSchrodingerHerm.sesq_apply, GlobalTheory.WeilSchrodingerHerm.mem_one_iff]
  have e : star y ⬝ᵥ (V.J *ᵥ x) = ∑ i, ∑ j, star (y i) * V.J i j * x j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [e]

theorem hasSig_map_conj {m a b : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : HasSig M a b) :
    HasSig (M.map (starRingEnd ℂ)) a b := by
  obtain ⟨hn, A, hA⟩ := h
  refine ⟨hn, A.map star, ?_⟩
  have e1 : (A.map star).map star = A := by ext i j; simp
  have e2 : (A.map star)ᵀ * M.map (starRingEnd ℂ) * A = (Aᵀ * M * A.map star).map (starRingEnd ℂ) := by
    simp only [Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext i j; simp
  rw [e1, e2, hA, Matrix.fromBlocks_map]
  have e3 : (-1 : Matrix (Fin b) (Fin b) ℂ).map (starRingEnd ℂ) = -1 := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp [e3]

theorem hasSignature_all (hG : B.IsGood D.sp.cm.sig) {m a b : ℕ} (J : Matrix (Fin m) (Fin m) D.host.E)
    (hs : ∀ w, HasSig (J.map (B.emb w).1) a b) (φ : D.host.E →+* ℂ) : Formalism.UG.HasSignature (J.map φ) a b := by
  have h := hG.cm
  haveI := h.1
  set w := InfinitePlace.mk (φ.comp (algebraMap D.host.F D.host.E)) with hw
  have hreal : ComplexEmbedding.IsReal (φ.comp (algebraMap D.host.F D.host.E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have he : (B.emb w).1.comp (algebraMap D.host.F D.host.E) = φ.comp (algebraMap D.host.F D.host.E) := by
    rw [(B.emb w).2, hw, InfinitePlace.embedding_mk_eq_of_isReal hreal]
  refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
  rcases GlobalTheory.IdxAll.eq_or_eq_comp _ h _ _ he with h1 | h1
  · rw [h1]; exact hasSig_map_conj (hs w)
  · have e : (J.map φ).map (starRingEnd ℂ) = J.map (B.emb w).1 := by
      ext i j; simp [h1]
    rw [e]; exact hs w

end GlobalTheory.ConjSpace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc) in

theorem GlobalTheory.ConjSpace.main : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  intro D Bs hG _ n r p V hV
  have hn : r + p = n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    exact (hV.sig w).1
  have hgram := GlobalTheory.WeilSchrodinger.gram_hspOf V.J (GlobalTheory.ConjSpace.sesq_herm hV) (GlobalTheory.ConjSpace.sesq_nondeg hV)
    (GlobalTheory.ConjSpace.conjLat V.L) (GlobalTheory.ConjSpace.isLattice_conjLat hV.lat) (GlobalTheory.ConjSpace.sesq_unimod hV)
    (fun _ => (n - p, p))
  refine ⟨GlobalTheory.WeilSchrodinger.hspOf D V.J (GlobalTheory.ConjSpace.sesq_herm hV) (GlobalTheory.ConjSpace.sesq_nondeg hV)
    (GlobalTheory.ConjSpace.conjLat V.L) (GlobalTheory.ConjSpace.isLattice_conjLat hV.lat) (GlobalTheory.ConjSpace.sesq_unimod hV)
    (fun _ => (n - p, p)), GlobalTheory.ConjSpace.conjLat V.L, ⟨GlobalTheory.ConjSpace.isLattice_conjLat hV.lat, fun y => ?_⟩,
    fun τ => ?_, ⟨rfl, ?_, fun y => ?_⟩⟩
  · rw [hgram]
    refine (GlobalTheory.ConjSpace.mem_conjLat_iff (n := n) hV y).trans ?_
    refine forall₂_congr fun x _ => ?_
    exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩
  · show Formalism.UG.HasSignature ((HSpace.gram _).map (tauE D τ)) _ p
    rw [hgram]
    have h := GlobalTheory.ConjSpace.hasSignature_all hG V.J hV.sig (tauE D τ)
    have hr : r = n - p := by omega
    rw [hr] at h
    exact h
  · rw [hgram, one_smul]
    rfl
  · refine Iff.symm ((GlobalTheory.ConjSpace.mem_conjLat (n := n) V.L _).trans ?_)
    simp only [star_star]
    exact Iff.rfl

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  atlas_forward_decl GlobalTheory.ConjSpace.main
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SkewOverW

open Matrix GlobalTheory.SkewLat GlobalTheory.SkewLat.DualPair
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (HasSig form)
open scoped nonZeroDivisors

private theorem hasSignature_of_smul {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSig ((κ : ℂ) • M) r s) : Formalism.UG.HasSignature M r s := by
  refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
  obtain ⟨h1, A, hA⟩ := h
  refine ⟨h1, ((Real.sqrt κ : ℝ) : ℂ) • A.map star, ?_⟩
  have h2 := congrArg (fun X : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul] at h2
  have e2 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) =
      Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp
  have hs : ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) = (κ : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hκ.le
  have t1 : (((Real.sqrt κ : ℝ) : ℂ) • A.map star)ᵀ = ((Real.sqrt κ : ℝ) : ℂ) • (Aᵀ).map (starRingEnd ℂ) := by
    ext i j; simp
  have t2 : (((Real.sqrt κ : ℝ) : ℂ) • A.map star).map star =
      ((Real.sqrt κ : ℝ) : ℂ) • (A.map star).map (starRingEnd ℂ) := by
    ext i j; simp
  have t3 : ((κ : ℂ) • M).map (starRingEnd ℂ) = (κ : ℂ) • M.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [t3, e2] at h2
  rw [t1, t2, ← h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]

variable {D : D7}

private theorem form_smul {d : ℕ} (J : Matrix (Fin d) (Fin d) D.host.E) (c e : D.host.E) (y x : Fin d → D.host.E) :
    form D.sp.cm.sig J (c • y) (e • x) = c * star e * form D.sp.cm.sig J y x := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, hσ, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem mem_lat {d : ℕ} {L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)} {y : Fin d → D.host.E} :
    y ∈ scLat D.host.AA⁻¹ L ↔ ∀ c ∈ D.host.AA, c • y ∈ L := by
  rw [mem_scLat, inv_inv]

private theorem smul_mem_lat {d : ℕ} {L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)} {y : Fin d → D.host.E}
    (hy : y ∈ L) {e : D.host.E} (he : e ∈ D.host.AA⁻¹) : e • y ∈ scLat D.host.AA⁻¹ L := by
  refine mem_lat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul he hc
  rw [smul_smul, mul_comm, ← hb]
  exact L.smul_mem b hy

private theorem mem_iff {d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : Fin d → D.host.E) :
    y ∈ L ↔ y ∈ scLat D.host.AA (scLat D.host.AA⁻¹ L) := by
  refine ⟨fun hy e he => smul_mem_lat hy he, fun h => ?_⟩
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, u • y ∈ L := fun u hu =>
    FractionalIdeal.mul_induction_on hu (C := fun u => u • y ∈ L)
      (fun a ha e he => by rw [mul_smul]; exact mem_lat.1 (h e he) a ha)
      (fun u v hu hv => by rw [add_smul]; exact L.add_mem hu hv)
  simpa using key 1 one_mem_AA_mul

private theorem dual_iff {d : ℕ} (J : Matrix (Fin d) (Fin d) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, IntTr (form D.sp.cm.sig J y x)) (y : Fin d → D.host.E) :
    y ∈ scLat D.host.AA⁻¹ L ↔ ∀ x ∈ scLat D.host.AA⁻¹ L,
      ∃ b : 𝓞 D.host.E, (b : D.host.E) = D.host.xi0⁻¹ * form D.sp.cm.sig J y x := by
  have hξ : D.host.xi0 ≠ 0 := xi_ne
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := fun c h => GlobalTheory.star_mem_AA_of_mem_AAbar h
  constructor
  · intro hy x hx
    have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) * D.host.AA * D.host.AAbar ≤
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar := by
      rw [hX, mul_assoc, FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ z ?_
      refine FractionalIdeal.mul_induction_on hj
        (C := fun j => form D.sp.cm.sig J y x * j ∈
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E))
        (fun a ha b hb => ?_) (fun u v hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      have h1 := (intTr_iff_mem_dual _).1 ((hL _).1 (mem_lat.1 hy a ha) _ (mem_lat.1 hx _ (hc b hb)))
      rw [form_smul, star_star, mul_comm] at h1
      exact h1
    have hne : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero AA_ne AAbar_ne
    have hle' : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) ≤
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 := by
      rw [mul_assoc, mul_assoc] at hle
      calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x)
          = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) * (D.host.AA * D.host.AAbar) *
            (D.host.AA * D.host.AAbar)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
        _ ≤ FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * (D.host.AA * D.host.AAbar) *
            (D.host.AA * D.host.AAbar)⁻¹ := by gcongr
        _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).1 (hle' (FractionalIdeal.mem_spanSingleton_self _ _))
    refine ⟨z, ?_⟩
    rw [← hz, Algebra.smul_def]
    field_simp
  · intro h
    refine mem_lat.2 fun c hcA => (hL _).2 fun x hx => ?_
    have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, IntTr (c * star u * form D.sp.cm.sig J y x) := by
      intro u hu
      refine FractionalIdeal.mul_induction_on hu (C := fun u => IntTr (c * star u * form D.sp.cm.sig J y x))
        (fun a ha e he => ?_) (fun u v hu hv => ?_)
      · obtain ⟨b, hb⟩ := h _ (smul_mem_lat hx he)
        have h1 := form_smul J 1 e y x
        rw [one_smul, one_mul] at h1
        have e1 : c * star (a * e) * form D.sp.cm.sig J y x = D.host.xi0 * c * star a * (b : D.host.E) := by
          rw [hb, h1, star_mul']
          field_simp
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs hcA ha)).mul_int b
      · rw [star_add, mul_add, add_mul]
        exact hu.add hv
    have h1 := form_smul J c 1 y x
    rw [one_smul] at h1
    rw [h1]
    exact key 1 one_mem_AA_mul

private theorem exists_place (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (h : GlobalTheory.SqStepBig.EmbCM Bs) (τ : D.what₂.Tau) :
    ∃ w, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x) := by
  refine ⟨InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)), ?_⟩
  obtain ⟨τ', hτ'⟩ := h (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  have e : τ' = τ := by
    apply (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D).1
    have h1 := (Bs.emb (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))).2
    have h2 : ComplexEmbedding.conjugate ((tauE D τ').comp (algebraMap D.host.F D.host.E)) =
        (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding := by
      rw [← h1]
      ext x
      simp [hτ']
    show InfinitePlace.mk _ = InfinitePlace.mk _
    rw [← InfinitePlace.mk_conjugate_eq, h2, InfinitePlace.mk_embedding]
  rwa [e] at hτ'

end GlobalTheory.SkewOverW

open Matrix GlobalTheory.SkewOverW GlobalTheory.SkewLat GlobalTheory.WeilSchrodinger GlobalTheory.WeilSchrodingerHerm in
theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_scaled_skewHermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (d r y : ℕ) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d), Z.IsSkew D.sp.cm.sig Bs r y →
      ∃ (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
        IsSelfDualC WW Λ ∧ NegIdx WW y ∧ GlobalTheory.SqStepBig.OverW WW Λ Z := by
  intro D Bs _ hemb d r y Z hZ
  have hξ : D.host.xi0 ≠ 0 := DualPair.xi_ne
  have hsξ : star D.host.xi0 = -D.host.xi0 := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  have hsk : ∀ i j, star (Z.J j i) = -Z.J i j := fun i j => hZ.skew i j
  set G : Matrix (Fin d) (Fin d) D.host.E := (D.host.xi0⁻¹ • Z.J)ᵀ with hG
  have hGij : ∀ i j, G i j = D.host.xi0⁻¹ * Z.J j i := fun i j => rfl
  have hsG : ∀ i j, star (G i j) = G j i := fun i j => by
    rw [hGij, hGij, star_mul', star_inv₀, hsξ, hsk, inv_neg, neg_mul_neg]
  have hdetJ : Z.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    have h := det_ne_zero_of_hasSig (hZ.sig w)
    intro h0
    apply h
    have hm : (Z.J.map (Bs.emb w).1).det = (Bs.emb w).1 Z.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]
  have hdet : G.det ≠ 0 := by
    rw [hG, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hξ)) hdetJ
  have hform : ∀ x v, sesq D G x v = D.host.xi0⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig Z.J v x := fun x v => by
    rw [hG, sesq_transpose_eq_form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hsum : ∀ x v : Fin d → D.host.E, ∑ i, ∑ j, star (x i) * G i j * v j =
      D.host.xi0⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig Z.J v x := fun x v => by
    rw [← hform, sesq_apply]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hdual := dual_iff Z.J Z.L hZ.dual
  have hlat : Submodule.IsLattice D.host.E (scLat D.host.AA⁻¹ Z.L) :=
    PairLatLattice.scLat_isLattice (inv_ne_zero DualPair.AA_ne) hZ.lat
  have herm : (sesq D G).IsSymm := by
    refine ⟨fun x v => ?_⟩
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
      star_star, Pi.star_apply, hsG, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have nd : (sesq D G).Nondegenerate := by
    refine ⟨fun x hx => ?_, fun v hv => ?_⟩
    · have h1 : star x ᵥ* G = 0 := by
        refine dotProduct_eq_zero _ fun v => ?_
        rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
        exact hx v
      have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
      simpa using congrArg star h2
    · have h1 : G *ᵥ v = 0 := by
        refine dotProduct_eq_zero _ fun u => ?_
        rw [dotProduct_comm]
        have := hv (star u)
        rwa [sesq_apply, star_star] at this
      exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) (scLat D.host.AA⁻¹ Z.L) := by
    show Formalism.E.hdual _ _ = _
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hdual x]
    refine forall₂_congr fun v _ => ?_
    rw [hform, Submodule.mem_one]
  have hgram := gram_hspOf G herm nd _ hlat hU (fun _ => (r, y))
  refine ⟨hspOf D G herm nd _ hlat hU (fun _ => (r, y)), scLat D.host.AA⁻¹ Z.L, ⟨hlat, fun v => ?_⟩, fun τ => ?_,
    rfl, ?_, fun v => mem_iff Z.L v⟩
  · rw [hgram]
    refine (hdual v).trans (forall₂_congr fun x _ => ?_)
    exact exists_congr fun b => Eq.congr_right (hsum x v).symm
  · obtain ⟨w, hw⟩ := exists_place Bs hemb τ
    have hs := hZ.sig w
    have hre : (tauE D τ D.host.xi0).re = 0 := by
      have h := congrArg Complex.re (GlobalTheory.FockCompare.tauE_star τ D.host.xi0)
      rw [hsξ, map_neg, Complex.neg_re, Complex.conj_re] at h
      linarith
    have hx : (Bs.emb w).1 D.host.xi0 = -((((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I) := by
      rw [hw]; apply Complex.ext <;> simp [hre]
    have hJ : ∀ i j, Z.J i j = D.host.xi0 * star (G i j) := fun i j => by
      rw [hsG, hGij, mul_inv_cancel_left₀ hξ]
    have hM : Complex.I • Z.J.map (Bs.emb w).1 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) • G.map (tauE D τ) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      rw [hJ, map_mul, hx, hw, GlobalTheory.FockCompare.tauE_star, Complex.conj_conj]
      linear_combination (-(((tauE D τ D.host.xi0).im : ℝ) : ℂ) * tauE D τ (G i j)) * Complex.I_mul_I
    rw [hM] at hs
    have h := hasSignature_of_smul (xi_zero_im_pos D τ) hs
    have hr : r = d - y := by have := hs.1; omega
    rw [hr] at h
    unfold gramAt
    rw [hgram]
    exact h
  · rw [hgram]
    ext i j
    show Z.J i j = D.host.xi0 * G j i
    rw [hGij, mul_inv_cancel_left₀ hξ]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem chrEq_pow' {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · have hp : (χ ^ a).locK P k = χ.locK P k ^ a := by
      have : ∀ x, (χ ^ a).1 x = χ.1 x ^ a := fun x => by rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
      exact this _
    rw [MonoidHom.pow_apply, hp, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem exists_prime_power_pow_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) : c ^ n = 1 := by
  have h1 := chrEq_pow' h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem _root_.GlobalTheory.T.squareNu_ratio_values_roots_of_unity : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ), ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
      (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) = D.what₂.embLL ζ := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W S hN i j t k => ?_⟩⟩
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hc1 : Lc.xi μ₀ k = 1 := GlobalTheory.ChrEqUnique.eq_one_of_chrEq (hL.xi_base ▸ hL.xi μ₀) k
  have e : (GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k = Lc.xi t k := by
    have key : ∀ {Γ : Type} [CommGroup Γ] (a x y e c : Γ), y = 1 → (a * x * e / (c * e)) / (a * y * e / (c * e)) = x := by
      intro Γ _ a x y e c hy
      subst hy
      rw [mul_one, div_div_div_cancel_right, mul_div_mul_right_eq_div, mul_div_cancel_left]
    exact key (Lc.mu0 ((j : ℕ) + 1) k) (Lc.xi t k) (Lc.xi μ₀ k) ((Lc.eta ^ (rankV D i j % 2)) k) (G.ch.chi (D.R.m - i) k) hc1
  obtain ⟨y, hy⟩ := GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field D (Lc.xi t) (Lc.xiH t) n _ D.what₂.embLL (hL.xi t) hn ho ((hN.chars.xi t).valuesIn) k
  have h1 : ((Lc.xi t k : Circle) : ℂ) ^ n = 1 := by
    have := DFunLike.congr_fun (exists_prime_power_pow_eq_one (hL.xi t) ho) k
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have hyn : (y : D.what₂.LL) ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hy, h1, map_one])
  exact ⟨y, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one _ hn hyn, by rw [e, hy]⟩
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.Square

theorem awayUnit_inv {K : Type} [Field K] {m : ℕ} {x : K} (hx : x ≠ 0) (h : IsAwayUnit m x) : IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hxa⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ?_, ?_⟩
  · rw [pow_add, hb]
    exact mul_dvd_mul_left _ (dvd_mul_left _ _)
  · have hb' : (m : K) ^ k' = (a : K) * (b : K) := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hb
    have : ((((m : 𝓞 K) ^ k * b : 𝓞 K)) : K) = (m : K) ^ k * (b : K) := by push_cast; ring
    rw [this, hb', ← hxa]
    field_simp

theorem stepRatio_swap {K P : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {m : ℕ} {S₀ : Finset P} {cc qq : P → ℕ} {u u₀ C : ℂ} {ζ : K}
    (h : StepRatio σ m S₀ cc qq u₀ u) (h0 : u₀ ≠ 0) (hζ : IsAwayUnit m ζ) :
    StepRatio σ m S₀ cc qq (C * σ ζ * u) (C * u₀) := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  have h1 : b * ∏ v ∈ S₀, (g v : K) / (g' v : K) ≠ 0 := fun hz => h0 (by rw [e, hz, map_zero, zero_mul])
  refine ⟨ζ * b⁻¹, g', g, hζ.mul (awayUnit_inv (left_ne_zero_of_mul h1) hb), fun v hv => (hg v hv).symm, ?_⟩
  have h2 : ∏ v ∈ S₀, (g' v : K) / (g v : K) = (∏ v ∈ S₀, (g v : K) / (g' v : K))⁻¹ := by
    rw [← Finset.prod_inv_distrib]; simp only [inv_div]
  have h3 : σ (b * ∏ v ∈ S₀, (g v : K) / (g' v : K)) ≠ 0 := (map_ne_zero σ).2 h1
  rw [h2, mul_assoc ζ, ← mul_inv, map_mul, map_inv₀, e]
  field_simp

theorem gbig_of_three {Q1 Q2 Q3 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2) (h3 : GBig Q3)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q3 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, g3⟩ := h3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G
  · exact g3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G

theorem two_le_half {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {p q e : ℕ} {A A' WW : HSp D} {X : Tri T A A' WW} (h : GlobalTheory.SqTower.IsStageC W i j p q X)
    (he : A.rank = A'.rank + 2 * e) : 2 ≤ e := by
  obtain ⟨hp, hq, hA, hA', -⟩ := h
  obtain ⟨k, hk⟩ := D.R.k_even
  obtain ⟨m, hm⟩ := D.R.m_even
  obtain ⟨t, ht⟩ := D.R.t_odd
  have h2 := D.R.two_le_m
  have h3 := D.R.three_m_lt_t
  have e1 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have e2 : sLen D = D.R.k + D.R.m - 1 + 6 := rfl
  simp only [pp, qq] at *
  omega

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LFun

section IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem reS_congr {n : ℕ} {X X₂ : Spc F E n} (Y : Spc F E n) (h : X₂.J = X.J ∧ X₂.L = X.L) : reS X₂ Y = reS X Y := by
  cases X; cases X₂; obtain ⟨h1, h2⟩ := h; cases h1; cases h2; rfl

theorem isHerm_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsHerm σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsHerm σ B r s :=
  { herm := h.herm, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isSkew_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsSkew σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsSkew σ B r s :=
  { skew := h.skew, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isGood_reG {B : Base F E} {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {V : Spc F E a} {V' : Spc F E a'}
    {Z : Spc F E (a + a')} (hV : (reS Γ.V V).IsHerm σ B (a - Γ.p) Γ.p) (hV' : (reS Γ.V' V').IsHerm σ B Γ.q (a' - Γ.q))
    (hZ : (reS Γ.W Z).IsSkew σ B (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) : (reG Γ V V' Z).IsGood B :=
  ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hZ, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
    ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩

theorem resEtaPow_quot {R K' : Type} [CommRing R] [CommRing K'] [Algebra R K'] {K : Subgroup Rˣ}
    {χ χ' : K'ˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem exists_isTriple (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} (hB : B.IsGood σ) {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {X : Chars F E}
    (c : X.IsGood B a a') : ∃ om om', IsTriple B Γ X om om' := by
  have hd : ∀ {χ χ' : Chr F E}, IsHecke F E χ → IsHecke F E χ' → IsHecke F E (χ / χ') := fun h h' =>
    ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩
  obtain ⟨om, hom⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hB a (a + a') Γ.V Γ.W _ _ _ _ g.hV g.hW Γ.M g.hM X.β (X.β / X.α)
    c.heckeβ (hd c.heckeβ c.heckeα) c.resβ (resEtaPow_quot c.resβ c.resα)
  obtain ⟨om', hom'⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hB a' (a + a') Γ.V' Γ.W _ _ _ _ g.hV' g.hW Γ.M' g.hM' X.α (X.α / X.β)
    c.heckeα (hd c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_quot c.resα c.resβ)
  exact ⟨om, om', hB, g, c, hom, hom'⟩

theorem exists_pair (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, GlobalTheory.T.real_maps_two_triples_agree hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩

theorem pair_reG (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} (hB : B.IsGood σ)
    {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {Xa Xb : Chars F E} (xa : Xa.IsGood B a a') (xb : Xb.IsGood B a a') {la lb : ℂ}
    (H : ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), IsMatched B Γ Xa om om' R Rf → IsMatched B Γ Xb om₀ om₀' R Rf₀ →
      IsConst B Γ Xa om om' R Rf c → IsConst B Γ Xb om₀ om₀' R Rf₀ c₀ →
      ∃ k : (AE F E)ˣ, c * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (c₀ * la))
    {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')} (g₂ : (reG Γ V V' Z).IsGood B) :
    ∃ oa oa' ob ob' R Ra Rb da db, IsMatched B (reG Γ V V' Z) Xa oa oa' R Ra ∧ IsMatched B (reG Γ V V' Z) Xb ob ob' R Rb ∧
      IsConst B (reG Γ V V' Z) Xa oa oa' R Ra da ∧ IsConst B (reG Γ V V' Z) Xb ob ob' R Rb db ∧ db ≠ 0 ∧
      ∃ k : (AE F E)ˣ, da * lb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * la) := by
  obtain ⟨oa, oa', ha⟩ := exists_isTriple hP hB g xa
  obtain ⟨ob, ob', hb⟩ := exists_isTriple hP hB g xb
  have ha₂ : IsTriple B (reG Γ V V' Z) Xa oa oa' := ⟨hB, g₂, xa, ha.weil, ha.weil'⟩
  have hb₂ : IsTriple B (reG Γ V V' Z) Xb ob ob' := ⟨hB, g₂, xb, hb.weil, hb.weil'⟩
  obtain ⟨R, Ra, Rb, ca, cb, m1, m2, k1, k2, hcb⟩ := exists_pair hP hK hM ha hb
  obtain ⟨R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb⟩ := exists_pair hP hK hM ha₂ hb₂
  obtain ⟨k, hk⟩ := H R oa oa' Ra ob ob' Rb ca cb m1 m2 k1 k2
  obtain ⟨k', hk'⟩ := GlobalTheory.T.real_maps_triple_coherence hP hK hM F E σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db
    m1 m2 n1 n2 k1 k2 l1 l2
  refine ⟨oa, oa', ob, ob', R₂, Sa, Sb, da, db, n1, n2, l1, l2, hdb, k * k', mul_left_cancel₀ hcb ?_⟩
  have e : ((Xa.ν (k * k') / Xb.ν (k * k') : Circle) : ℂ) =
      ((Xa.ν k / Xb.ν k : Circle) : ℂ) * ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, Circle.coe_mul]
  rw [e]
  linear_combination lb * hk' + ((Xa.ν k' / Xb.ν k' : Circle) : ℂ) * db * hk

theorem stepAlpha_cast {e₁ e₂ s : ℤˣ} (h : StepAlpha σ e₁ e₂ s) (B : Base F E) {a b a' e : ℕ} (hab : a = b + 2)
    (he : a = a' + 2 * e) (Γ : Geo σ a a') (Γ₁ : Geo σ b a') (H : Plane E a b) (H' : Plane E (a + a') (b + a'))
    (R : RealMaps F a a') (R₁ : RealMaps F b a') (h1 : Γ₁.V' = Γ.V') (h2 : Γ.q = 0) (h3 : Γ₁.q = 0) (h4 : Γ₁.p + 1 = Γ.p)
    (h5 : H.IsAdapted σ B Γ.V Γ₁.V 0 (b + 1)) (h6 : H'.IsAdapted σ B Γ.W Γ₁.W 0 (b + 1)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B Γ X om om' R Rf → IsMatched B Γ₁ X om₁ om₁' R₁ Rf₁ →
      ∀ c c₁, IsConst B Γ X om om' R Rf c → IsConst B Γ₁ X om₁ om₁' R₁ Rf₁ c₁ →
        c = C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) * charL X.ν (X.S₀ : Set (Pl F)) (e : ℂ) * c₁ := by
  subst hab
  have := h B b a' Γ Γ₁ H H' R R₁ h1 h2 h3 h4 h5 h6
  rwa [show (b + 2 - a') / 2 = e by omega] at this

end IndefiniteRowSideFullHecke

theorem gbig_both {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b :=
  gbig_of_three h₁ h₂ h₂ fun _ _ _ _ _ a b _ => ⟨a, b⟩

theorem step_identity : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (C : ℂ) (ζ : D.what₂.LL),
          GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
          lam t = C * D.what₂.embLL ζ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) *
            GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) * c t ∧
          lam μ₀ = C * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) *
            GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) * c μ₀ := by
  intro hP hK hM
  refine gbig_of_three (gbig_both GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage (GlobalTheory.T.tower_stage_fit_factor hP hK hM)) (gbig_both (GlobalTheory.T.self_dual_lattice_rank_bound hP) GlobalTheory.T.squareNu_ratio_values_roots_of_unity)
    (GlobalTheory.T.exists_factor_of_stage_triangle hP hK hM) ?_
  rintro D T Lc sc G μ₀ C x b ⟨qb, qd⟩ ⟨qs, qx⟩ qf W S hψ hN i j p A A' WW X lam e hX hF he
  obtain ⟨e₁, e₂, s, hα⟩ := hK.2.2
  obtain ⟨emb, hemb⟩ := qb W hψ i j _ _ A A' WW X hX
  obtain ⟨B₀, he₀, f₀⟩ := hemb μ₀
  obtain ⟨Γ₀, o₀, p₀, q₀, g₀, -⟩ := qd W hψ i j _ _ A A' WW X lam μ₀ B₀ hX hF f₀
  have b1 := g₀.eBig
  have b2 := g₀.aBig
  have b3 := g₀.lt
  have hV₀ := g₀.hV
  have hW₀ := g₀.hW
  rw [p₀, q₀] at b1 b2 hW₀
  rw [p₀] at hV₀
  obtain ⟨n, hn⟩ : ∃ n, A.rank = n + 2 := ⟨A.rank - 2, by omega⟩
  obtain ⟨Y', V₁, H₀, hY', hV₁, hH₀⟩ := GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace _ _ _ B₀ f₀.2.1 A.rank n hn (by omega) Γ₀.V _ _ (by omega) (by omega) hV₀
    0 (n + 1) (by omega) (by omega)
  obtain ⟨Z', W₁, H₀', hZ', hW₁, hH₀'⟩ := GlobalTheory.T.skewHermitian_selfDual_lattice_hyperbolic_plane_splitting _ _ _ B₀ f₀.2.1 (A.rank + A'.rank) (n + A'.rank) (by omega) (by omega) Γ₀.W
    _ _ (by omega) (by omega) hW₀ 0 (n + 1) (by omega) (by omega)
  obtain ⟨B, ΛB, sB, nB, oB⟩ := GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian D B₀ f₀.2.1 f₀.2.2.1 n _ _ V₁ hV₁
  obtain ⟨WW₁, ΛW, sW, nW, oW⟩ := GlobalTheory.T.exists_selfDual_orientedModel_scaled_skewHermitian D B₀ f₀.2.1 f₀.2.2.1 _ _ _ W₁ hW₁
  obtain rfl : n = B.rank := oB.1.symm
  obtain ⟨s1, s2, s3, s4, -, s6, -, s8⟩ := id hX
  obtain ⟨Y, hY, y1, y2, y3⟩ := qs W hψ i j p 0 B A' WW₁ ΛB X.rA'.Λ ΛW sB s8.rigA'.1 sW (by omega) s2 (by omega) s4
    (by simpa using nB) s6 (by simpa using nW) oW.1.symm
  obtain ⟨c, hc⟩ := qf W S hψ hN i j p 0 B A' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨B, A', WW₁, Y, c, hY, hc.isConst, fun t => ?_⟩
  obtain ⟨Bs, hes, f⟩ := hemb t
  have hee : Bs.emb = B₀.emb := hes.trans he₀.symm
  have f₁ : Fit G W i j t μ₀ Bs B.rank A'.rank := Fit.down_left (hn ▸ f)
  obtain ⟨Γ, o, pΓ, qΓ, g, HX⟩ := qd W hψ i j _ _ A A' WW X lam t Bs hX hF f
  obtain ⟨Γ₁, o₁, pΓ₁, qΓ₁, g₁, HY⟩ := qd W hψ i j _ _ B A' WW₁ Y c t Bs hY hc f₁
  obtain ⟨U, U₁, H, u1, u2, u3, u4, hH⟩ := GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis _ _ _ f.2.1.cm B₀ Bs hee _ _ _ V₁ H₀ 0 (B.rank + 1) (by omega) (by omega)
    hY'.lat hV₁.lat hH₀
  obtain ⟨Z, Z₁, H', z1, z2, z3, z4, hH'⟩ := GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis _ _ _ f.2.1.cm B₀ Bs hee _ _ _ W₁ H₀' 0 (B.rank + 1) (by omega) (by omega)
    hZ'.lat hW₁.lat hH₀'
  have eV : reS Γ.V U = reS (reS Γ₀.V Y') U := reS_congr U (o₀.1.eq o.1)
  have eW : reS Γ.W Z = reS (reS Γ₀.W Z') Z := reS_congr Z (o₀.2.2.eq o.2.2)
  have eV₁ : reS Γ₁.V U₁ = reS V₁ U₁ := reS_congr U₁ (oB.eq (y1 ▸ o₁.1))
  have eW₁ : reS Γ₁.W Z₁ = reS W₁ Z₁ := reS_congr Z₁ (oW.eq (y3 ▸ o₁.2.2))
  have eV' : reS Γ₁.V' Γ.V' = reS Γ.V' Γ.V' := reS_congr Γ.V' (o.2.1.eq (y2 ▸ o₁.2.1))
  have hV' : (reS Γ.V' Γ.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := g.hV'
  have g₂ : (reG Γ U Γ.V' Z).IsGood Bs := isGood_reG g (by rw [eV, pΓ]; exact isHerm_rebase hee hY' u1 u3) hV'
    (by rw [eW, pΓ, qΓ]; exact isSkew_rebase hee hZ' z1 z3)
  have g₃ : (reG Γ₁ U₁ Γ.V' Z₁).IsGood Bs := by
    refine isGood_reG g₁ ?_ (by rw [eV', qΓ₁, ← qΓ]; exact hV') ?_
    · rw [eV₁, pΓ₁]
      convert isHerm_rebase hee hV₁ u2 u4 using 1 <;> omega
    · rw [eW₁, pΓ₁, qΓ₁]
      convert isSkew_rebase hee hW₁ z2 z4 using 1 <;> omega
  obtain ⟨oa, oa', ob, ob', R, Ra, Rb, da, db, m1, m2, k1, k2, hdb, k, hk⟩ :=
    pair_reG hP hK hM f.2.1 g f.2.2.2.1 f.2.2.2.2.1 HX g₂
  obtain ⟨pa, pa', pb, pb', R₁, Sa, Sb, ca, cb, n1, n2, l1, l2, hcb, k', hk'⟩ :=
    pair_reG hP hK hM f.2.1 g₁ f₁.2.2.2.1 f₁.2.2.2.2.1 HY g₃
  obtain ⟨C₀, -, HC⟩ := stepAlpha_cast (hα _ _ D.sp.cm.sig) Bs hn he (reG Γ U Γ.V' Z) (reG Γ₁ U₁ Γ.V' Z₁) H H' R R₁ eV' qΓ qΓ₁
    (by show Γ₁.p + 1 = Γ.p; rw [pΓ, pΓ₁]) (by show H.IsAdapted _ _ (reS Γ.V U) (reS Γ₁.V U₁) _ _; rw [eV, eV₁]; exact hH)
    (by show H'.IsAdapted _ _ (reS Γ.W Z) (reS Γ₁.W Z₁) _ _; rw [eW, eW₁]; exact hH')
  have E1 := HC _ _ _ _ _ _ _ m1 n1 _ _ k1 l1
  have E0 := HC _ _ _ _ _ _ _ m2 n2 _ _ k2 l2
  obtain ⟨ζ, hζ, eζ⟩ := qx W S hN i j t k
  obtain ⟨ζ', hζ', eζ'⟩ := qx W S hN i j t k'
  have hz : D.what₂.embLL ζ ≠ 0 := eζ ▸ Circle.coe_ne_zero _
  have hz0 : ζ ≠ 0 := fun h => hz (by rw [h, map_zero])
  rw [eζ] at hk
  rw [eζ'] at hk'
  have hc0 := hc.1 μ₀
  refine ⟨Bs, e₁, e₂, s, H.𝔟, H'.𝔟, C₀ * lam μ₀ * cb / (db * c μ₀), ζ' * ζ⁻¹, f.1, hζ'.mul (awayUnit_inv hz0 hζ), ?_, ?_⟩
  · change da = _ * _ * charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ * _ at E1
    rw [map_mul, map_inv₀]
    generalize stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) = u at E1 ⊢
    generalize charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) = L at E1 ⊢
    field_simp
    linear_combination (-c μ₀) * hk + lam μ₀ * c μ₀ * E1 + C₀ * u * L * lam μ₀ * hk'
  · change db = _ * _ * charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ * _ at E0
    generalize stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) = u at E0 ⊢
    generalize charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (e : ℂ) = L at E0 ⊢
    field_simp
    linear_combination lam μ₀ * E0

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.Square

theorem towerStep_big : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_of_three (step_identity hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b q1 q2 q3 W S hψ hN i j p A A' WW X lam e Lf hX hF he hL
  obtain ⟨B, B', WW₁, Y, c, hY, hc, H⟩ := q1 W S hψ hN i j p A A' WW X lam e hX hF he
  have he2 := two_le_half hX he
  have hlam := hF.1
  have hne : ∀ t, Lf t e * c t ≠ 0 := fun t => by
    obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, C', ζ, -, -, et, -⟩ := H t
    rw [q3 i j t e (Lf t) he2 (hL t)] at et
    have h := hlam t
    rw [et] at h
    exact mul_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul h)) (right_ne_zero_of_mul h)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t / (Lf t e * c t), hY, hc, fun t => ⟨div_ne_zero (hlam t) (hne t), ?_⟩, fun t => ?_⟩
  · rw [mul_assoc, div_mul_cancel₀ _ (hne t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, C', ζ, hB, hζ, et, e0⟩ := H t
    rw [q3 i j t e (Lf t) he2 (hL t)] at et
    rw [q3 i j μ₀ e (Lf μ₀) he2 (hL μ₀)] at e0
    have ht := hlam t
    have h0 := hlam μ₀
    rw [et] at ht
    rw [e0] at h0
    have key := stepRatio_swap (C := C') (q2 W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (1 - (e : ℤ)) hB
      (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ht))))
      (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h0))) hζ
    beta_reduce
    rw [et, e0, mul_assoc _ (Lf t e), mul_assoc _ (Lf μ₀ e), mul_div_cancel_right₀ _ (hne t),
      mul_div_cancel_right₀ _ (hne μ₀)]
    exact key

end GlobalTheory.SqStepBig

end
end
