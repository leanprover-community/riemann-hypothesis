import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStepOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLawsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSuppBarOfNe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitPeriodTranslatesMomentsFinite
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubAddLeSpread
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPDelAtrEqLocPNabAtr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Formalism.LocalToGlobal.Columns.AtTOwedS
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatTermOfRatStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatStepOfChThOk
import Formalism.LocalToGlobal.Columns.TiedAtT
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.VecP χ ∧ B.LatAll ∧ ∀ a b, B.ThZeroMem a b := by
  first | exact @GlobalTheory.NatFamily.family | exact GlobalTheory.NatFamily.family | (intros; apply GlobalTheory.NatFamily.family <;> assumption)
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

open Formalism.MainNotions.TaylorLogMetric in

theorem jetMoments_of_unitPeriod
    (hM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc →
      IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 →
      jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p →
      ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω)
    (hE : MovesAll) (hL : LatticeFactsAll) : JetMoments := by
  intro D hD H s cc δ B χ cD ⟨hs, _, hcc, hδ, hχ, hcD⟩ u _ hcop w ι hw
  classical
  obtain ⟨lam, hlam⟩ := (_root_.GlobalTheory.MomPlace.places D.X.K (D.Pr.T u) s.σ₀ ι).1
  obtain ⟨⟨hTs, hTq⟩, -⟩ : (D.Pr.T u ∉ H.host.small ∧ D.Pr.T u ≠ H.host.q) ∧
      ∀ i, D.Pr.g i ∉ H.host.small ∧ D.Pr.g i ≠ H.host.q :=
    ⟨(_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).1 u, (_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).2⟩
  have hT2 : D.Pr.T u ≠ 2 := UpperTheory.Small.ne_two H.host hTs
  have hP := hD.primes
  have hp := hP.T_prime u
  have hn := hP.piT_norm u
  obtain ⟨Ω, hΩ, hmom⟩ := hM H cc δ B χ hcc hδ hχ (D.Pr.T u) lam hT2
    ((_root_.GlobalTheory.MomT.SplitK.splitk H D.X s (D.Pr.piT u) _ hs (hP.piT_Kq u)).2 hp hT2 hn (hP.piT_cop u)) hcop
  obtain ⟨M, _, hMe, hMs⟩ := hcD
  have hcQ : ∀ τ, cD τ ∈ TaylorLogMetric.Qbar := by
    intro τ
    obtain ⟨x, hx, -⟩ := hMs τ
    rw [← hx]
    exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (algebraMap M ℂ).toRatAlgHom)
  refine ⟨fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω, fun τ => ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := hMs (s.iT τ)
    rw [norm_div, hΩ, div_one, ← hx]
    exact GlobalTheory.EigenGenerator.norm_generator_eq_one H _ lam hTs hTq M hMe _ x hx'
  intro sel S mu cst hsel hS hcq i b _ hb SG SG' d d' hd hd' Ξ₀ hΞ
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have ha := hev i
  have hb' : Even b := hb ▸ hev _
  obtain ⟨hla, hsm⟩ := hL H D.X s cc δ B χ cD hD.fields hs hcc hδ hχ _ _ ha hb'
  have hπ0 : D.Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : D.X.conjO (D.Pr.piT u) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  obtain ⟨hfree, hrow⟩ := _root_.GlobalTheory.Proof.AbsNormSplitPlace.main D u sel S mu hD hsel (hS (Or.inr ⟨u, rfl⟩))
    (fun k => hS (Or.inl (by fin_cases k <;> simp)))
  have hUT : ∀ P : HeightOneSpectrum (𝓞 D.X.E), ((D.Pr.T u : ℕ) : 𝓞 D.X.E) ∈ P.asIdeal →
      localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 D.X.E) D.X.E) :=
    fun P h => _root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.1 H D.X s cc δ B χ cD P _ hp hTs hTq h hcop
  have hmemS : ∀ P, P ∈ Sall sel mu u ↔ D.Pr.piT u ∈ P.asIdeal ∨ P ∈ rowSG D.Pr sel mu := by
    intro P
    unfold Sall
    rw [Finset.mem_union, Primes.vT, mem_divs hπ0]
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
    intro P hPS
    rcases (hmemS P).1 hPS with h | h
    · exact hUT P (hn ▸ Ideal.mul_mem_right _ _ h)
    · have bad := _root_.GlobalTheory.ThetaMove.BadPrimes.bad_primes D.X D.Pr sel S mu u hD.fields hP hsel (hS (Or.inr ⟨u, rfl⟩))
        (fun k => hS (Or.inl (by fin_cases k <;> simp))) P hPS
      exact _root_.GlobalTheory.PeriodIdealUnit.locP_AA_eq_one D.X H s cc δ B χ cD P bad.2.1 bad.2.2.1 (hcq P h)
  have hG : Nat.Coprime (∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => (Nat.coprime_primes (hrow P.1 P.2).1 hp).2 (hrow P.1 P.2).2.1
  have hctx : Ctx (ambOf s B χ cD) (D.R.N i) b (Sall sel mu u) (rowSG D.Pr sel mu) (D.Pr.piT u) (D.Pr.T u)
      ((∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) ^ cst.B) (cAof sel mu cst) :=
    ⟨hD.fields, ⟨hla.1, hla.2.1, hfree, hU, hla.2.2.2.2⟩,
      fun P h => hUT P (hn ▸ Ideal.mul_mem_left _ _ ((mem_divs hπ0' P).1 h)), hsm, hp, hn, hP.piT_cop u, hmemS,
      fun P h => (hrow P h).2.2.1, hG.pow_left _, hG.pow_left _⟩
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨c1, c1'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d.1.N hD.fields hs hχ hn hN
    fun P h => hd ⟨P, (mem_divs hπ0 P).2 h⟩
  obtain ⟨c2, c2'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d'.1.N hD.fields hs hχ hn hN'
    fun P h => hd' ⟨P, (mem_divs hπ0 P).2 h⟩
  have hF : (ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  have hF1 : ‖TaylorLogMetric.lamC lam ((ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N)‖ = 1 := by
    refine (congrArg norm (lamC_mul lam (zpow_mem c1 _) (zpow_mem c2 _))).trans ?_
    rw [lamC_zpow lam c1, lamC_zpow lam c2, norm_mul, norm_zpow, norm_zpow, c1', c2', one_zpow, one_zpow, one_mul]
  refine ⟨fun hseen => ?_, fun hseen => ?_⟩
  · refine type_bar hctx hlam hw d d' hF hF1 Ξ₀ hΞ ?_
    have := _root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.X.conjO (D.Pr.piT u)) (D.R.N i) b hD.fields hs hcc hT2 hcop
      (fun k => (hlam k).2) hcQ (fun τ τ' => ?_) (by rw [conjO_conjO, mul_comm, hn])
      (by rw [conjO_conjO]; exact (hP.piT_cop u).symm) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rwa [e, star_star] at this
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rw [e, hD.fields.emb_star, hD.fields.emb_star, hP.piT_Kq u τ τ']
  · have hsq : ∀ P ∈ divs (D.Pr.piT u), D.Pr.piT u ∉ P.asIdeal ^ 2 := by
      intro P hPm h2
      refine GlobalTheory.SplitUnram.natCast_notMem_sq D.X.E D.X.conjO (D.Pr.piT u) _ conjO_conjO hp hn (hP.piT_cop u) ?_
        (hP.vT_norm u) P hPm (hn ▸ Ideal.mul_mem_right _ _ h2)
      have h1 : (divs (D.Pr.piT u)).card = Module.finrank ℚ D.X.F := (hP.vT_card u).trans hD.fields.card_Tau
      rw [h1, ← Module.finrank_mul_finrank ℚ D.X.F D.X.E, hD.fields.rankE, mul_comm]
    obtain ⟨N'', hN'', hc⟩ := _root_.GlobalTheory.MomT.MomentCompanion.companion D.X b SG' (D.Pr.piT u) d' hD.fields hπ0 (hP.piT_cop u) hsq
    have hval := _root_.GlobalTheory.MomT.ChiMove.chi_move H D.X s χ b SG' (D.Pr.piT u) d' N'' hD.fields hs hχ hπ0 (hP.piT_cop u) hsq hN'' hc
    set k : D.X.K := ∏ τ, (D.X.emb τ (((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) / star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E)))⁻¹ with hk
    have hval' : χ (TaylorLogMetric.detId H (s.lat d'.1.N) (s.lat N'')) = s.σ₀ k := by
      rw [hval, hk, map_prod]
      exact Finset.prod_congr rfl fun τ _ => (map_inv₀ _ _).symm
    have hk0 : k ≠ 0 := by
      have h0 : ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) ≠ 0 := by exact_mod_cast hπ0
      exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero ((map_ne_zero _).2 (div_ne_zero h0 (star_ne_zero.2 h0)))
    have hkn : ‖ι k‖ ≤ (D.Pr.T u : ℝ) ^ D.X.f := by
      rw [hk, map_prod, norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_).trans_eq
        (Finset.prod_const (D.Pr.T u : ℝ))
      rw [map_inv₀]
      exact norm_ratio_le (ι.comp (D.X.emb τ)) hn
    have hcard : (divs (D.Pr.piT u)).card = D.X.f := hP.vT_card u
    have key := type_p hctx hlam hw d d' hd hF hF1 Ξ₀ hΞ
      (_root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.Pr.piT u) (D.R.N i) b hD.fields hs hcc hT2 hcop
        (fun k => (hlam k).2) hcQ (hP.piT_Kq u) hn (hP.piT_cop u) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom)
      (hP.vT_norm u) N'' hN'' hc (s.σ₀ (k ^ (D.R.N i / 2))) (hlam _).1 ?_ ?_
    · rw [hcard] at key
      exact key
    · rw [(hlam _).2, map_pow, norm_pow, ← pow_mul, Nat.div_two_mul_two_of_even ha, hcard, pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hkn _
    · intro R hR z
      have hmv := _root_.GlobalTheory.MomT.Move.move H D.X s cc δ B χ cD _ b d.1.N d'.1.N N'' hD.fields hs (hE H cc δ B χ hcc hδ hχ) ha hb' hla
        hN hN' hN'' R hR z
      have hR0 : ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨x, hx, -⟩ := hR.2.2 0 (zero_mem _)
        have : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
        exact_mod_cast (Real.sqrt_pos.2 this).ne'
      have hσ : s.σ₀ k ≠ 0 := (map_ne_zero _).2 hk0
      rw [hmv, hval', map_pow, zpow_neg, zpow_natCast]
      field_simp

end GlobalTheory.MomT
end
end

section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
end
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomTop

theorem jetMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments :=
  GlobalTheory.MomT.jetMoments_of_unitPeriod
    (GlobalTheory.T.unitPeriodTranslates_moments_finite GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomEq.eq_and_alg.2)
    GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomLat.latticeFactsAll

end GlobalTheory.MomTop
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelJets_levelPlace_integralMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments := by
  atlas_forward_decl GlobalTheory.MomTop.jetMoments
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open scoped Matrix

noncomputable section

namespace GlobalTheory.BarStd

open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (adj suppBar StdAtT InIntClosure Induces jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis detFac extLat admitted InClosure ptTable)
open GlobalTheory.CharVal (intAt_iff valuation_conjP conjP_conjP')

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n a b : ℕ}

theorem mem_localization_dual {M : Submodule (𝓞 E) (Sp E n)} (hM : M.FG) (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal (dual (hStd E n) M) ↔
      ∀ y ∈ localization₂ P.asIdeal M, (conjPrime₂ P).valuation E (hStd E n y x) ≤ 1 := by
  constructor
  · intro hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP _ _ _).1 hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((mem_dual _ _).1 hsx _ hty)
    refine (intAt_iff _).1 ⟨r, cO E t * s, fun h => ((conjPrime₂ P).isPrime.mem_or_mem h).elim
      (fun h' => ht (by rwa [mem_conjP, cO_cO] at h')) hs, ?_⟩
    rw [hr, hStd_osmul_left, ← mul_smul, ← algebraMap_smul E (cO E t * s) x, map_smul, smul_eq_mul]
  · intro H
    let M' : Submodule (𝓞 E) (Sp E n) := (1 : Submodule (𝓞 E) E).comap ((hStd E n x).restrictScalars (𝓞 E))
    have h1 : localization₂ P.asIdeal M ≤ localization₂ P.asIdeal M' := by
      intro y hy
      have h2 := H y hy
      rw [valuation_conjP, ← starRingEnd_apply, hStd_isSymm.eq] at h2
      obtain ⟨r, s, hs, e⟩ := (intAt_iff _).2 h2
      refine (mem_locP _ _ _).2 ⟨s, hs, ?_⟩
      change hStd E n x (s • y) ∈ (1 : Submodule (𝓞 E) E)
      rw [← algebraMap_smul E s y, map_smul, smul_eq_mul, e]
      exact Submodule.mem_one.2 ⟨r, rfl⟩
    obtain ⟨c, hc, hcM⟩ := GlobalTheory.StdReps.exists_smul_of_le hM h1
    refine (mem_locP _ _ _).2 ⟨cO E c, by rwa [mem_conjP, cO_cO], (mem_dual _ _).2 fun y hy => ?_⟩
    rw [← hStd_osmul_left]
    exact hStd_mem_one_symm (hcM y hy)

omit [NumberField E] in
theorem hStd_mulVec (A : Matrix (Fin b) (Fin a) E) (z : Sp E a) (x : Sp E b) :
    hStd E b (A *ᵥ z) x = hStd E a z (Aᴴ *ᵥ x) := by
  change star (A *ᵥ z) ⬝ᵥ x = star z ⬝ᵥ (Aᴴ *ᵥ x)
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

omit [NumberField E] in
theorem hStd_adj (x : HomE E a b) (l : Sp E a) (y : Sp E b) : hStd E a l (adj x y) = hStd E b (x l) y := by
  rw [adj, Matrix.toLin'_apply, ← hStd_mulVec, LinearMap.toMatrix'_mulVec]

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

theorem adj_mem (d : DecoSet E a ST SG) (d' : DecoSet E b ST SG') {x : HomE E a b} (hx : x ∈ suppBar d.1 d'.1) (P : ST)
    {y : Sp E b} (hy : y ∈ d'.1.Lsh) : adj x y ∈ localization₂ (conjPrime₂ P.1).asIdeal d.1.Lsh := by
  rw [Deco.Lsh, mem_localization_dual d.2.L_lattice.fg]
  intro l hl
  rw [hStd_adj]
  refine (mem_localization_dual d'.2.L_lattice.fg P.1 y).1 (le_locP _ _ hy) _ ?_
  rw [d.2.mem_locP_L] at hl
  rw [d'.2.mem_locP_L]
  exact ⟨(hx P l hl.1).1, (hx P l hl.1).2.trans hl.2⟩

omit [StarRing E] in
theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) : x ∈ stdAt E n P ↔ ∀ i, P.valuation E (x i) ≤ 1 := by
  let _ : StarRing E := starRingOfComm
  rw [stdAt, mem_localization_standardLattice]
  exact forall_congr' fun i => intAt_iff _

theorem exists_coeff (d : DecoSet E n ST SG) (P : ST) (h : d.1.at P.1 = stdAt E n P.1) :
    ∃ c : Fin n → 𝓞 E, ∀ x ∈ stdAt E n P.1,
      (d.1.f P x = 0 ↔ P.1.valuation E (∑ j, algebraMap (𝓞 E) E (c j) * x j) < 1) := by
  classical
  choose c hc using fun j : Fin n => Ideal.Quotient.mk_surjective (d.1.f P (Pi.single j 1))
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
  choose r hr using (mem_stdLat _).1 hsx
  have he : ∀ j, (Pi.single j (1 : E) : Sp E n) ∈ d.1.at P.1 := fun j => by
    rw [h]
    exact le_locP _ _ (by simpa using single_mem_stdLat (E := E) j 1)
  have h1 : ∀ F : Finset (Fin n), d.1.f P (∑ j ∈ F, r j • (Pi.single j (1 : E) : Sp E n)) =
      Ideal.Quotient.mk P.1.asIdeal (∑ j ∈ F, c j * r j) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using d.2.f_zero P
    | insert j F hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, d.2.f_add P _ (Submodule.smul_mem _ _ (he j)) _
        (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (he k)), ih, d.2.f_smul P _ _ (he j), ← hc, map_add,
        map_mul, mul_comm]
  have h2 : s • x = ∑ j, r j • (Pi.single j (1 : E) : Sp E n) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
  have h3 := d.2.f_smul P s x (h ▸ hx)
  rw [h2, h1] at h3
  have h4 : algebraMap (𝓞 E) E (∑ j, c j * r j) = algebraMap (𝓞 E) E s * ∑ j, algebraMap (𝓞 E) E (c j) * x j := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hr, Pi.smul_apply, Algebra.smul_def]
    ring
  have h5 : P.1.valuation E (algebraMap (𝓞 E) E s) = 1 := (P.1.valuation_eq_one_iff_notMem).2 hs
  have h6 : P.1.valuation E (algebraMap (𝓞 E) E (∑ j, c j * r j)) < 1 ↔ _ :=
    P.1.valuation_lt_one_iff_mem (K := E) (∑ j, c j * r j)
  rw [h4, map_mul, h5, one_mul] at h6
  rw [h6, ← Ideal.Quotient.eq_zero_iff_mem, h3, mul_eq_zero, or_iff_right (mk_ne_zero hs)]

theorem exists_matrix_ker (d : DecoSet E n ST SG) (P : ST) (h : d.1.at P.1 = stdAt E n P.1) {q : E}
    (hq : P.1.valuation E q = WithZero.exp (-1 : ℤ)) :
    ∃ A : Matrix (Fin n) (Fin n) E, P.1.valuation E (q * A.det) = 1 ∧
      ∀ x, x ∈ localization₂ P.1.asIdeal d.1.L ↔ A *ᵥ x ∈ stdAt E n P.1 := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff d P h
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  obtain ⟨k, hk⟩ : ∃ k, c k ∉ P.1.asIdeal := by
    by_contra H
    push Not at H
    obtain ⟨x, hx, hne⟩ := d.2.f_ne P
    have hx' : x ∈ stdAt E n P.1 := h ▸ le_locP _ _ hx
    refine hne ((hc x hx').2 (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_))
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le ((P.1.valuation_lt_one_iff_mem (K := E) _).2 (H j)) ((mem_stdAt _ _).1 hx' j)
  have hk1 : P.1.valuation E (algebraMap (𝓞 E) E (c k)) = 1 := (P.1.valuation_eq_one_iff_notMem).2 hk
  have hlt : ∀ z : E, P.1.valuation E (q⁻¹ * z) ≤ 1 ↔ P.1.valuation E z < 1 := by
    intro z
    rw [map_mul, map_inv₀, hq, inv_mul_le_one₀ WithZero.exp_pos]
    by_cases hz : P.1.valuation E z = 0
    · simp [hz]
    · rw [← WithZero.exp_log hz, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_lt_exp]
      omega
  let A : Matrix (Fin n) (Fin n) E := (1 : Matrix (Fin n) (Fin n) E).updateRow k fun j => q⁻¹ * algebraMap (𝓞 E) E (c j)
  have hA1 : ∀ x : Sp E n, (A *ᵥ x) k = q⁻¹ * ∑ j, algebraMap (𝓞 E) E (c j) * x j := by
    intro x
    simp only [A, Matrix.mulVec, dotProduct, Matrix.updateRow_self, Finset.mul_sum, mul_assoc]
  have hA2 : ∀ (x : Sp E n) j, j ≠ k → (A *ᵥ x) j = x j := by
    intro x j hj
    simp [A, Matrix.mulVec, dotProduct, Matrix.updateRow_ne hj, Matrix.one_apply]
  refine ⟨A, ?_, fun x => ?_⟩
  · have e : (fun j => q⁻¹ * algebraMap (𝓞 E) E (c j)) =
        ∑ j, (q⁻¹ * algebraMap (𝓞 E) E (c j)) • (1 : Matrix (Fin n) (Fin n) E) j := by
      funext l
      simp [Finset.sum_apply, Matrix.one_apply]
    simp only [A]
    rw [e, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one, mul_inv_cancel_left₀ hq0, hk1]
  · rw [d.2.mem_locP_L, h]
    constructor
    · rintro ⟨h1, h2⟩
      rw [mem_stdAt]
      intro j
      by_cases hj : j = k
      · rw [hj, hA1, hlt]
        exact (hc x h1).1 h2
      · rw [hA2 x j hj]
        exact (mem_stdAt _ _).1 h1 j
    · intro H
      rw [mem_stdAt] at H
      have h1 := H k
      rw [hA1, hlt] at h1
      have h2 : x ∈ stdAt E n P.1 := by
        rw [mem_stdAt]
        intro j
        by_cases hj : j = k
        · subst hj
          have h3 : algebraMap (𝓞 E) E (c j) * x j = (∑ l, algebraMap (𝓞 E) E (c l) * x l) -
              ∑ l ∈ Finset.univ.erase j, algebraMap (𝓞 E) E (c l) * x l := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_right]
          have h4 : P.1.valuation E (algebraMap (𝓞 E) E (c j) * x j) ≤ 1 := by
            rw [h3]
            refine Valuation.map_sub_le _ h1.le (Valuation.map_sum_le _ fun l hl => ?_)
            rw [map_mul, ← hA2 x l (Finset.ne_of_mem_erase hl)]
            exact mul_le_one' (P.1.valuation_le_one _) (H l)
          rwa [map_mul, hk1, one_mul] at h4
        · rw [← hA2 x j hj]
          exact H j
      exact ⟨h2, (hc x h2).2 h1⟩

theorem isBasisAt_of (Q : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) (B : GL (Fin n) E)
    (h : ∀ z, (B : Matrix (Fin n) (Fin n) E) *ᵥ z ∈ localization₂ Q.asIdeal M ↔ z ∈ stdAt E n Q) : IsBasisAt Q M B := by
  classical
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (M' := (B : Matrix (Fin n) (Fin n) E)) (Units.inv_mul B) (Units.mul_inv B)
  have hf : ∀ x, f x = (B : Matrix (Fin n) (Fin n) E) *ᵥ x := fun x => rfl
  have e : colLat B = gmap f (stdLat E n) := by
    rw [stdLat_eq_span]
    unfold gmap colLat
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j i
    simp [hf]
  ext y
  rw [e, mem_localization_gmap, ← f.apply_symm_apply y, hf, h, ← hf, f.symm_apply_apply]
  rfl

theorem exists_basis_Lsh (d : DecoSet E n ST SG) (P : ST) (h : d.1.at P.1 = stdAt E n P.1) {q : ℕ}
    (hq : P.1.valuation E (q : E) = WithZero.exp (-1 : ℤ)) :
    ∃ B : GL (Fin n) E, IsBasisAt (conjPrime₂ P.1) d.1.Lsh B ∧
      (conjPrime₂ P.1).valuation E (q * (B : Matrix (Fin n) (Fin n) E).det) = 1 := by
  obtain ⟨A, hA, hL⟩ := exists_matrix_ker d P h hq
  have hA0 : A.det ≠ 0 := by
    intro h0
    simp [h0] at hA
  have hB0 : Aᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hA0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hB0, isBasisAt_of _ _ _ fun z => ?_, ?_⟩
  · change Aᴴ *ᵥ z ∈ _ ↔ _
    rw [Deco.Lsh, mem_localization_dual d.2.L_lattice.fg, stdAt, ← show dual (hStd E n) (stdLat E n) = _ from stdLat_unimodular,
      mem_localization_dual stdLat_lattice.fg]
    constructor
    · intro H m hm
      obtain ⟨l, rfl⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA0.isUnit)) m
      rw [hStd_mulVec]
      exact H l ((hL l).2 hm)
    · intro H l hl
      rw [← hStd_mulVec]
      exact H _ ((hL l).1 hl)
  · change (conjPrime₂ P.1).valuation E (q * Aᴴ.det) = 1
    rw [valuation_conjP, Matrix.det_conjTranspose, star_mul', star_star, star_natCast, hA]

end Lat

section Closure

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

theorem finite_inDeg {ι : Type} [Fintype ι] (lam : ι → DomWeight a) (s' : ι → ℤ) :
    {m : DVar ι a b →₀ ℕ | InDeg lam s' m}.Finite := by
  refine (Finsupp.finite_of_degree_le (∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ)).toNat).subset fun m hm => ?_
  have h : (m.degree : ℤ) = ∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ) := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [← hm τ, Fintype.sum_prod_type]
  rw [Set.mem_setOf_eq, ← h, Int.toNat_natCast]

theorem val_le_one_iff {ι : X.K →+* ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)} (h : Induces ι w) (x : X.K) :
    NormedField.valuation (ι x) ≤ 1 ↔ w.valuation X.K x ≤ 1 := by
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact ⟨GlobalTheory.DatumJets.Place.valuation_le_one_of_norm ι w h x, GlobalTheory.MomPlace.norm_le_one_of_valuation X.K p ι w h x⟩

def ptMat (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (x : HomE X.E a b) (τ : X.Tau) : Matrix (Fin a) (Fin b) ℂ_[p] :=
  Matrix.of fun α β => un τ * ι (X.emb τ (adj x (Pi.single β 1) α))

theorem ptMat_mulVec (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (x : HomE X.E a b) (τ : X.Tau) (y : Sp X.E b) :
    ptMat ι un x τ *ᵥ (fun i => ι (X.emb τ (y i))) = un τ • fun i => ι (X.emb τ (adj x y i)) := by
  funext α
  conv_rhs => rw [← LinearMap.toMatrix'_mulVec]
  simp only [ptMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    LinearMap.toMatrix'_apply, Finset.mul_sum, mul_assoc]

theorem admissible_adjointRationalPointPadicMatrix {ι : X.K →+* ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)} (h : Induces ι w) {un : X.Tau → ℂ_[p]}
    (hun : ∀ τ, ‖un τ‖ = 1) {L : Submodule (𝓞 X.E) (Sp X.E a)} {L' : Submodule (𝓞 X.E) (Sp X.E b)} {x : HomE X.E a b}
    (hx : ∀ τ, ∀ y ∈ L', adj x y ∈ localization₂ (pullW τ w).asIdeal L) :
    admitted NormedField.valuation ι (fun τ => tauLat X.emb τ L) (fun τ => tauLat X.emb τ L') (ptMat ι un x) := by
  intro τ y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    beta_reduce
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      beta_reduce
      rw [ptMat_mulVec]
      have h1 : (fun i => X.emb τ (adj x l i)) ∈ localization₂ w.asIdeal (tauLat X.emb τ L) := by
        obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 (hx τ l hl)
        refine (mem_locP _ _ _).2 ⟨X.embO τ s, hs, Submodule.subset_span ⟨_, hsx, ?_⟩⟩
        exact bc_bcV_osmul (X.emb τ) s _
      have h2 : NormedField.valuation (un τ) ≤ 1 := by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, hun, NNReal.coe_one]
      exact Submodule.smul_mem _ (⟨un τ, h2⟩ : (NormedField.valuation (K := ℂ_[p])).integer)
        (GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (val_le_one_iff h) _ _ h1)
    | zero =>
      have : (fun i => ι ((0 : Fin b → X.K) i)) = 0 := by funext i; simp
      rw [this, Matrix.mulVec_zero]
      exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : (fun i => ι ((z + z') i)) = (fun i => ι (z i)) + fun i => ι (z' i) := by funext i; simp
      rw [this, Matrix.mulVec_add]
      exact add_mem hz hz'
    | smul c z _ hz =>
      have : (fun i => ι ((c • z) i)) = ι (c : X.K) • fun i => ι (z i) := by
        funext i
        exact map_mul ι (c : X.K) (z i)
      rw [this, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ (⟨ι (c : X.K), (val_le_one_iff h _).2 (w.valuation_le_one c)⟩ :
        (NormedField.valuation (K := ℂ_[p])).integer) hz
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy

theorem jetOp_of_closure {ι : X.K →+* ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)} (h : Induces ι w) {un : X.Tau → ℂ_[p]}
    (hun : ∀ τ, ‖un τ‖ = 1) {hab : a < b} {lam : X.Tau → DomWeight a} {lam' : X.Tau → DomWeight b} {s s' : X.Tau → ℤ}
    {n : X.Tau → ℕ} (hw : WtCompat hab lam lam' s s' n) {L : Submodule (𝓞 X.E) (Sp X.E a)} {L' : Submodule (𝓞 X.E) (Sp X.E b)}
    (hL : Submodule.IsLattice X.E L) (hL' : Submodule.IsLattice X.E L') {B : X.Tau → GL (Fin a) X.E} {B' : X.Tau → GL (Fin b) X.E}
    (hB : ∀ τ, IsBasisAt (pullW τ w) L (B τ)) (hB' : ∀ τ, IsBasisAt (pullW τ w) L' (B' τ)) {Sup : Set (HomE X.E a b)}
    (hS : ∀ x ∈ Sup, ∀ τ, ∀ y ∈ L', adj x y ∈ localization₂ (pullW τ w).asIdeal L) (κ : X.K) {M : Set (DVar X.Tau a b →₀ ℕ)}
    (hM : ∀ m, InDeg lam s' m → m ∈ M) {J : (DVar X.Tau a b →₀ ℕ) → X.K}
    (hJ : InIntClosure Sup (fun x m => ι κ * GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.ptTab ι un x m) M fun m => ι (J m)) :
    ∀ F ∈ localization₂ w.asIdeal (nabAtr X.emb lam L), ∃ G ∈ localization₂ w.asIdeal (nabAtr X.emb lam' L'),
      jetOp lam lam' J n F =
        (κ * detFac s s' (fun τ => Formalism.UG.bc (X.emb τ) (B τ)) fun τ => Formalism.UG.bc (X.emb τ) (B' τ)) • G := by
  classical
  let _ : StarRing X.K := starRingOfComm
  refine GlobalTheory.JetPoint.closureIntegral X.K w ℂ_[p] _ NormedField.valuation ι (val_le_one_iff h) X.Tau a b hab lam lam' s s' n hw
    (fun τ => tauLat X.emb τ L) (fun τ => tauLat X.emb τ L') _ _
    (fun τ => ⟨(GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ L hL).fg, bc_isBasisAt (X.emb τ) w (hB τ)⟩)
    (fun τ => ⟨(GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ L' hL').fg, bc_isBasisAt (X.emb τ) w (hB' τ)⟩) κ J
    fun ε hε => ?_
  obtain ⟨c, hc1, hc2, hc3⟩ := hJ (finite_inDeg lam s').toFinset (fun m hm => hM m (by simpa using hm)) ‖ι ε‖
    (norm_pos_iff.2 ((map_ne_zero ι).2 hε))
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun i => c (e i), fun i => ptMat ι un (e i), fun i => ?_,
    fun i => admissible_adjointRationalPointPadicMatrix h hun (hS _ (hc1 (e i).2)), fun m hm => ?_⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact hc2 _
  · rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    refine le_of_eq_of_le ?_ (hc3 m (by simpa using hm)).le
    congr 2
    rw [Finsupp.sum, ← Finset.sum_coe_sort c.support, ← e.sum_comp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

end Closure

section Step

variable {X : Fields} {Pr : Primes X}

theorem unramOver {S : Set ℕ} (mu : Tup X.F X.E X.K S) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) :
    GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.UnramOver (mu : Chr X.F X.E X.K) l := by
  intro v h5 hv
  have hgood : GoodPl X.E S v := by
    by_contra hn
    exact hv (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hn)
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem stdOver (hPr : Pr.Ok) {u : Pr.Word} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (d : DecoSet X.E n (Pr.vT u) SG) (h : StdAtT d.1) : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (Pr.T u) d.1.N := by
  intro P hP
  rw [← hPr.piT_norm u] at hP
  rcases P.isPrime.mem_or_mem hP with h1 | h1
  · exact h ⟨P, (mem_divs (hPr.piT_ne_zero u) _).2 h1⟩
  · have h2 := GlobalTheory.StdReps.at_conj_eq d (h ⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 h1⟩)
    rwa [conjP_conjP'] at h2

theorem sub_eq_half {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) {hab : R.N i < R.N (i + 1)}
    {s s' : X.Tau → ℤ} {n : X.Tau → ℕ} (hw : WtCompat hab (W.lamTrue u i) (W.lamTrue u (i + 1)) s s' n) (τ : X.Tau) :
    s τ - s' τ = ((R.t + 1) / 2 : ℕ) := by
  have h1 := congrArg (Int.cast : ℤ → ℚ) (hw.1 τ ⟨0, R.N_pos i⟩)
  have h2 : _ = ((W.lamTrue u i τ).w ⟨0, R.N_pos i⟩ : ℚ) + _ - _ :=
    W.lamTrue_old u hi τ (Fin.castLE hab.le ⟨0, R.N_pos i⟩) (R.N_pos i)
  have h3 := cast_t_add_one_div_two R
  push_cast at h1
  rw [h2] at h1
  unfold sExp sExp' Ranks.N at h1
  rw [Nat.add_sub_cancel] at h1
  have h4 : ((s τ - s' τ : ℤ) : ℚ) = ((((R.t + 1) / 2 : ℕ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, h3]
    push_cast at h1 ⊢
    linarith
  exact_mod_cast h4

end Step

theorem barStd : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) → AlcoveAt Z.W u (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), seenBarC Z.Pr u w → ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y' := by
  intro hJM hP Z H s cc δ B χ cD sel S mu cst u i hi hyp hJ hAl w hw SG SG' d fr d' fr' Ξ₀ hstd hfr hfr' hbox hint y hy
  classical
  have hX := hyp.ok.fields
  have hPr := hyp.ok.primes
  haveI : Fact (Z.Pr.T u).Prime := ⟨hPr.T_prime u⟩
  have hTw := hw.T_mem hX hPr
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  have hv : ∀ τ, conjPrime₂ (pullW τ w) ∈ Z.Pr.vT u := fun τ => (conjP_pullW_mem_vT_iff hPr u τ w).2 (hw τ)

  obtain ⟨ι, hι⟩ := GlobalTheory.DatumJets.Place.exists_embedding (p := Z.Pr.T u) w hTw
  have hind : Induces ι w := fun y => by rw [hι]; rfl
  have hcop : Nat.Coprime (Ideal.absNorm cc) (Z.Pr.T u) := by
    obtain ⟨τ⟩ := hX.nonempty_Tau
    rw [← hPr.vT_norm u _ (hv τ)]
    exact hyp.cop _ (Finset.mem_union_left _ (hv τ))
  obtain ⟨un, hun, hmom⟩ := hJM Z hyp.ok H s cc δ B χ cD hyp.ana u hcop w ι hind
  have hclo := (hmom sel S mu cst hyp.isSel hyp.host (fun P hP => hyp.cop P (Finset.mem_union_right _ hP)) i _ hi rfl SG SG'
    d d' hstd.1 hstd.2 Ξ₀ (fun x _ => ⟨hint x, hbox.2 x⟩)).1 hw

  obtain ⟨m0, eta, ht, hq⟩ := hyp.tied
  have hscal := (((GlobalTheory.CharVal.charValAtT Z H s χ u hyp.ok hyp.ana.1 hyp.ana.2.1 hyp.ana.2.2.2.2.1 hyp.chiK).2.2 m0 eta ht sel
    hyp.isSel S mu (unramOver mu (hPr.T_prime u) (hyp.host (Or.inr ⟨u, rfl⟩)))
    (fun k => unramOver mu (hPr.g_prime k) (hyp.host (Or.inl (by fin_cases k <;> simp)))) cst hq ⟨i, hi⟩).1 w hTw).1.2
    _ _ d.1.N fr d'.1.N fr' hsd hsd' (stdOver hPr d hstd.1) (stdOver hPr d' hstd.2) hfr hfr'

  obtain ⟨σ, σ', hwt, -⟩ := GlobalTheory.ColPeriod.chainWeights Z.X Z.Pr Z.R Z.W u i hi
  have hval := fun τ => (GlobalTheory.CharVal.splitOver_vT hX hPr u (hv τ)).val
  choose Bs hBs hBd using fun τ => exists_basis_Lsh d ⟨_, hv τ⟩ (hstd.1 _) (hval τ)
  choose Bt hBt hBd' using fun τ => exists_basis_Lsh d' ⟨_, hv τ⟩ (hstd.2 _) (hval τ)
  simp only [conjP_conjP'] at hBs hBd hBt hBd'
  obtain ⟨G, hG, hGe⟩ := jetOp_of_closure hind hun hwt d.2.Lsh_lattice d'.2.Lsh_lattice hBs hBt (Sup := suppBar d.1 d'.1)
    (fun x hx τ y hy => by
      have := adj_mem d d' hx ⟨_, hv τ⟩ hy
      rwa [conjP_conjP'] at this) 1
    (M := RatIdx (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
      fun x => phiT Z.X.K d.1 d'.1 x * Ξ₀ x)
    (fun m hm x hx _ => hJ _ _ hsd hsd' x hx m fun τ => by
      refine (hm τ).trans (Finset.sum_congr rfl fun a _ => ?_)
      rw [hwt.2.2 τ]
      ring)
    (by simpa only [map_one, one_mul] using hclo) y
    (localization_mono _ (Submodule.comap_mono (usage₁₁ _ _)) hy)
  rw [← GlobalTheory.KerT.localization_delAtr_eq_localization_nabAtr hP Z.X _ _ _ (hPr.T_prime u) hAl w hTw _ d'.2.Lsh_lattice] at hG
  have hT0 : (Z.Pr.T u : Z.X.K) ≠ 0 := Nat.cast_ne_zero.2 (hPr.T_prime u).ne_zero
  have hvT : w.valuation Z.X.K (Z.Pr.T u) ≠ 0 := by simpa using hT0
  have hdet : ∀ {n : ℕ} (τ : Z.X.Tau) (C : GL (Fin n) Z.X.E),
      (pullW τ w).valuation Z.X.E (Z.Pr.T u * (C : Matrix (Fin n) (Fin n) Z.X.E).det) = 1 →
      w.valuation Z.X.K ((Formalism.UG.bc (Z.X.emb τ) C : GL (Fin n) Z.X.K) : Matrix (Fin n) (Fin n) Z.X.K).det =
        (w.valuation Z.X.K (Z.Pr.T u))⁻¹ := by
    intro n τ C hC
    have h1 := GlobalTheory.CharVal.val_emb_eq_one (GlobalTheory.CharVal.mem_pullW τ w) hC
    rw [map_mul, map_natCast, map_mul, RingHom.map_det] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hfac : w.valuation Z.X.K (detFac σ σ' (fun τ => Formalism.UG.bc (Z.X.emb τ) (Bs τ)) fun τ => Formalism.UG.bc (Z.X.emb τ) (Bt τ)) =
      w.valuation Z.X.K (Z.Pr.T u) ^ (Z.X.f * ((Z.R.t + 1) / 2)) := by
    rw [detFac, map_prod, Fields.f, mul_comm, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_zpow₀, map_zpow₀, hdet τ _ (hBd τ), hdet τ _ (hBd' τ), inv_zpow', inv_zpow', ← zpow_add₀ hvT,
      ← zpow_natCast, ← sub_eq_half Z.W u hi hwt τ]
    congr 1
    ring
  rw [term, ker, stepT, GlobalTheory.ColPeriod.kerOf_thDistC _ _ _ (GlobalTheory.ColPeriod.cAof_pos sel mu cst)
    (GlobalTheory.ColPeriod.cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat, LinearMap.smul_apply, hGe, one_mul, smul_smul]
  refine ⟨(((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2)))⁻¹ * _) • G, GlobalTheory.ColPeriod.smul_mem_localizationAt_of_le w _ ?_ hG,
    by rw [smul_smul, mul_inv_cancel_left₀ (pow_ne_zero _ hT0)]⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.UnitAt GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.scal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.muInv at hscal
  rw [map_mul, map_mul, hfac, hscal, one_mul, map_inv₀, map_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hvT)]

end GlobalTheory.BarStd
end
end

section
noncomputable section

namespace GlobalTheory.KerT.Bar

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (InBox)

section Box

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap _ _ _ _).2 (by simpa using hy))
    exact (mem_localization_gmap _ _ _ _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap _ _ _ _).1 hy)
    exact (mem_localization_gmap _ _ _ _).2 (by simpa using this)

theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    g'.symm.toLinearMap ∘ₗ (c • x) ∘ₗ g.toLinearMap = c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine LinearMap.ext fun y => ?_
  exact equiv_osmul g'.symm c (x (g y))

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K} (h : InBox S cA cB N N' Ξ)
    (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 : (cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) ∈ homAt S N N' := h.1 _ hx
    change (cA : 𝓞 E) • x ∈ homAt S (gmap g N) (gmap g' N')
    rw [mem_homAt_gmap, conj_osmul]
    exact h1
  · rintro x _ ⟨z, hz, rfl⟩
    have h1 := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) = _
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]
    exact h1

end Box

variable {X : Fields}

theorem framed_gmap {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) (fun P : SB => g * fr P) := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem mem_valAt_gmap (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    y ∈ valAt w lam (gmap γ.1 L) ↔ ∃ z ∈ valAt w lam L, rhoVr X.emb lam (ufGL X.E n γ) z = y := by
  unfold valAt
  rw [delAtr_gmap, Formalism.BasicNotions.SkeletonIndexLemmas.localization_map₂]
  exact Iff.rfl

theorem rho_inv_apply {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem barTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y') → BarTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  obtain ⟨y', hy', he⟩ := hstd (((γ, 1) : UF Z.X.E _ × GLG Z.X.E _ SG) • d) (fun P => γ.1 * fr P)
    (((γ', 1) : UF Z.X.E _ × GLG Z.X.E _ SG') • d') (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap))
    ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩ (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1)
    (inBox_gmap hbox γ.1 γ'.1) (fun x => hint _) (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by
      rw [DecoSet.smul_val, Deco.Lsh_act _ γ.2, mem_valAt_gmap]
      exact ⟨y, hy, rfl⟩)
  rw [DecoSet.smul_val, Deco.Lsh_act _ γ'.2, mem_valAt_gmap] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  refine ⟨z, hz, ?_⟩
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul] at he
  have h2 := congrArg (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ'⁻¹)) he
  rwa [rho_inv_apply, rho_inv_apply] at h2

end GlobalTheory.KerT.Bar
end
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

local instance starFields (B : Base) : StarRing B.fields.E := B.fields.starE

theorem kerBar : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJM hP B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hA : ColIn.A I = ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J)
      (ColIn.chi I) I.J.cD := by
    rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hAl := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hRS := GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
    (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi
  rw [hA] at hRS
  have hRT : GlobalTheory.KerT.RatTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) _ u i hX hPr
      h.sel_ok (h.T_mem u) hRS
  have hT := isTerm h u a hi
  intro w hw hseen b b' d d' F hF
  classical
  unfold OverT at hw
  have hw' : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have h0 := Formalism.L2.Col.att_resChar_mem (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w
    rw [hw] at h0
    exact h0
  have hs : ¬ seenC (B.primes X) u ((I.rec7 l Z).plEq w) := fun hc => by
    have h0 : decide (seenC (B.primes X) u ((I.rec7 l Z).plEq w)) = false := hseen
    simp [hc] at h0
  have hsb : seenBarC (B.primes X) u ((I.rec7 l Z).plEq w) := (seenC_or_seenBarC hX hPr u _ hw').resolve_left hs
  have hbar : GlobalTheory.KerT.BarTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD) u i (i + 1)
      ((I.rec7 l Z).plEq w) := GlobalTheory.KerT.Bar.barTerm_of_std I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hRT ((I.rec7 l Z).plEq w)
    (fun d fr d' fr' Ξ₀ => GlobalTheory.BarStd.barStd hJM hP I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hAl
      ((I.rec7 l Z).plEq w) hsb d fr d' fr' Ξ₀)
  rw [← hA] at hbar
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := hT b b' d d'
  have hk' := hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [hk']
  have hF' : F ∈ GlobalTheory.KerT.valAt ((I.rec7 l Z).plEq w) (B.wts.lamTrue u i) d.1.1.deco.1.Lsh := hF
  obtain ⟨y', hy', he⟩ := hbar d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hw') F hF'
  refine ⟨y', hy', he.trans ?_⟩
  have e1 : B.fields.f = (I.rec7 l Z).R.f := GlobalTheory.Mem.Base.fields_f B
  rw [e1]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernels_bound_conjugatePrimePlaces : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  atlas_forward_decl GlobalTheory.LvT.Built.TrueLaws.kerBar
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open scoped Matrix

noncomputable section

namespace GlobalTheory.KerT.PStd

open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis admitted InClosure extLat ptTable detFac)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (InIntClosure Induces adj suppP StdAtT)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (UnramOver StdOver)

section Place

variable {p : ℕ} [Fact p.Prime]

theorem val_le_iff (x y : ℂ_[p]) :
    NormedField.valuation (K := ℂ_[p]) x ≤ NormedField.valuation (K := ℂ_[p]) y ↔ ‖x‖ ≤ ‖y‖ := by
  change ‖x‖₊ ≤ ‖y‖₊ ↔ _
  exact Iff.rfl

theorem val_le_one_iff (x : ℂ_[p]) : NormedField.valuation (K := ℂ_[p]) x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ _
  exact Iff.rfl

theorem norm_le_one_iff {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) :
    NormedField.valuation (K := ℂ_[p]) (ι x) ≤ 1 ↔ w.valuation K x ≤ 1 := by
  rw [val_le_one_iff]
  refine ⟨fun h => ?_, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw x⟩
  by_contra hx
  have hx1 : 1 < w.valuation K x := not_le.1 hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx1
  have h1 : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hx1
  obtain ⟨r, t, e⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ h1.le
  have h2 : r ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K r) < 1
    rw [← e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (w.valuation_le_one _)) h1
  have h3 : 1 ≤ ‖ι ((t : 𝓞 K) : K)‖ := not_lt.1 fun hlt => t.2 ((hw _).2 hlt)
  have h4 := (hw r).1 h2
  have h5 : ‖ι ((t : 𝓞 K) : K)‖ = ‖ι x‖ * ‖ι (r : K)‖ := by
    rw [← norm_mul, ← map_mul]
    congr 2
    change _ = x * algebraMap (𝓞 K) K r
    rw [← e, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (r : K))]

theorem finite_inDeg {I : Type} [Fintype I] {a b : ℕ} (lam : I → DomWeight a) (s' : I → ℤ) :
    {m : DVar I a b →₀ ℕ | InDeg lam s' m}.Finite := by
  refine (Finsupp.finite_of_degree_le (∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ)).toNat).subset fun m hm => ?_
  have h4 : (m.degree : ℤ) = ∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ) := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [← hm τ, Fintype.sum_prod_type]
  change m.degree ≤ _
  omega

theorem inClosure_of {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ_[p]) {I : Type} [Fintype I] {a b : ℕ}
    (lam : I → DomWeight a) (s' : I → ℤ) (M : I → Submodule (𝓞 K) (Fin a → K)) (MW : I → Submodule (𝓞 K) (Fin b → K))
    (κ : K) (J : (DVar I a b →₀ ℕ) → K) {H : Type} {Sup : Set H} (ap : H → I → Matrix (Fin a) (Fin b) ℂ_[p])
    {Ms : Set (DVar I a b →₀ ℕ)} (hM : ∀ m, InDeg lam s' m → m ∈ Ms)
    (hadm : ∀ x ∈ Sup, admitted (NormedField.valuation (K := ℂ_[p])) ι M MW (ap x))
    (h : InIntClosure Sup (fun x m => ι κ * ptTable (ap x) m) Ms fun m => ι (J m)) :
    InClosure (NormedField.valuation (K := ℂ_[p])) ι lam s' M MW κ J := by
  intro ε hε
  obtain ⟨c, hc, hc1, hc2⟩ := h (finite_inDeg (b := b) lam s').toFinset (fun m hm => hM m (by simpa using hm)) ‖ι ε‖
    (norm_pos_iff.2 ((map_ne_zero ι).2 hε))
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun i => c (e i), fun i => ap (e i), fun i => (val_le_one_iff _).2 (hc1 _),
    fun i => hadm _ (hc (e i).2), fun m hm => (val_le_iff _ _).2 ?_⟩
  have h1 := hc2 m (by simpa using hm)
  have h2 : (c.sum fun x r => r * (ι κ * ptTable (ap x) m)) = ι κ * ∑ i, c (e i) * ptTable (ap (e i)) m := by
    rw [Finsupp.sum, ← Finset.sum_coe_sort, ← e.sum_comp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  rw [← h2]
  exact h1.le

end Place

section Lat

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {I : Type} [Fintype I] (emb : I → E →+* K) {n : ℕ}

theorem localization_tauLat_le (w : HeightOneSpectrum (𝓞 K)) (τ : I) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∈ w.asIdeal → s ∈ P.asIdeal)
    {L L' : Submodule (𝓞 E) (Fin n → E)} (h : L ≤ localization₂ P.asIdeal L') :
    localization₂ w.asIdeal (tauLat emb τ L) ≤ localization₂ w.asIdeal (tauLat emb τ L') :=
  localization_le_of_le_localization w (tauLat_le_locP emb w τ fun x hx => by
    obtain ⟨s, hs, hsx⟩ := h hx
    exact ⟨s, fun h' => hs (hP s h'), hsx⟩)

omit [Fintype I] in
theorem tauLat_colLat (τ : I) (B : GL (Fin n) E) :
    tauLat emb τ (colLat B) = colLat (Matrix.GeneralLinearGroup.map (emb τ) B) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, map_add]
      exact add_mem hy hz
    | smul r y _ hy =>
      have e : (fun a => emb τ ((r • y) a)) = RingOfIntegers.mapRingHom (emb τ) r • fun a => emb τ (y a) := by
        funext a
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl
      change (fun a => emb τ ((r • y) a)) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem isBasisAt_tauLat (w : HeightOneSpectrum (𝓞 K)) (τ : I) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∈ w.asIdeal → s ∈ P.asIdeal)
    {L : Submodule (𝓞 E) (Fin n → E)} {B : GL (Fin n) E} (h : IsBasisAt P L B) :
    IsBasisAt w (tauLat emb τ L) (Matrix.GeneralLinearGroup.map (emb τ) B) := by
  unfold IsBasisAt at h ⊢
  rw [← tauLat_colLat]
  exact le_antisymm (localization_tauLat_le emb w τ P hP (fun x hx => h ▸ GlobalTheory.TestLat.WeylLocal.le_locP P L hx))
    (localization_tauLat_le emb w τ P hP (fun x hx => h ▸ GlobalTheory.TestLat.WeylLocal.le_locP P (colLat B) hx))

theorem admissible_of_integral_conj_le {Ω Γ : Type} [Field Ω] [LinearOrderedCommGroupWithZero Γ] (v : Valuation Ω Γ) (σ : K →+* Ω)
    (w : HeightOneSpectrum (𝓞 K)) (hσ : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) (τ : I) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∈ w.asIdeal → s ∈ P.asIdeal) {a b : ℕ}
    {L : Submodule (𝓞 E) (Fin a → E)} {L' : Submodule (𝓞 E) (Fin b → E)} (A : Matrix (Fin a) (Fin b) E)
    (hA : ∀ y ∈ L', A *ᵥ y ∈ localization₂ P.asIdeal L) (c : Ω) (hc : v c ≤ 1) :
    ∀ y ∈ extLat v σ (tauLat emb τ L'), (Matrix.of fun α β => c * σ (emb τ (A α β))) *ᵥ y ∈ extLat v σ (tauLat emb τ L) := by
  have h1 : ∀ z ∈ tauLat emb τ L', A.map (emb τ) *ᵥ z ∈ localization₂ w.asIdeal (tauLat emb τ L) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have e : A.map (emb τ) *ᵥ (fun a => emb τ (x a)) = fun a => emb τ ((A *ᵥ x) a) := by
        funext α
        simp [Matrix.mulVec, dotProduct]
      rw [e]
      exact localization_tauLat_le emb w τ P hP (L := localization₂ P.asIdeal L) le_rfl
        (GlobalTheory.TestLat.WeylLocal.le_locP w _ (Submodule.subset_span ⟨_, hA x hx, rfl⟩))
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    have h2 := (GlobalTheory.ExtLatMatrix.extLat_matrix_integral K w Ω Γ v σ hσ).1 a _ _ (h1 z hz)
    have e : (Matrix.of fun α β => c * σ (emb τ (A α β))) *ᵥ (fun i => σ (z i)) =
        (⟨c, hc⟩ : v.integer) • fun i => σ ((A.map (emb τ) *ᵥ z) i) := by
      funext α
      simp [Matrix.mulVec, dotProduct, Subring.smul_def, Finset.mul_sum, mul_assoc]
    rw [e]
    exact Submodule.smul_mem _ _ h2
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul r x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

end Lat

section Ker

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem exists_mul_eq_of_unif {P : HeightOneSpectrum (𝓞 E)} {T r : 𝓞 E} (hT : T ∈ P.asIdeal) (hT2 : T ∉ P.asIdeal ^ 2)
    (hr : r ∈ P.asIdeal) : ∃ s ∉ P.asIdeal, ∃ b : 𝓞 E, s * r = T * b := by
  obtain ⟨J, hJ⟩ : P.asIdeal ∣ Ideal.span {T} := Ideal.dvd_span_singleton.2 hT
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    apply hT2
    have : Ideal.span {T} ≤ P.asIdeal ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.1 hJP
  have hm : r * s ∈ Ideal.span {T} := hJ ▸ Ideal.mul_mem_mul hr hsJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨s, hs, b, by rw [mul_comm s, ← hb, mul_comm]⟩

theorem isBasisAt_one {P : HeightOneSpectrum (𝓞 E)} {L : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal L = stdAt E n P) :
    IsBasisAt P L 1 := by
  unfold IsBasisAt
  rw [h, stdAt, stdLat_eq_span, colLat]
  congr 3
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem exists_basis_ker {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hs : d.at P.1 = stdAt E n P.1) {T : 𝓞 E}
    (hT : T ∈ P.1.asIdeal) (hT2 : T ∉ P.1.asIdeal ^ 2) :
    ∃ B : GL (Fin n) E, (B : Matrix (Fin n) (Fin n) E).det = algebraMap (𝓞 E) E T ∧ IsBasisAt P.1 d.L B := by
  classical
  have hle : stdLat E n ≤ d.at P.1 := hs ▸ Formalism.L2.Col.le_locP P.1 _
  have hvec : ∀ r : Fin n → 𝓞 E, (fun a => algebraMap (𝓞 E) E (r a) : Sp E n) ∈ stdLat E n := fun r =>
    (mem_stdLat _).2 fun a => ⟨r a, rfl⟩
  let g : (Fin n → 𝓞 E) →ₗ[𝓞 E] (𝓞 E ⧸ P.1.asIdeal) := (hd.fLin P _ hle) ∘ₗ
    LinearMap.codRestrict (stdLat E n) ((Algebra.linearMap (𝓞 E) E).compLeft (Fin n)) hvec
  have hg : ∀ r, g r = d.f P fun a => algebraMap (𝓞 E) E (r a) := fun _ => rfl
  have hgs : ∀ r, g r = ∑ j, Ideal.Quotient.mk P.1.asIdeal (r j) * g (Pi.single j 1) := fun r => by
    conv_lhs => rw [← Finset.univ_sum_single r, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← quot_smul_def, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hred : ∀ x ∈ d.at P.1, ∃ s ∉ P.1.asIdeal, ∃ r : Fin n → 𝓞 E, s • x = (fun a => algebraMap (𝓞 E) E (r a)) ∧
      g r = Ideal.Quotient.mk P.1.asIdeal s * d.f P x := by
    intro x hx
    obtain ⟨s, hs1, hs2⟩ := (Formalism.L2.Col.mem_locP P.1 (stdLat E n) x).1 (show x ∈ stdAt E n P.1 from hs ▸ hx)
    choose r hr using (mem_stdLat _).1 hs2
    have e : s • x = fun a => algebraMap (𝓞 E) E (r a) := funext fun a => (hr a).symm
    exact ⟨s, hs1, r, e, by rw [hg, ← e, hd.f_smul P s x hx]⟩
  obtain ⟨i, hi⟩ : ∃ i, g (Pi.single i 1) ≠ 0 := by
    by_contra h0
    push Not at h0
    obtain ⟨x, hx, hne⟩ := hd.f_ne P
    obtain ⟨s, hs1, r, -, e⟩ := hred x (Formalism.L2.Col.le_locP P.1 _ hx)
    rw [hgs] at e
    simp only [h0, mul_zero, Finset.sum_const_zero] at e
    exact mul_ne_zero (mk_ne_zero hs1) hne e.symm
  have hmax := P.1.isMaximal
  obtain ⟨z, hz⟩ := Ideal.Quotient.exists_inv hi
  choose c hc using fun j => Ideal.Quotient.mk_surjective (g (Pi.single j 1) * z)
  have hc' : ∀ j, g (Pi.single j 1) = Ideal.Quotient.mk P.1.asIdeal (c j) * g (Pi.single i 1) := fun j => by
    rw [hc, mul_assoc, mul_comm z, hz, mul_one]
  let t : Fin n → 𝓞 E := Function.update (fun j => -c j) i T
  let B₀ : Matrix (Fin n) (Fin n) (𝓞 E) := (1 : Matrix (Fin n) (Fin n) (𝓞 E)).updateRow i t
  have hdet : B₀.det = T := by
    have h1 := Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) (𝓞 E)) i t
    have h2 : (∑ k, t k • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) k) = t := by
      funext j
      simp [Finset.sum_apply, Matrix.one_apply]
    rw [h2] at h1
    simp [B₀, h1, t]
  have hT0 : algebraMap (𝓞 E) E T ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hT2 (zero_mem _)
  have hdet' : (B₀.map (algebraMap (𝓞 E) E)).det = algebraMap (𝓞 E) E T := by
    rw [← hdet, RingHom.map_det]
    rfl
  have hcol : ∀ j, (fun a => B₀ a j) = if j = i then T • Pi.single i 1 else Pi.single j 1 - c j • Pi.single i 1 := by
    intro j
    funext a
    by_cases ha : a = i <;> by_cases hj : j = i <;>
      simp [B₀, t, ha, hj, Matrix.updateRow_apply, Matrix.one_apply, Pi.single_apply, Function.update_apply, eq_comm]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet' ▸ hT0), hdet', le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := (hd.mem_locP_L P x).1 hx
    obtain ⟨s, hs1, r, e, e'⟩ := hred x hx1
    have h1 : r i + ∑ j ∈ Finset.univ.erase i, r j * c j ∈ P.1.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      refine (mul_eq_zero.1 ?_).resolve_right hi
      rw [hx2, mul_zero, hgs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at e'
      rw [← e', map_add, map_sum, add_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc, ← hc']
    obtain ⟨s', hs', b, hb⟩ := exists_mul_eq_of_unif hT hT2 h1
    refine (Formalism.L2.Col.mem_locP P.1 _ x).2 ⟨s' * s, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs' hs1, ?_⟩
    have h2 : s' • r = ∑ j, (Function.update (s' • r) i b) j • fun a => B₀ a j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hcol, if_pos rfl, Function.update_self,
        Finset.sum_congr rfl fun j hj => by rw [hcol, if_neg (Finset.ne_of_mem_erase hj),
          Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
      funext a
      by_cases ha : a = i
      · subst ha
        simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        rw [Finset.sum_congr rfl fun j hj => by rw [Pi.single_eq_of_ne' (Finset.ne_of_mem_erase hj)]]
        rw [mul_add, Finset.mul_sum] at hb
        rw [mul_comm b, ← hb, add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero fun j _ => by ring, add_zero]
      · simp [Finset.sum_apply, Pi.single_apply, ha]
    have h3 : (s' * s) • x = ∑ j, (Function.update (s' • r) i b) j • fun a => algebraMap (𝓞 E) E (B₀ a j) := by
      funext a
      have h4 := congrArg (fun y => algebraMap (𝓞 E) E (y a)) h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h4
      rw [mul_smul, e]
      simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
      exact h4
    rw [h3]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine localization_le_of_le_localization P.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    refine (hd.mem_locP_L P _).2 ⟨hle (hvec fun a => B₀ a j), (hg fun a => B₀ a j).symm.trans ?_⟩
    rw [hcol]
    split_ifs with hj
    · rw [map_smul, quot_smul_def, Ideal.Quotient.eq_zero_iff_mem.2 hT, zero_mul]
    · rw [map_sub, map_smul, quot_smul_def, ← hc', sub_self]

end Ker

section Data

theorem unramOver_of_mem {X : Fields} {S : Set ℕ} (mu : Tup X.F X.E X.K S) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) :
    UnramOver (mu : Chr X.F X.E X.K) p := by
  intro v hv hq
  have h1 : GoodPl X.E S v := by
    by_contra hg
    exact hq (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hg)
  have h2 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ p := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hv
  haveI := v.isPrime
  have h3 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p := ((Nat.dvd_prime hp).1 h2).resolve_left CharP.ringChar_ne_one
  exact h1.2.2 (show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S from h3 ▸ hS)

theorem stdOver_of_stdAtT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {n : ℕ}
    {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n (Pr.vT u) SG) (h : StdAtT d.1) : StdOver (Pr.T u) d.1.N := by
  intro Q hQ
  rw [← hPr.piT_norm u] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h1 | h1
  · exact h ⟨Q, (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) Q).2 h1⟩
  · have h2 := h ⟨conjPrime₂ Q, (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).2 h1⟩
    have h3 := GlobalTheory.StdReps.localization_conj_le_of_le d.2.lat.fg d.2.uni stdLat_unimodular h2.le
    have h4 := GlobalTheory.StdReps.localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular d.2.uni h2.ge
    rw [GlobalTheory.CharVal.conjP_conjP'] at h3 h4
    exact le_antisymm h4 h3

end Data

theorem pTerm_std : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) → AlcoveAt Z.W u (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), seenC Z.Pr u w → ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ((Z.Pr.T u : Z.X.K) ^ (((Z.X.f * Z.R.N i : ℕ) : ℤ) - ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift)) • term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.L := by
  intro hJ hKnown Z H s cc δ B χ cD sel S mu cst u i hi hyp hjets halc w hw SG SG' d fr d' fr' Ξ₀ hstd hfr hfr' hbox hint y hy
  classical
  have hZ := hyp.ok
  have hPr := hZ.primes
  have hTp := hPr.T_prime u
  haveI : Fact (Z.Pr.T u).Prime := ⟨hTp⟩
  obtain ⟨τ₀⟩ : Nonempty Z.X.Tau := Fintype.card_pos_iff.1 hZ.fields.f_pos
  have hP : ∀ τ, pullW τ w ∈ Z.Pr.vT u := (seenC_iff hPr u w).1 hw
  have hTw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal := by
    have h1 := (mem_pullW τ₀ w _).1 (T_mem hPr u ⟨_, hP τ₀⟩)
    rwa [map_natCast] at h1
  have hT0 : (Z.Pr.T u : Z.X.K) ≠ 0 := Nat.cast_ne_zero.2 hTp.ne_zero
  obtain ⟨ι, hι⟩ := GlobalTheory.DatumJets.Place.exists_embedding (p := Z.Pr.T u) w hTw
  have hind : Induces ι w := fun y => by rw [hι]; rfl
  have hσ := norm_le_one_iff ι w hind
  have hTS : Z.Pr.T u ∈ S := hyp.host (Or.inr ⟨u, rfl⟩)
  have hgS : ∀ k, Z.Pr.g k ∈ S := fun k => hyp.host (Or.inl (by fin_cases k <;> simp))
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩

  obtain ⟨m0, eta, htied, hmu⟩ := hyp.tied
  have hscal := ((((GlobalTheory.CharVal.charValAtT Z H s χ u hZ hyp.ana.1 hyp.ana.2.1 hyp.ana.2.2.2.2.1 hyp.chiK).2.2 m0 eta htied sel
    hyp.isSel S mu (unramOver_of_mem mu hTp hTS) (fun k => unramOver_of_mem mu (hPr.g_prime k) (hgS k)) cst hmu ⟨i, hi⟩).1
    w hTw).1).2 _ _ d.1.N fr d'.1.N fr' hsd hsd' (stdOver_of_stdAtT hPr u d hstd.1) (stdOver_of_stdAtT hPr u d' hstd.2) hfr hfr'

  have hcopT : Nat.Coprime (Ideal.absNorm cc) (Z.Pr.T u) := by
    have h1 := hyp.cop _ (Finset.mem_union_left _ (hP τ₀))
    rwa [hPr.vT_norm u _ (hP τ₀)] at h1
  obtain ⟨un, hun, hmom⟩ := hJ Z hZ H s cc δ B χ cD hyp.ana u hcopT w ι hind
  have hclo := (hmom sel S mu cst hyp.isSel hyp.host (fun P hP => hyp.cop P (Finset.mem_union_right _ hP)) i _ hi rfl SG SG' d d'
    hstd.1 hstd.2 Ξ₀ (fun x _ => ⟨hint x, hbox.2 x⟩)).2 hw

  obtain ⟨s₀, s', hwt, -⟩ := GlobalTheory.ColPeriod.chainWeights Z.X Z.Pr Z.R Z.W u i hi
  have hloc : ∀ τ, localization₂ (pullW τ w).asIdeal d.1.Lsh = d.1.at (pullW τ w) := fun τ =>
    d.2.locP_Lsh (sepElt_of_ok hPr u) ⟨_, hP τ⟩
  have hM : LatWithBasis w (fun τ => tauLat Z.X.emb τ d.1.Lsh) 1 := fun τ =>
    ⟨(tauLatLattice _ _ _ _ Z.X.emb τ _ d.2.Lsh_lattice).fg, by
      have h1 := isBasisAt_tauLat Z.X.emb w τ (pullW τ w) (fun _ h => h) (isBasisAt_one ((hloc τ).trans (hstd.1 ⟨_, hP τ⟩)))
      rwa [map_one] at h1⟩
  choose BE hBE hBE' using fun τ => exists_basis_ker d'.2 ⟨_, hP τ⟩ (hstd.2 ⟨_, hP τ⟩) (T_unif hZ.fields hPr u ⟨_, hP τ⟩).1
    (T_unif hZ.fields hPr u ⟨_, hP τ⟩).2
  have hMW : LatWithBasis w (fun τ => tauLat Z.X.emb τ d'.1.L) fun τ => Matrix.GeneralLinearGroup.map (Z.X.emb τ) (BE τ) := fun τ =>
    ⟨(tauLatLattice _ _ _ _ Z.X.emb τ _ d'.2.L_lattice).fg, isBasisAt_tauLat Z.X.emb w τ (pullW τ w) (fun _ h => h) (hBE' τ)⟩
  have hfac : detFac s₀ s' (1 : Z.X.Tau → GL (Fin (Z.R.N i)) Z.X.K)
      (fun τ => Matrix.GeneralLinearGroup.map (Z.X.emb τ) (BE τ)) =
      (Z.Pr.T u : Z.X.K) ^ ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift := by
    have h1 : ∀ τ, ((Matrix.GeneralLinearGroup.map (Z.X.emb τ) (BE τ)).val).det = Z.Pr.T u := fun τ => by
      have h2 := congrArg (Z.X.emb τ) (hBE τ)
      rw [RingHom.map_det, map_natCast, map_natCast] at h2
      exact h2
    simp only [detFac, h1, Pi.one_apply, Units.val_one, Matrix.det_one, one_zpow, one_mul, GlobalTheory.JetPoint.detShift_eq hwt]
    induction (Finset.univ : Finset Z.X.Tau) using Finset.induction_on with
    | empty => simp
    | insert τ t h ih => rw [Finset.prod_insert h, Finset.sum_insert h, zpow_add₀ hT0, ih]
  have hin := inClosure_of ι (Z.W.lamTrue u i) s' (fun τ => tauLat Z.X.emb τ d.1.Lsh) (fun τ => tauLat Z.X.emb τ d'.1.L)
    ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * Z.R.N i))⁻¹
    (GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.jetSum (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
      fun x => phiT Z.X.K d.1 d'.1 x * Ξ₀ x)
    (Ms := GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.RatIdx (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
      fun x => phiT Z.X.K d.1 d'.1 x * Ξ₀ x) (Sup := suppP d.1 d'.1)
    (fun x τ => Matrix.of fun α β => un τ * ι (Z.X.emb τ (LinearMap.toMatrix' (adj x) α β)))
    (fun m hm x hx _ => hjets _ _ hsd hsd' x hx m fun τ => by
      refine (hm τ).trans (Finset.sum_congr rfl fun a _ => ?_)
      rw [hwt.2.2 τ]
      ring)
    (fun x hx τ => admissible_of_integral_conj_le Z.X.emb _ ι w hσ τ (pullW τ w) (fun _ h => h) _ (fun y hy => by
      have h1 := (d'.2.mem_locP_L ⟨_, hP τ⟩ y).1 (Formalism.L2.Col.le_locP _ _ hy)
      rw [LinearMap.toMatrix'_mulVec, hloc]
      exact hx ⟨_, hP τ⟩ y h1.1 h1.2) _ ((val_le_one_iff _).2 (hun τ).le))
    (by
      rw [map_inv₀, map_pow, map_natCast]
      exact hclo)
  have hy' : y ∈ HAt w (Z.W.lamTrue u i) fun τ => tauLat Z.X.emb τ d.1.Lsh := by
    obtain ⟨t, ht, hty⟩ := hy
    exact ⟨t, ht, delLeNab _ _ _ _ _ hty⟩
  obtain ⟨G, hG, hG'⟩ := GlobalTheory.JetPoint.closureIntegral Z.X.K w _ _ _ ι hσ _ _ _ _ _ _ s₀ s' _ hwt _ _ _ _ hM hMW _ _ hin y hy'
  rw [term, ker, stepT, GlobalTheory.ColPeriod.kerOf_thDistC _ _ _ (GlobalTheory.ColPeriod.cAof_pos sel mu cst)
    (GlobalTheory.ColPeriod.cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat, LinearMap.smul_apply, smul_comm, hG', hfac, smul_smul (_ ^ _),
    zpow_sub₀ hT0, zpow_natCast]
  refine GlobalTheory.ColPeriod.smul_mem_localizationAt_of_le w _ (le_of_eq hscal) ?_
  rw [div_mul_eq_mul_div, mul_inv_cancel_left₀ (pow_ne_zero _ hT0), div_self (zpow_ne_zero _ hT0), one_smul]
  rw [GlobalTheory.KerT.localization_delAtr_eq_localization_nabAtr hKnown Z.X _ (Z.Pr.T u) _ hTp halc w hTw _ d'.2.L_lattice]
  exact hG

end GlobalTheory.KerT.PStd
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerT.PAll

section Hom

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap P g N _).2 (by simpa using hy))
    exact (mem_localization_gmap P g' N' _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap P g N _).1 hy)
    refine (mem_localization_gmap P g' N' _).2 ?_
    simpa using this

omit [NumberField E] [StarRing E] in
theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    (g'.symm.toLinearMap ∘ₗ (c • x : HomE E a b) ∘ₗ g.toLinearMap : HomE E a b) =
      c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) := by
  rw [← algebraMap_smul E c x, ← algebraMap_smul E c, LinearMap.smul_comp, LinearMap.comp_smul]

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB N N' Ξ) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have h1 : ((cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b)) ∈ homAt S N N' := h.1 _ hx
    change ((cA : 𝓞 E) • x) ∈ homAt S (gmap g N) (gmap g' N')
    rwa [mem_homAt_gmap, conj_osmul]
  · obtain ⟨z, hz, rfl⟩ := hy
    have := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    refine Eq.trans ?_ this
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) =
      Ξ (_ + (cB : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap : HomE E a b))
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]

end Hom

variable {X : Fields} {n : ℕ}

theorem framed_gmap {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) fun P => g * fr P := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem rho_inv_apply (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem mem_localization_map {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (f : V →ₗ[𝓞 K] V) (hf : Function.Injective f) (M : Submodule (𝓞 K) V) (y : V) :
    f y ∈ localization₂ w.asIdeal (M.map f) ↔ y ∈ localization₂ w.asIdeal M := by
  rw [mem_locP, mem_locP]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← map_smul]
  exact ⟨fun ⟨z, hz, h⟩ => hf h ▸ hz, fun h => ⟨_, h, rfl⟩⟩

theorem rho_mem_valAt (w : HeightOneSpectrum (𝓞 X.K)) (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ) y ∈ valAt w lam (gmap γ.1 L) ↔ y ∈ valAt w lam L := by
  unfold valAt
  rw [delAtr_gmap]
  exact mem_localization_map w ((rhoVr X.emb lam (ufGL X.E n γ)).restrictScalars (𝓞 X.K))
    (Function.LeftInverse.injective (rho_inv_apply lam γ)) _ y

theorem pTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ((Z.Pr.T u : Z.X.K) ^ (((Z.X.f * Z.R.N i : ℕ) : ℤ) - ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift)) • term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.L) → PTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  have e1 : (((γ, 1) : UF Z.X.E (Z.R.N i) × GLG Z.X.E (Z.R.N i) SG) • d).1.Lsh = gmap γ.1 d.1.Lsh :=
    Deco.Lsh_act d.1 γ.2 1
  have e2 : (((γ', 1) : UF Z.X.E (Z.R.N (i + 1)) × GLG Z.X.E (Z.R.N (i + 1)) SG') • d').1.L = gmap γ'.1 d'.1.L :=
    Deco.L_act d'.1 γ'.1 1
  have h := hstd _ (fun P => γ.1 * fr P) _ (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩
    (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1) (inBox_gmap hbox γ.1 γ'.1) (fun _ => hint _)
    (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by rw [e1, rho_mem_valAt]; exact hy)
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, e2, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul,
    rho_mem_valAt] at h
  exact h

end GlobalTheory.KerT.PAll
end
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

local instance starHostP (B : Base) : StarRing B.host.E := B.fields.starE

theorem kerP : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJet hKnown B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro w hw hs b b' d d' F hF
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := isTerm h u a hi b b' d d'
  rw [hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩]
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z) w
  have eA := AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hal := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hrat : GlobalTheory.KerT.RatTerm B.wts I.Ch I.sel (I.tup a) (I.cst a) (ColIn.A I) u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (ColIn.A I) u i hX hPr
    h.sel_ok (h.T_mem u) (GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
      (B.R.m - 2) u i (ColIn.A I) hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi)
  rw [ColIn.A, eA] at hrat
  have hseen : Formalism.L2.Col.seenC (B.primes X) u ((I.rec7 l Z).plEq w) := @of_decide_eq_true _ (Classical.propDecidable _) hs
  have hPT : GlobalTheory.KerT.PTerm B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) ((I.rec7 l Z).plEq w) :=
    GlobalTheory.KerT.PAll.pTerm_of_std I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hrat _
    (GlobalTheory.KerT.PStd.pTerm_std hJet hKnown I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hal _ hseen)
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have e := hw
    unfold OverT at e
    rw [e] at h1
    exact h1
  have key := hPT d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hT) F hF
  rw [ColIn.A, eA]
  have eS : ∀ τ, (dat I l Z u a).ch.C.sDiv i τ = -((B.wts.lamTrue u (i + 1) τ).detShift) := fun τ => by
    have e1 := (KMap.sSharp_eq (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi τ).2
    have e2 := GlobalTheory.GO.ChSrc.trueWt_detShift_succ (X := B.fields) (B.wts.hc u) hi τ
    have e3 := congrFun (GlobalTheory.GO.ChSrc.trueWt_eq B.wts u (i + 1)) τ
    refine e1.trans ?_
    rw [← e3, e2, neg_neg]
  have eE : (((I.rec7 l Z).R.f * (I.rec7 l Z).R.N i : ℕ) : ℤ) + ∑ τ, (dat I l Z u a).ch.C.sDiv i τ =
      ((B.fields.f * B.R.N i : ℕ) : ℤ) - ∑ τ, (B.wts.lamTrue u (i + 1) τ).detShift := by
    rw [Finset.sum_congr rfl (fun τ _ => eS τ), Finset.sum_neg_distrib, B.fields_f, sub_eq_add_neg]
    rfl
  rw [eE]
  exact key

end GlobalTheory.LvT.Built.TrueLaws
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernels_bound_levelPrimePlaces : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  atlas_forward_decl GlobalTheory.LvT.Built.TrueLaws.kerP
end

section
section
noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem kmap_dat : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  intro B X I h hJ l Z hv u a i hi c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := KMap.laHyp_of_vecP I (I.cols l) Z.W Z.V Z.S Z.N Z.G h hv a u i (i + 1)
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  have hJa : GlobalTheory.KerT.JetsAll (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := fun L L' hL hL' =>
    (GlobalTheory.MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) L L').2
      (GlobalTheory.MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u) hL hL')
  have hr := KMap.rhoIs I h a u hi
  refine KMap.kmap_of_jet (I.chIn u a) I.A.σ₀ (l.ch u a) (B.hcW u) hi c c' F _ ?_
  have hV := GlobalTheory.GO.ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have hnu : GlobalTheory.GO.ChSrc.nuEnd (B.hcW u) i = nuLast (Pr := B.primes X) B.wts u i := GlobalTheory.GO.ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  rw [hnu] at hV ⊢

  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB := GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u
  have hLa' : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u) := hLa
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    KMap.map_kerOf (X := B.fields) I.A (Sall (Pr := B.primes X) I.sel (I.tup a) u) (rowSG (B.primes X) I.sel (I.tup a)) hA hB I.sel
      (mUof (R := B.R) I.Ch (I.tup a) i) (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) hV hLa' h0 hE
      (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      (hJa _ _ ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩) (hbox p p') F
  refine (key (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c')).trans ?_
  rw [← hr c.1 (((dat I l Z u a).I.S i).rep c) c'.1 (((dat I l Z u a).I.S (i + 1)).rep c'), ColIn.A_cD]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c) (((dat I l Z u a).I.S (i + 1)).rep c') F) := by
  atlas_forward_decl GlobalTheory.LvT.Built.TrueLaws.kmap_dat
end

section
section
noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem moveStep_fam (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    GlobalTheory.KerT.MoveStep (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := by
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hEq := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  obtain ⟨-, hLat, hTh⟩ := GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hM := GlobalTheory.ThetaMove.moveStep_of_family I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hEq hLat
    (fun a b _ _ => hTh a b) hJa
  rw [← AmbIn.amb_eq_ambOf] at hM
  exact hM

theorem kernelCondition_at_row_family (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerUK (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P F
  exact UpLaw.kAt_uk B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi)
    (GlobalTheory.KerT.UK.ukTerm_of_moveStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) I.A u i hX hPr h.sel_ok
      (h.T_mem u) (moveStep_fam h hJ l Z u a hi)) b b' d d' P F

theorem laws_true_fam : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (I.rec7 l Z) u, Bd.ch = tw (I.tw l l0 Z) u a ∧
      (∀ i, i ≤ (I.rec7 l Z).R.m → Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
      (∀ i, i < (I.rec7 l Z).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
      Bd = dat I l Z u a := by
  intro B X I h hJ l l0 Z u a
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hE := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hV := (GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1
  have hth : ∀ (a : I.ι) (u : B.Word), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a)
      (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) := fun a u =>
    GlobalTheory.ChainTheta.chTh_ok_of_colIn' B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ hE hV a u
  refine ⟨dat I l Z u a, dat_ch I l l0 Z u a, fun i _ => split u a h i, sees l Z u a, fun i hi => ?_, rfl⟩
  exact ⟨_, kerEq h l Z u a (hth a u) hi (GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives B X I h hJ l Z hV u a i hi), kerDil h l Z u a hi,
    kernelCondition_at_row_family h hJ l Z u a hi, GlobalTheory.T.trueChainKernels_bound_conjugatePrimePlaces GlobalTheory.T.kernelJets_levelPlace_integralMoments GlobalTheory.T.weylModule_simple_closedLowestAlcove B X I h hJ l Z u a (hth a u) i hi,
    GlobalTheory.T.trueChainKernels_bound_levelPrimePlaces GlobalTheory.T.kernelJets_levelPlace_integralMoments GlobalTheory.T.weylModule_simple_closedLowestAlcove B X I h hJ l Z u a (hth a u) i hi⟩

end GlobalTheory.LvT.Built.TrueLaws
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fivePointLaws_trueChains : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (I.rec7 l Z) u, Bd.ch = tw (I.tw l l0 Z) u a ∧ (∀ i, i ≤ (I.rec7 l Z).R.m → Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧ (∀ i, i < (I.rec7 l Z).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧ Bd = dat I l Z u a := by
  atlas_forward_decl GlobalTheory.LvT.Built.TrueLaws.laws_true_fam
end
