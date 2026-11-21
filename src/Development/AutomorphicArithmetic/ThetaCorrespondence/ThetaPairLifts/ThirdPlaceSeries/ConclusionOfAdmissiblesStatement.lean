import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfLocalConditionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfLocalConditions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StepsOfArtinReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StepsOfArtinReciprocity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CommTriv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTail
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutBoundOfSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePartitionsPerm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
abbrev _root_.GlobalTheory.Pass.stepType_proof_tyz : Prop :=  _root_.GlobalTheory.Pass.StepTypeAlt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove
noncomputable section
namespace UpperTheory.GalS
open UpperTheory.Lit.Car (IneAb comm_le_ine)
theorem stepType_alt : _root_.GlobalTheory.Pass.stepType_proof_tyz := by
  intro D P hDZ h0 h1 h2' h5 i k hl r hr x PI hPI v τ hτ hsq hroot
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hnc := nc_of_label P hDZ h1 i k v PI τ hτ hsq hroot
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  refine ⟨u, hu, ?_⟩
  have hcard : ∀ a : (ZMod (D.host.g k))[X], Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := fun a => by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]
  have hroot0 : ∀ y ∈ Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t), y ≠ 0 := by
    rintro y hy rfl
    unfold Formalism.CyclotomicNorms.rootsBar at hy
    have h := isRoot_of_mem_roots hy
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, mul_coeff_zero, coeff_zero_eq_eval_zero (_ ^ _)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((P.lz k).lab_spec τ).2.2 h
    · simp at h
  have key : ∀ w, w ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host w → Nc D.nd D.naut (D.naut.locV i PI w) →
      D.naut.mono0 (D.naut.locV i PI w) →
      (D.naut.items₂ k w (D.naut.locV i PI w)).natDegree = D.R.nV →
      (∀ y ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w)), y ≠ 0) →
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w))).map
            fun y => X - C (P.om k w y σ)).prod := by
    intro w hw hs hn hm hdeg hnz
    have hwl : w ∈ placesOver D.host.E (D.nd.l i) := hl ▸ hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨hdR, heq, -⟩ := compatR D h0 h2 h5 i r hr x PI Pa hPI hB w hwl (by rw [hB.2.2.2.1 w hs]; exact hn)
    rw [hB.2.2.2.1 w hs] at heq
    have hdim : D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := by
      have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) (r x)) w
      rwa [heq.dim, D.naut.lpDim_tw] at h
    refine ⟨hdR, ?_, fun σ hσ => ?_⟩
    · refine heq.mono ?_
      rw [D.naut.monomial_twist_iff]; exact hm
    · have hab : IneAb D.nd D.naut (D.naut.lpTw (D.naut.locV i PI w) ((1 - (D.R.nV : ℝ)) / 2)) := fun s hs' => by
        rw [D.naut.inePol_tw _ _ s (comm_le_ine w hs'), D.naut.lpDim_tw,
          P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) s (comm_le_ine w hs'),
          Multiset.map_congr rfl (fun y hy => by rw [comm_triv _ (P.om k w y) (P.om_one k w y (hnz y hy)) (P.om_mul k w y (hnz y hy)) s hs', C_1]),
          Multiset.map_const', Multiset.prod_replicate, hcard, hdeg, hdim]
      rw [heq.ine ⟨(D.naut.monomial_twist_iff _ _).2 hm, hab⟩ σ hσ, D.naut.inePol_tw _ _ σ hσ]
      exact P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) σ hσ
  intro w M hwM
  rcases hwM with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · have hdeg : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v))).natDegree = D.R.nV := by
      rw [hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
        ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
      rfl
    have h := key _ (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) (hnc _ (Or.inl rfl)) hm0 hdeg (by rw [hlab]; exact hroot0)
    rw [hlab] at h
    exact h
  · obtain ⟨hw, hs⟩ := conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    have h := key w hw hs (hnc w (Or.inr hc)) hm hdeg (by
      rw [hroots]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact inv_ne_zero (hroot0 z hz))
    rw [hroots] at h
    exact h
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.Pass.ResidualSpan
theorem main_alt_alt : _root_.GlobalTheory.Pass.ResidueStatement := by
  intro D hRb _ i r ρ hr π hπ hd
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have h := hRb.2 i hHG _ hrb
  unfold ResSpan
  convert h using 3
  funext g
  first
    | rfl
    | (ext a b; simp [mapM, rhoO, redRep, mapRep])
end GlobalTheory.Pass.ResidualSpan
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.StepGlobalPf
variable {D : D7} (i : D.nd.Loc)
variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  intro hA D i r ρ π Xs eρ eχ hr _ _ hG4 hG5 hG5x hG6 hDec _ hS hZ hπ hl hsel hsha
  obtain ⟨S, hS⟩ := hS
  rw [GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal]
  exact GlobalTheory.CutCore.main hA D i r ρ π Xs eρ eχ S hr hS hZ hπ (noChiOff i r Xs hG6) (unrOut i r ρ π Xs hG4 hDec)
    (atS i r π Xs hG5 hG5x) (atQ i r Xs hG5 hG5x)
    (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eρ).1 (hl w hw).2.1,
      fun c hc => (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eχ).1 ((hl w hw).2.2 c hc)⟩) hsel hsha
end GlobalTheory.StepGlobalPf
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalPass_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  atlas_forward_decl _root_.GlobalTheory.StepGlobalPf.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.Pass
theorem stepsNoCut_of_artin_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := fun hA =>
  ⟨GlobalTheory.CentralIdem.centralIdemCoeff, GlobalTheory.T.central_elements_from_idempotent_coeffs, GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof, _root_.UpperTheory.GalS.stepType_alt, GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension,
    GlobalTheory.PotDual.stepPotDual, GlobalTheory.T.jump_range_positive_sign_place, GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof, GlobalTheory.StepLiftPf.main, GlobalTheory.T.twisted_galois_rep_character_blocks, GlobalTheory.T.twisted_dual_families_continuous,
    GlobalTheory.T.localCountDirectLifting_proof, GlobalTheory.T.localCountDualLifting_proof, GlobalTheory.T.blochKatoCharactersTypePrime_proof, _root_.GlobalTheory.Pass.ResidualSpan.main_alt_alt, _root_.GlobalTheory.T.globalPass_of_globalArtinReciprocity hA⟩
end GlobalTheory.Pass
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := by
  atlas_forward_decl _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
noncomputable section
namespace GlobalTheory.Pass
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cutBound_of_steps_alt : _root_.GlobalTheory.Pass.NoCutStatement → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CT : ℕ), SumRepresentations.adm5 D → ElementDenominator.adm12 D → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π) := by
  rintro ⟨_hCI, _hCen, hDeg, hType, hPotD, hPotDu, hJD, hJDu, hLift, hSub, hCont, hLocD, hLocDu, hHf, hRes, hGlob⟩
  intro D P HW F CT h5 h12 hIne hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB hBK hBC hLGC hFont htie0 hChi
  obtain ⟨hDJ, hPDR, hPT, hBr, hIE⟩ := GlobalTheory.Closing.closing_at_record D
  intro i k k' _hkk' hlk r ρ hr hdec eta s S sg U hs _hlog hCT _hsg hHost hsFin hSha π hπ Xs hπXs hTL
  have hπZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hHG : HG D.nd D.naut i := GlobalTheory.EigenProjector.HG_of_mem_Zgood D i π hπ
  have hdecπ := hdec π hπZ
  have hTLGC : TypeLGC P := hType D P hDZ htie0 hBC hLGC h5
  have hPH : PairedCharacterCondition.tiePH (D := D) := D.loc_tie
  have hl2 : D.nd.l i ≠ 2 := hlk ▸ Formalism.L2.Pj.g_ne_two D k
  have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) (2 * D.R.r * eMax D CT eta) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) (2 * 1 * eMax D CT eta) := by
    intro w hw
    have hdeg1 := (hDeg D hBr i k hlk).2 w hw
    have hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) :=
      hPotD D P hTLGC hFont htie0 hBr hPH hChi hIE h12 hPT hIne i k hlk r ρ hr π hπZ hdecπ Xs hπXs hTL w hw
    have hCT' : CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i := hlk ▸ hCT
    have hH : eta + D.R.t + 1 < s + S := by omega
    have hsub := hSub D i r ρ hr π hdecπ Xs hπXs
    have key : ∀ (kk : ℕ) (M : GE D.nd →* Matrix (Fin kk) (Fin kk) (D.nd.O i)), SubTw i r Xs M →
        LocBoundP i w hw r Xs M (2 * kk * eMax D CT eta) := by
      intro kk M hM
      cases hsw : sg w
      · have hPotDu' := hPotDu D hPT i r hr Xs w hw _ hPot
        have hJ := hJDu D hDJ hPDR i r hr eta s S sg U hs hHost Xs w hw _ hsw hPot
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rDuO D.nd i r x)
          (fun x => (hCont D i r hr x).2) eta (s + S) hH hCT' hPotDu' hJ
        exact hLocDu D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
      · have hJ := hJD D i r eta s S sg U hs hHost Xs w hw hsw
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rTwO D.nd i r x)
          (fun x => (hCont D i r hr x).1) eta (s + S) hH hCT' hPot hJ
        exact hLocD D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
    exact ⟨hHf D P HW F hTB hIE i k hlk hl2 w hw hdeg1, key _ _ hsub.1, fun c hc => key _ _ (hsub.2 c hc)⟩
  have hG1 : TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
    intro g kk
    obtain ⟨f, hf⟩ := (hG14 i r hr).1 g kk
    have e : (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff kk) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [e]
    exact f.2
  have hG4 : TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
    intro x v hl hS hQ g hg
    exact (hG14 i r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
  obtain ⟨S0, hS0, -⟩ := ((hN5g i k hlk hHG r ρ hr).2 π hπZ hdecπ).1 hπZ
  have hG := hGlob D i r ρ π Xs (2 * D.R.r * eMax D CT eta) (2 * 1 * eMax D CT eta) hr hG1
    (hRes D hRbar hG14 i r ρ hr π hπ hdecπ) hG4 (galois_condition_five_of D i r hG5 hHG hr)
    (GlobalTheory.TameDesign.main D i).2 (galois_condition_six_of D i r hG6 hHG hr) hdecπ (coefficient_compatibility_of D i (hBr i))
    ⟨S0, hS0⟩ hπZ hπXs hloc (hsFin π hπ) hSha
  have hcard : (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f := (hDeg D hBr i k hlk).1
  have hnat : (placesOver D.host.E (D.nd.l i)).ncard * (2 * D.R.r * eMax D CT eta + D.R.t * (2 * 1 * eMax D CT eta)) =
      D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) * (CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) +
        (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))))) := by
    rw [hcard]; unfold eMax; ring
  rw [hnat] at hG
  have hrn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr2 : 2 ≤ D.R.r := hRbar.1
  refine ⟨D.R.nV + 1, (D.R.nV + 1) ^ 2 / 4, by omega, le_refl _, ?_, Nat.mul_div_le _ _, ?_⟩
  · have h9 : 9 ≤ (D.R.nV + 1) ^ 2 := by nlinarith
    omega
  · have hG' := (Rat.cast_le (K := ℝ)).2 hG
    push_cast at hG' ⊢
    linarith
end GlobalTheory.Pass
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
noncomputable section
namespace GlobalTheory.BCPerm
abbrev _root_.GlobalTheory.BCPerm.mainTheorem : Prop :=  ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i)
    (P0 PI : D.naut.AV i) (Pa0 Pa : List (Part D.naut.CG)), D.naut.ptV i P0 = some x →
    D.naut.ptV i PI = some x → IsBCV D.nd D.naut i P0 Pa0 → IsBCV D.nd D.naut i PI Pa → Pa0.Perm Pa
end GlobalTheory.BCPerm
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open GlobalTheory.BCPerm
noncomputable section
namespace UpperTheory.GalS
theorem bcPerm_alt : _root_.GlobalTheory.BCPerm.mainTheorem := by
  intro D ht h2 h5 i x P0 PI Pa0 Pa hx hx' hB0 hB
  have hG : GalIsoN D.nd D.naut i := by
    intro P Pb hPb
    obtain ⟨ρ, hc, hss, hw, -⟩ := isoRep D ht (_root_.UpperTheory.GalS.weak' h2) i P Pb hPb
    exact ⟨ρ, hc, hss, hw⟩
  have hC : GlobalTheory.RowTie.ChebSplit D.nd := by
    intro S
    rw [dense_iff_closure_eq]
    exact h5.2.2.1 (S : Set (PlE D.host)) S.finite_toSet
  have hAN : GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := h5.2.1
  have hS := splitBC_of_galIso D.R D.host D.what₂ D.nd D.naut i hG hC hAN
  have hd0 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) ≠ 0 := by
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ (D.nd.S i : Set (PlE D.host)) ∪ (D.nd.Q i : Set (PlE D.host)) ∪
      placesOver D.host.E (D.host.g 0) ∪ placesOver D.host.E (D.host.g 1) ∪
      placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)).Finite := by
    refine (((((GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 0).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 1).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v → D.naut.locV i P0 v = D.naut.locV i PI v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => GlobalTheory.RowTie.locV_eq_of_pt D.nd D.naut i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  exact hS P0 PI hev Pa0 Pa hB0 hB
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Polynomial
namespace GlobalTheory.CutAtGood
section AtPlace
attribute [local instance] Formalism.BasicNotions.Examples₂.NZ.neZero_g Formalism.BasicNotions.Examples₂.NZ.fact_g Classical.propDecidable
variable (D : D7)
end AtPlace
section OnMt
variable (D : D7) (μ : D.what₂.Tup) (j : ℕ)
local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
end OnMt
section Record
variable {D : D7}
theorem isBCV_of_isBCV_of_same_ptV (hT0 : SumRepresentations.tie0 D) (hG : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D) (hBC : SumRepresentations.adm1 D) {i : D.nd.Loc}
    {x : D.nd.X i} {P0 PI : D.naut.AV i} (h0 : D.naut.ptV i P0 = some x) (hx : D.naut.ptV i PI = some x)
    {Pa0 : List (Part D.naut.CG)} (hB0 : IsBCV D.nd D.naut i P0 Pa0) : IsBCV D.nd D.naut i PI Pa0 := by
  obtain ⟨Pa, hPa⟩ := hBC i PI
  have hp := _root_.UpperTheory.GalS.bcPerm_alt D hT0 hG h5 i x P0 PI Pa0 Pa h0 hx hB0 hPa
  exact isBCV_perm hPa hp.symm
end Record
section Series
variable {D : D7}
local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
end Series
section Main
end Main
theorem main_alt_alt : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  intro D P hSer hBC hLGC hT0 h5 hEig hCE i k hl π hπ
  classical
  obtain ⟨hπZN, Sig, hSig, hgood⟩ := (D.Zgood_tie i π).1 hπ
  obtain ⟨σ', hσ'⟩ := P.Par_surj i π Sig hSig
  obtain ⟨P0, hP0, hB0⟩ := hSig
  let s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X] := fun kv => D.ntypes.labPar kv.1 σ' kv.2
  obtain ⟨z, L, hLnd, hLall, hz⟩ := hCE i s
  have hz' : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F := by
    intro F
    rw [hz, list_prod_eq s L hLnd hLall]
    rw [show (D.what₂.restRowsFiniteGroupCard : ℂ) • ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) = (((D.what₂.restRowsFiniteGroupCard : ℂ) • ∏ kv, ef s kv :
          ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl,
      onMt_coe, map_smul]
    rfl
  have hfixπ : ∀ PI : D.naut.AV i, D.naut.ptV i PI = some π → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F = F := by
    intro PI hPI F hF
    have hB := _root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP0 hPI hB0
    have hF' := typeV_le_mtPar hσ' hB hF
    refine cen_prod_fix _ _ _ F fun kv _ => ?_
    rw [← onMt_coe]
    exact series_fix hSer i σ' F hF' kv.1 kv.2
  have hιb : iotaO D.nd D.naut i (D.what₂.restRowsFiniteGroupCard : D.nd.O i) = (D.what₂.restRowsFiniteGroupCard : ℂ) := map_natCast _ _
  have hscal : ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
      (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = (D.what₂.restRowsFiniteGroupCard : D.nd.O i) • u :=
    hEig i z π _ fun PI hPI F hF => by rw [hz', hfixπ PI hPI F hF, hιb]
  let Xs : Set (D.nd.X i) :=
    {x | ∃ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u ≠ 0}
  have hwit : ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
      ∀ kv, D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (ef s kv) F ≠ 0 := by
    rintro x ⟨u, hu, hne⟩
    by_contra hcon
    push Not at hcon
    apply hne
    have h0 := hEig i z x 0 (fun PI hPI F hF => ?_) u hu
    · rw [h0, zero_smul]
    · obtain ⟨kv, hkv⟩ := hcon PI hPI F hF
      rw [hz', map_zero, zero_smul]
      by_contra hc
      have hc' : D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F ≠ 0 := fun h => hc (by rw [h, smul_zero])
      exact cen_prod_ne _ _ _ F hc' kv (Finset.mem_univ kv) hkv
  have hcard : D.what₂.restRowsFiniteGroupCard ≠ 0 := by
    rw [D.nd.restN_card_levelGroup_eq]
    refine Finset.prod_ne_zero_iff.2 fun k' _ => ?_
    have : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
    exact pow_ne_zero _ Nat.card_pos.ne'
  have hb0 : (D.what₂.restRowsFiniteGroupCard : D.nd.O i) ≠ 0 := by
    intro h
    have := congrArg (iotaO D.nd D.naut i) h
    rw [hιb, map_zero] at this
    exact (Nat.cast_ne_zero.2 hcard) this
  have hπX : π ∈ Xs := by
    have hpos : 0 < Module.finrank ℂ ↥(⨆ P ∈ {P | D.naut.ptV i P = some π}, D.naut.typeV i P) := by
      obtain ⟨P2, hP2⟩ := D.naut.pt_surj i π
      refine Nat.pos_of_ne_zero fun h0 => D.naut.typeV_ne i P2 ?_
      have hbot := Submodule.finrank_eq_zero.1 h0
      exact le_bot_iff.1 (hbot ▸ le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) P2 hP2 le_rfl)
    rw [← D.naut.eig_dim i π] at hpos
    have hne : heckeEig (D.nd.T i) (D.nd.act i) π ≠ ⊥ := by
      intro h
      have e : D.nd.mult i π = Module.finrank (FractionRing (D.nd.O i))
          ↥(heckeEig (D.nd.T i) (D.nd.act i) π) := rfl
      rw [e, h, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨u, hu, ?_⟩
    rw [hscal u hu, ← algebraMap_smul (FractionRing (D.nd.O i))]
    refine smul_ne_zero ?_ hu0
    rw [Ne, ← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))]
    exact (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))).ne hb0
  refine ⟨Xs, P.zO i z, (D.what₂.restRowsFiniteGroupCard : D.nd.O i), ⟨hπX, (D.Z_tie i π).2 hπZN, ?_, fun f => P.zO_comm i z f,
    hb0, hscal, fun x hx u hu => ?_, ?_⟩, ?_⟩
  · intro x hx hxZ
    obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
    obtain ⟨Sig1, hS1⟩ := hasParamX_of_Z hT0 h5 hxZ
    obtain ⟨σ1, hσ1⟩ := P.Par_surj i x Sig1 hS1
    obtain ⟨P1, hP1, hB1⟩ := hS1
    have hF1 := typeV_le_mtPar hσ1 (_root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP1 hPI hB1) hF
    have hlab : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), s kv = D.ntypes.labPar kv.1 σ1 kv.2 := fun kv =>
      hSer i σ1 kv.1 kv.2 (s kv) F hF1
        (by rw [show Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)) = ((ef s kv : ↥(Subalgebra.center ℂ
          (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl, onMt_coe]; exact hne kv)
    have hg1 : goodSig D.nd D.naut Sig1 := goodSig_of_labels (fun k' v => by
      rw [← labPar_eq hσ' k' v, ← labPar_eq hσ1 k' v]; exact hlab ⟨k', v⟩) hgood
    exact (D.Zgood_tie i x).2 ⟨(D.Z_tie i x).1 hxZ, Sig1, ⟨P1, hP1, hB1⟩, hg1⟩
  · by_contra h
    exact hx ⟨u, hu, h⟩
  · rw [← hl]
    exact lenUnit_natCast_le i _ hcard
  · refine ⟨fun v => s ⟨k, v⟩, fun v => ?_, fun x hx => ?_⟩
    · show Squarefree (D.ntypes.labPar k σ' v) ∧ ∀ u : (ZMod (D.host.g k))ˣ,
          u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (D.ntypes.labPar k σ' v).IsRoot (u : ZMod (D.host.g k))
      rw [labPar_eq hσ' k v]
      exact good_labels hgood i k v
    · obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
      refine ⟨PI, hPI, fun v => ?_⟩
      have h1 := hne ⟨k, v⟩
      rw [← onMt_coe] at h1
      change D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s ⟨k, v⟩))) F ≠ 0 at h1
      have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
          Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = s ⟨k, v⟩ then (P.lz k).idem τ else 0) ∈
            Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
        intro τ _
        split_ifs
        · exact atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
        · rw [atPlace_zero]
          exact Subalgebra.zero_mem _
      rw [P.eSer_eq k, atPlace_sum, onMt_sum D _ _ _ _ hc, LinearMap.sum_apply] at h1
      obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      by_cases hlab : (P.lz k).lab τ = s ⟨k, v⟩
      · rw [if_pos hlab] at hτ
        exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
      · exfalso
        apply hτ
        rw [if_neg hlab, atPlace_zero]
        unfold NTypes.onMt
        rw [dif_pos (Subalgebra.zero_mem _)]
        have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
        rw [e0, map_zero]
        rfl
end GlobalTheory.CutAtGood
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admBC_of_serLoc : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  atlas_forward_decl _root_.GlobalTheory.CutAtGood.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.TypePrimeEta
end GlobalTheory.TypePrimeEta
namespace GlobalTheory
theorem typePrimeBound_of_etaBound_alt : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory
theorem conclusion_of_typeLocus_alt {D : D7} (P : Pend D) (CT : ℕ)
    (hcut : ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i,
      ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i),
        CutAt i k π Xs β b ∧ TypeLocus P i k Xs)
    (hl5 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π)) :
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := by
  intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hQ := hl5 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hc := hcut i k hl
  choose! Xs β b hcb using hc
  refine ⟨Xs, β, b, fun π hπ => ⟨(hcb π hπ).1, ?_⟩⟩
  exact hQ π hπ (Xs π) (hcb π hπ).1.1 (hcb π hπ).2
theorem admT_of_adm5_eigSpan_tieInePoly : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR D P HW F C CT hC hadm5 hEig hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hSer hTB hBK hBC hLGC htie0 htieChi
  have hSteps : _root_.GlobalTheory.Pass.NoCutStatement := _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity hGAR
  have hCent : CentralElt D := hSteps.2.1 hSteps.1 D P
  have hl5 := _root_.GlobalTheory.Pass.cutBound_of_steps_alt hSteps D P HW F CT hadm5 (GlobalTheory.Per.ResFinite.adm12_elementDenominator D) hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB
    hBK hBC hLGC (GlobalTheory.FontaineAdmissible.fontaineProperties_all_places D) htie0 htieChi
  have hcut := _root_.GlobalTheory.T.admBC_of_serLoc D P hSer hBC hLGC htie0 hadm5 hEig hCent
  have h3 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := _root_.GlobalTheory.conclusion_of_typeLocus_alt P CT hcut hl5
  have h4 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) := by
    intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8
    exact GlobalTheory.EtaFromCut.etaBound_of_cut D CT i k ρ eta
      (h3 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8)
  exact _root_.GlobalTheory.typePrimeBound_of_etaBound_alt D C CT hC h4
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  atlas_forward_decl _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly
end
end
