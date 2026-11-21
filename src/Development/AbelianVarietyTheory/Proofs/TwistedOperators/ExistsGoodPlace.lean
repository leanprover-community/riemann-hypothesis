import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarboux

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T S' T' : HSp D), S'.rank = T.rank → T'.rank = S.rank →
    ∀ (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S),
    Continuous L → Continuous L.symm → (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') →
    (∀ x y, symplO S T (L x) (L y) = symplO S' T' x y) →
    (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) → (∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0) →
    Continuous φ → Continuous φ' → (∀ γ ∈ GQ S', φ γ ∈ GQ T) → (∀ γ ∈ GQ T', φ' γ ∈ GQ S) →
    (∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)) →
    (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) → (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) →
    (∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det) → (∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det) →
    ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
      ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
        ∀ g h (f : WO S T → ℂ), ω' (g, h) (fun u => f (L u)) = fun u => ω (φ' h, φ g) f (L u) := by
  first | exact @GlobalTheory.SwapWeil.isWeilDatumO_swap | exact GlobalTheory.SwapWeil.isWeilDatumO_swap | (intros; apply GlobalTheory.SwapWeil.isWeilDatumO_swap <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_equiv_conj_of_gram_transpose_eq_neg : ∀ (D : D7) (S T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank), T'.gramᵀ = -(S.gram.submatrix e₁ e₁) →
    ∃ φ' : GA D T' ≃* GA D S, Continuous φ' ∧ (∀ γ ∈ GQ T', φ' γ ∈ GQ S) ∧
      (∀ h, (Formalism.L2.Theta.mt S (φ' h)).submatrix e₁ e₁ = (Formalism.L2.Theta.mt T' h).map (cA D)) ∧
      (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) ∧ ∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det := by
  first | exact @GlobalTheory.GrpConj.exists_conj_equiv | exact GlobalTheory.GrpConj.exists_conj_equiv | (intros; apply GlobalTheory.GrpConj.exists_conj_equiv <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  first | exact @GlobalTheory.InvTransposeIso.grp_contra | exact GlobalTheory.InvTransposeIso.grp_contra | (intros; apply GlobalTheory.InvTransposeIso.grp_contra <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  first | exact @GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | exact GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | (intros; apply GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_hom_transpose_gram_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  first | exact @GlobalTheory.DarbouxSymp.symplO_darboux | exact GlobalTheory.DarbouxSymp.symplO_darboux | (intros; apply GlobalTheory.DarbouxSymp.symplO_darboux <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleDarboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)

theorem base_isGood {D : D7} (B : Base D.host.F D.host.E) (hψ : IsStdChar D B.ψ (-1))
    (hP : ∀ v ∈ B.P, ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) : B.IsGood D.sp.cm.sig := by
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := fun v hv => GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v fun hle => hP v hv (Ideal.dvd_iff_le.2 hle) }
  intro v w hw
  have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
    rintro ⟨w1, w2, hne, h1, h2⟩
    apply hne
    have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
      have hle : w.asIdeal ≤ u.asIdeal := by
        rw [← hw]
        exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
      exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
    rw [key w1 h1, key w2 h2]
  obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
  exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩

theorem exists_good_place (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ S ∧ SplitsFully D.host.E v₁ ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  classical
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := mul_ne_zero (mul_ne_zero hn hq) hd
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  refine ⟨v, fun hu => ?_, ?_, ?_⟩
  · refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt v hp ?_ hv
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.TripleDarboux

end
end
