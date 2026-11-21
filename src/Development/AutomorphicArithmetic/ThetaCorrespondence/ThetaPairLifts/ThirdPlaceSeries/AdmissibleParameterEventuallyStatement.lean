import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundLargeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundLarge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpBoundFamilyLargeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpBoundFamilyLarge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageConditionsOfRankPartStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageConditionsOfRankPart
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageThirdConditionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageThirdCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionThreeOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageSecondConditionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageSecondCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltTer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticUnitAtRamifiedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticUnitAtRamifiedPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticZetaNeOneAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticZetaNeOneAtPlace

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.LargeJumps
theorem jump_bound_of_facts_large_family_alt : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x),
    _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  intro eps Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a hF => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  have hA := (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
  exact _root_.GlobalTheory.JumpStatement.holds_all_alt _ _ (hF.admJ _ hA)
end GlobalTheory.LargeJumps
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_prvJ_of_facts : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  atlas_forward_decl _root_.GlobalTheory.LargeJumps.jump_bound_of_facts_large_family_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.AdmissibleSetting
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  intro D L nch i r π ρ fa _ _ _ hr _ _
  exact ⟨_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i r fa.Conclusion1.1 hr, Formalism.MainNotions.N.continuous_family_of D i r hr,
    Formalism.MainNotions.N.semisimple_family_of D i r hr⟩
end GlobalTheory.AdmissibleSetting
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG1_continuous_admSS_of_rank_r_summand : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  atlas_forward_decl _root_.GlobalTheory.AdmissibleSetting.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
noncomputable section
namespace GlobalTheory.AdmGThreeRest
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG3 i r (fun _ => ρ) π := by
  intro D L nch i r π ρ fa _ _ hHG hr _ hρ
  obtain ⟨hcont, e, he⟩ := hρ
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r (fun _ => ρ) π := ⟨e, fun g u => he g u⟩
  exact _root_.Formalism.MainNotions.N.galois_condition_three_of_alt_alt D i r (fun _ => ρ) π fa.Conclusion1.1 hr hdec hcont hHG fa.rhoBar (litBurnside_host D)
    (fa.duties.2.1 i r hr)
end GlobalTheory.AdmGThreeRest
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG3_of_isRankR_of_lStar_lt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG3 i r (fun _ => ρ) π := by
  atlas_forward_decl _root_.GlobalTheory.AdmGThreeRest.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
noncomputable section
namespace GlobalTheory.AdmGTwoLarge
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → AdmissibleParameterJ.AdmPar L → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG2 i r (fun _ => ρ) π := by
  intro hF D L nch i r π ρ hf hP _ hg _ hr hπ hρ
  have hJ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (hf.admJ L hP)
  have hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r (fun _ => ρ) π := by
    obtain ⟨-, e, he⟩ := hρ
    exact ⟨e, fun g u => he g u⟩
  exact _root_.GlobalTheory.GTwoTheta.main_alt_alt hF D L hf.g2.1 hJ.1 hJ.2.2.1 i r (fun _ => ρ) π hr (hg 0) (hg 1) hπ hD
end GlobalTheory.AdmGTwoLarge
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_of_isRankR_of_lStar_lt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → AdmissibleParameterJ.AdmPar L → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG2 i r (fun _ => ρ) π := by
  atlas_forward_decl _root_.GlobalTheory.AdmGTwoLarge.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut
namespace GlobalTheory.UnrNoChi
variable {D : D7} (i : D.nd.Loc)
end GlobalTheory.UnrNoChi
theorem GlobalTheory.UnrNoChi.main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  intro D L nch i r π ρ hF _ _ hHG hr _ hρ
  have hUnr := _root_.Formalism.MainNotions.N.admG4_of_goodR D i r hF.Conclusion1.1 hr
  have hSub := Formalism.MainNotions.N.galois_condition_six_of D i r hF.Conclusion2.2.1 hHG hr
  refine ⟨?_, ?_⟩
  · intro x _ hxZ u hu
    by_contra hu0
    refine hxZ (hSub x ⟨u, hu0, fun g => ?_⟩)
    have h := hu g
    rw [rTwO, GlobalTheory.UnrNoChi.mapM_twistM', Matrix.smul_mulVec] at h
    conv_rhs => rw [← h]
    rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      one_smul]
  · intro v hvl hvS hvQ x _ γ hγ
    have hχ := GlobalTheory.UnrNoChi.chi_one_eq_one i r π ρ hρ (hUnr π v hvl hvS hvQ γ hγ)
    have hx : rO D.nd i r x γ = 1 := by simp [rO, hUnr x v hvl hvS hvQ γ hγ]
    rw [rTwO, twistM]
    simp [hx, hχ]
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noChiOff_and_unrOut_of_large_good_place : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  atlas_forward_decl _root_.GlobalTheory.UnrNoChi.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.TheoremFiveAtS
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v := by
  intro D L nch i r π ρ hF _ _ hHG hr _ _ v hv
  have hIne : TruncatedSeriesCountingIdentities.admG5 i r := galois_condition_five_of D i r hF.Conclusion2.1 hHG hr
  have hTame : TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := (GlobalTheory.TameDesign.main D i).2
  have hS := ((D.nd.S_def i v).1 hv).1
  have hvI := hIne v (Or.inl hv)
  have hvT := hTame v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hvI.2 hk hv hvT.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hvI.1 (Or.inr hp)) x).1 γ hγ, hvT.2.2.2 hv hp⟩
end GlobalTheory.TheoremFiveAtS
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadAt_unit_zeta_sub_one_or_polyAt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v := by
  atlas_forward_decl _root_.GlobalTheory.TheoremFiveAtS.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.QuadAtQ
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  intro D L nch i r π ρ fa _ _ hHG hr _ _ v hv
  exact ⟨fun x _ γ hγ => ((galois_condition_five_of D i r fa.Conclusion2.1 hHG hr v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ,
    ((GlobalTheory.TameDesign.main D i).2 v (Or.inr hv)).2.2.1 hv⟩
end GlobalTheory.QuadAtQ
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadAt_and_zeta_ne_one_of_large_place : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  atlas_forward_decl _root_.GlobalTheory.QuadAtQ.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
private theorem admissible_parameter_eventually {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (a : Fm.Ix x), AdmissibleParameterJ.AdmPar (Fm.L x a) := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  exact (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
theorem GlobalTheory.NLinkE.main_alt_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  intro hP eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.T.exists_localPositionData_off_exceptional_primes Fm
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.T.eventually_prvJ_of_facts Fm
  obtain ⟨x3, h3⟩ := admissible_parameter_eventually Fm
  refine ⟨max (max x1 x2) x3, fun x hx' hx1 a hF => ?_⟩
  have hx : max x1 x2 ≤ x := le_trans (le_max_left _ _) hx'
  have hA := h3 x (le_trans (le_max_right _ _) hx') hx1 a
  have hJ := h2 x (le_trans (le_max_right _ _) hx) hx1 a hF
  intro k hl hg hexc _hW hHG r hr π hπ ρ hρ
  have hlp : (Fm.D x a).nd.l k |>.Prime := ((Fm.D x a).nd.lPrime k).out
  obtain ⟨⟨h5, ht, hq, hd, hsm⟩, hposition⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 a hJ _ hlp hl
  have hur := GlobalTheory.TripleGal.host_ramificationIdx_eq_one (Fm.D x a) _ hlp hsm hq hd
  have heps := GlobalTheory.AdmissibleDictionary.main (Fm.D x a) k
  obtain ⟨g1, gc, gss⟩ := _root_.GlobalTheory.T.admG1_continuous_admSS_of_rank_r_summand _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g3 := _root_.GlobalTheory.T.admG3_of_isRankR_of_lStar_lt _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g2 := _root_.GlobalTheory.T.admG2_of_isRankR_of_lStar_lt hP.font _ _ _ k r π ρ hF hA hl hg hHG hr hπ hρ
  obtain ⟨gno, gunr⟩ := _root_.GlobalTheory.T.noChiOff_and_unrOut_of_large_good_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gS := _root_.GlobalTheory.T.quadAt_unit_zeta_sub_one_or_polyAt _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gQ := _root_.GlobalTheory.T.quadAt_and_zeta_ne_one_of_large_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition k r (fun _ => ρ) π := hρ.2
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia _ k r (fun _ => ρ) π hr g1 g3 gc gss gdec heps g3.2.2 hπ hur ht
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x a)
  have hTOP := GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar hP.bk hP.tate hP.euler (Fm.D x a) HW F Cm
  have hloc := GlobalTheory.UseLoc.main (Fm.D x a) HW F k r (fun _ => ρ) π hTOP (GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists _ HW F) hJ.1 hr hπ g2 g3 gc gdec heps h5 hsm hq hd
    (fun n _ up τ => hposition hexc _ ((Fm.D x a).nd.j_range k).1 ((Fm.D x a).nd.j_range k).2 n up τ)
  exact GlobalTheory.T.congruenceBound_extended_of_rationalBound _ k π ρ hπ (fun v hv => (gQ v hv).2)
    (fun hs hsha => GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit hP.artin _ k r _ π S hr hS hπ gno gunr gS gQ hloc hs hsha)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_congBound_of_facts : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  atlas_forward_decl _root_.GlobalTheory.NLinkE.main_alt_alt
end
end
