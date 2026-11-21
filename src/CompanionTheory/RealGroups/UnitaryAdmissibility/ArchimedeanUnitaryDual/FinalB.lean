import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementCommutative
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementStar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ModularityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.ArchimedeanDenseStabilizers.StabOfMemLevelOpen
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ArchimedeanPrincipalSeries
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HenselStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneOfHenselAndPairing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SplittingOfSandwichAndPairing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfFrameWittTorus
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LatticeCongruenceSubgroupsOpenCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsometricLatticeCongruenceSubgroups

section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (fixed)

namespace CompanionTheory.Rg.Fl

def LocPI : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F))
      (U : Subgroup (GLoc σ J v)), IsOpen (U : Set (GLoc σ J v)) → ∃ K ≤ U, ∃ M, HasPI K M

theorem locPI_of (h2 : StSimple) (h3 : StStar) (h4 : StHecke) (h5 : StMod) (h7 : StTransfer) (hP : StPair)
    (hU : StCartanU) (hG : StCartanGL) (hM : StMove) (hD : StDict) (hC1 : StDefinite) (hC2 : StSepDef)
    (hC3 : StSepMove) : LocPI := by
  intro F E _ _ _ _ _ σ hc n J hJ v U hUo
  have hcar : HasCartan (GLoc σ J v) := by
    obtain ⟨L, _, _, _, _, h⟩ := hD F E σ hc n J hJ v
    rcases h with ⟨⟨e⟩⟩ | ⟨s, J', a1, a2, a3, a4, a5, ⟨e⟩⟩
    · exact hM _ _ e (hG L n)
    · exact hM _ _ e (hU L s a1 a2 a3 n J' a4 a5)
  obtain ⟨K, hKU, ho, hk, d, l, hcl⟩ := hcar U hUo
  obtain ⟨J', hJ', hpos, ⟨e⟩⟩ := hC1 F E σ hc n J hJ v
  have hco : ((K.map e.toMulEquiv.toMonoidHom : Subgroup _) : Set (GLoc σ J' v)) = e '' K := Subgroup.coe_map _ _
  exact ⟨K, hKU, hasPI_of h2 h3 h4 h5 h7 (hP _ K ho hk) hcl (hC3 _ _ e.toMulEquiv K
    (hC2 F E σ hc n J' hJ' hpos v _ (hco ▸ e.toHomeomorph.isOpenMap _ ho) (hco ▸ hk.image e.continuous)))⟩

theorem admissible_of (hL : LocPI) (hP : StProj) : GlobalTheory.Published.UnitaryIrreducibleAdmissible := by
  intro F E _ _ _ _ _ σ hc n J hJ v H _ _ π hπ U ho _
  haveI := hπ.complete
  obtain ⟨K, hKU, M, hM⟩ := hL F E σ hc n J hJ v U ho
  obtain ⟨P, hP1, -⟩ := hP _ H π hπ.unitary.norm_apply K
  have hfin := (CompanionTheory.D.gk.admitted.finite_rank_of_irreducible_unitary _ H π hπ.unitary.norm_apply (fun S hS h => hπ.irred.2 S ⟨hS, h⟩) P M
    (hM H π hπ.unitary.norm_apply P hP1)).1
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (P : H →ₗ[ℂ] H)) fun x hx => ⟨x, ?_⟩
  exact hP1.2.1 x fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k (hKU hk)

theorem flath_of (hL : LocPI) (hP : StProj) (hV : StFixVec) (hF : StFactor) (hA : StArchPI) (hI : StIso) (hO : StOp)
    (hT : StTensor) : GlobalTheory.Published.FlathTensorProduct := by
  intro F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ
  haveI := hπ.complete
  haveI := hπ.irred.1
  have hcomm : ∀ v x g, projPl σ J v g = 1 → Commute (embPl σ J v x) g := by
    rintro (w | v) x g hg
    · exact commute_embArch σ J x hg
    · exact commute_emb σ J x hg
  have hu : ∀ v, IsUnitaryRep (π.comp (embPl σ J v)) := fun v => isUnitaryRep_comp hπ.unitary (continuous_embPl σ J v)
  have hproj : ∀ v, ∃ P, IsPIProj (π.comp (embPl σ J v)) P := by
    rintro (w | v)
    · exact hA F E σ hc n J hJ w H _ (hu (.inl w))
    · haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
      have h1 : IsUnitaryRep (π.comp (emb σ J v)) := hu (.inr v)
      obtain ⟨U, x, ho, hx, hfix⟩ := hV _ H _ h1.norm_apply h1.continuous_apply
      obtain ⟨K, hKU, M, hM⟩ := hL F E σ hc n J hJ v U ho
      obtain ⟨P, hP1, hP2, hP3⟩ := hP _ H _ h1.norm_apply K
      refine ⟨P, fun h0 => hx ?_, ContinuousLinearMap.ext fun y => hP1.2.1 _ (hP1.1 y), hP2, hP3, M,
        hM H _ h1.norm_apply P hP1⟩
      rw [← hP1.2.1 x fun k hk => hfix k (hKU hk), h0]; rfl
  have hR : ∀ v, ∃ δ : IrrU (GPl σ J v), HasCompPl σ J v δ.π π := fun v => by
    obtain ⟨P, hP'⟩ := hproj v
    obtain ⟨W, hW⟩ := hF _ _ H π hπ.unitary.norm_apply hπ.irred _ _ (projPl_embPl_self σ J v) (hcomm v) P hP'
    exact hI _ _ H π hπ _ _ (continuous_embPl σ J v) (projPl_embPl_self σ J v) (hcomm v) W hW
  choose R hR using hR
  obtain ⟨ξ, B, h⟩ := hT hO hV (admissible_of hL hP) F E σ hc n J hJ H π hπ R hR
  exact ⟨R, ξ, B, h⟩

end CompanionTheory.Rg.Fl

end
end

section
namespace CompanionTheory.Rg.Fl.B

theorem stFrame : CompanionTheory.Rg.FlB.StFrame :=
  GlobalTheory.T.frame_of_anisotropic_plane_splitting (GlobalTheory.T.anisotropic_of_hensel_and_sandwich GlobalTheory.T.HenselStatement GlobalTheory.T.SandwichStatement) (GlobalTheory.T.plane_of_hensel_and_pairing GlobalTheory.T.HenselStatement (GlobalTheory.T.pairing_of_sandwich_statement GlobalTheory.T.SandwichStatement))
    (GlobalTheory.T.splitting_of_sandwich_and_pairing GlobalTheory.T.SandwichStatement (GlobalTheory.T.pairing_of_sandwich_statement GlobalTheory.T.SandwichStatement))

theorem stCartanU : StCartanU :=
  GlobalTheory.T.isometric_lattice_congruence_subgroups GlobalTheory.T.DeltaStatement (GlobalTheory.T.existence_of_sandwich_statement GlobalTheory.T.SandwichStatement) stFrame GlobalTheory.T.TorusStatement (GlobalTheory.T.decomposition_of_frame_witt_torus stFrame GlobalTheory.T.WittStatement GlobalTheory.T.TorusStatement)
    GlobalTheory.T.IwahoriStatement GlobalTheory.T.lattice_congruence_subgroups_open_compact

theorem locPI : LocPI :=
  locPI_of (GlobalTheory.T.simple_of_commutative_statement GlobalTheory.T.StatementCommutative) GlobalTheory.T.StatementStar GlobalTheory.T.HeckeAlgebraTheorem GlobalTheory.T.ModularityStatement GlobalTheory.T.TransferStatementBis GlobalTheory.T.PairingStatement stCartanU GlobalTheory.T.CartanDecompositionGL
    GlobalTheory.T.MovingStatement GlobalTheory.T.DictionaryStatement GlobalTheory.T.DefinitenessStatement CompanionTheory.Rg.FlSep.stSepDefB GlobalTheory.T.SeparatedMovingStatement

theorem unitaryIrreducibleAdmissible : GlobalTheory.Published.UnitaryIrreducibleAdmissible := admissible_of locPI GlobalTheory.T.ProjectionStatement

theorem flathTensorProduct : GlobalTheory.Published.FlathTensorProduct :=
  flath_of locPI GlobalTheory.T.ProjectionStatement GlobalTheory.T.FixedVectorStatement GlobalTheory.T.FactorizationStatement GlobalTheory.T.ArchimedeanPrincipalSeries GlobalTheory.T.IsomorphismStatement GlobalTheory.T.OperatorStatement GlobalTheory.T.stTensor'

end CompanionTheory.Rg.Fl.B
end
