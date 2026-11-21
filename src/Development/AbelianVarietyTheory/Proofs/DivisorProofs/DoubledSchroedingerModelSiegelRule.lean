import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsRationalOfRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartz
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleDiagonalDoubledSchroedingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledGram_satisfies_xi_relation : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  first | exact @GlobalTheory.DblSchr.dblGram_xi | exact GlobalTheory.DblSchr.dblGram_xi | (intros; apply GlobalTheory.DblSchr.dblGram_xi <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledDarbouxCoords_rational_of_rational : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  first | exact @GlobalTheory.DblSchr.ddr_rat | exact GlobalTheory.DblSchr.ddr_rat | (intros; apply GlobalTheory.DblSchr.ddr_rat <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

theorem exists_dbl_weilDatum_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd ∧
          ∃ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco
  have h1 : Formalism.L2.Theta.IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r0 : Formalism.L2.Theta.ResEta D 1 0 := ⟨rT.1, fun _ _ _ => by simp⟩
  have r1 : Formalism.L2.Theta.ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank :=
    Formalism.L2.Theta.resEta_parity r0 (by show 0 % 2 = (S.rank + S.rank) % 2; omega)
  obtain ⟨ωd, hωd⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp S) T 1 χT hψ h1 hT r1 rT
  refine ⟨ωd, hωd, ?_⟩
  exact GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA
    (GlobalTheory.T.doubledGram_satisfies_xi_relation D S JB ξ hξ) (κ ⊕ κ) (ddr co) (GlobalTheory.T.doubledDarbouxCoords_rational_of_rational D S T JA JB ξ κ co hco) ωd hωd

end GlobalTheory.DblSchr
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubledPairWeilDatum_schrodingerTransport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd ∧
          ∃ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ := by
  atlas_forward_decl GlobalTheory.DblSchr.exists_dbl_weilDatum_transport
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem actAB_one_reG (e : γ ≃ β) {JA : Matrix α α E} {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e)
    (g : GlobalTheory.WeilM.UG c J) (w : Matrix α β E) :
    GlobalTheory.WeilM.actAB c ((1 : GlobalTheory.WeilM.UG c JA), reG c e h g) (w.submatrix id e) =
      (GlobalTheory.WeilM.actB c g w).submatrix id e := by
  simp only [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, reG_val, OneMemClass.coe_one, Units.val_one, Matrix.one_mul,
    Matrix.transpose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

theorem continuous_reG [TopologicalSpace E] (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E}
    (h : J' = J.submatrix e e) : Continuous (reG c e h) := by
  unfold reG
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom ?_).comp continuous_subtype_val
  exact (continuous_id (X := Matrix β β E)).matrix_reindex e.symm e.symm

end Gen

section Read

variable {D : D7} [Invertible (2 : AF D.host.F)]

theorem dblD_rho_eq {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ψ : AddChar (AF D.host.F) ℂ) (w : Matrix (Fin T.rank) (Fin S.rank ⊕ Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (dblD _ co).rho ψ w = (ddr co).rho ψ (w.submatrix id finSumFinEquiv.symm) := by
  unfold GlobalTheory.WeilM.Darboux.rho ddr
  rw [reD_e, Matrix.submatrix_submatrix]
  simp

end Read

end GlobalTheory.DblSchr

namespace GlobalTheory.DblSchr

set_option maxHeartbeats 1000000 in

theorem isUSplitting_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r1 : ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank := GlobalTheory.Core.Rk.IP.FockModel.resEta_one_dbl S rT
  have hξd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hξ
  have hrat := GlobalTheory.DblSchr.ddr_rat D S T JA JB ξ κ co hco
  obtain ⟨hpres, himpl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hadm := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hunit := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hcont := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hom : ∀ g, omdOf omd₀ g = omd₀ (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) := fun _ => rfl
  refine { pres := ?_, impl := ?_, adm := ?_, unit := ?_, cont := ?_ }
  · intro g φ hφ
    rw [hom]
    exact hpres _ φ hφ
  · intro g w φ hφ
    have e1 := dblD_rho_eq co ψ w
    have e2 := dblD_rho_eq co ψ (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) g w)
    have e3 := himpl (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) (w.submatrix id finSumFinEquiv.symm) φ hφ
    have e4 := actAB_one_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (JA := incM D.host.F JA) (incM_JBd S JB) g w
    rw [e4] at e3
    rw [hom]
    exact (congrArg (fun f => omd₀ _ (f φ)) e1).trans (e3.trans (congrFun e2 _).symm)
  · intro g l hl
    rw [hom]
    exact hadm _ l hl
  · exact hunit.comp _
  · have hr := continuous_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB)
    have hp : Continuous fun g => ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)),
        reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB) g) := continuous_const.prodMk hr
    intro l hl φ hφ
    exact Continuous.congr ((hcont l hl φ hφ).comp hp) (fun g => rfl)

end GlobalTheory.DblSchr
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarySplitting_transportedDoubledWeilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  atlas_forward_decl GlobalTheory.DblSchr.isUSplitting_omdOf
end

section
section
namespace DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.DoublingFirstFactor

theorem doubled_first_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  intro D ψ _ S T χS χT ω hω ωd hωd g f₁ f₂ h₁ h₂
  have key := ((GlobalTheory.DoublingTheta.thetaClause D ψ S T χS χT ω ωd hω hωd f₁ f₂ h₁ h₂).2 g 1 1).1
  have e : ω ((1 : GA D S), (1 : GA D T)) = 1 := map_one ω
  rw [key, e, map_one, map_one, inv_one, Circle.coe_one, one_smul]
  rfl

end GlobalTheory.CompanionTheory.DoublingFirstFactor

end

end DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  first | exact @DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | exact DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | (intros; apply DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor <;> assumption)

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  atlas_forward_decl GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj | exact GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj | (intros; apply GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj <;> assumption)
end

section
section
namespace ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInj

theorem schr_reindex {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (σ : κ ≃ κ') (w : (κ' → R) × (κ' → R)) (φ : (κ → R) → ℂ) (x : κ' → R) :
    GlobalTheory.WeilM.schr ψ w (fun u : κ' → R => φ (u ∘ σ)) x =
      GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) φ (x ∘ σ) := by
  have hd : ∀ u v : κ' → R, (u ∘ σ) ⬝ᵥ (v ∘ σ) = u ⬝ᵥ v := fun u v =>
    Equiv.sum_comp σ fun i => u i * v i
  simp only [GlobalTheory.WeilM.schr, hd]
  rfl

theorem thetaSum_reindex (F : Type) [Field F] [NumberField F] {κ κ' : Type} (σ : κ ≃ κ')
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (fun u : κ' → AdeleRing (𝓞 F) F => Φ (u ∘ σ)) = GlobalTheory.WeilM.thetaSum F Φ := by
  unfold GlobalTheory.WeilM.thetaSum
  exact (Equiv.arrowCongr σ.symm (Equiv.refl F)).tsum_eq
    (fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))

theorem theta_transform_injOn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  intro D ψ hψ κ _ Φ hΦ Φ' hΦ' h
  classical
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  have key : ∀ (Ψ : (κ → AF D.host.F) → ℂ) (w : GlobalTheory.ThetaTransform.VA D.host.F (Fintype.card κ)),
      GlobalTheory.ThetaTransform.thV ψ (fun u : Fin (Fintype.card κ) → AF D.host.F => Ψ (u ∘ σ)) w =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ) := by
    intro Ψ w
    rw [← thetaSum_reindex D.host.F σ (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ)]
    unfold GlobalTheory.ThetaTransform.thV
    congr 1
    funext x
    exact schr_reindex ψ σ w Ψ x
  have e := GlobalTheory.ThetaTransform.thV_injOn hR hψ.1 (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ)
    (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ') (funext fun w => by rw [key, key]; exact h _)
  funext x
  have := congrFun e (x ∘ σ.symm)
  simpa [Function.comp_assoc] using this

end GlobalTheory.CompanionTheory.ThetaInj

end

end ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  first | exact @ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | exact ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | (intros; apply ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn <;> assumption)

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  atlas_forward_decl GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestr

open GlobalTheory.Doubling GlobalTheory.DblSchr GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero Formalism.IndefR.Datum

theorem partner_dbl {D : D7} (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
    (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (hgd : gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1) (gs : GA D S) (hgs : mt S gs = (g⁻¹).1.1ᵀ)
    (gdd : GA D (dblSp S)) (hgdd : mt (dblSp S) gdd = ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1ᵀ) :
    gdd = io S (gs, 1) := by
  have hg1 : g.1.1 * (g⁻¹).1.1 = 1 := Units.mul_inv g.1
  have hinv : (gd⁻¹).1.1 = Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hgd, Matrix.fromBlocks_multiply, hg1]
    simp [Matrix.fromBlocks_one]
  have hr : ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1 =
      (Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← map_inv, reG_val, hinv]
  have hm3 : mt (dblSp S) (io S (gs, 1)) =
      (Matrix.fromBlocks (mt S gs) 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  have hm : mt (dblSp S) gdd = mt (dblSp S) (io S (gs, 1)) := by
    rw [hgdd, hr, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, ← hgs, hm3, Matrix.transpose_zero,
      Matrix.transpose_one]
  exact Subtype.ext (Units.ext hm)

theorem restr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omd₀ homd g gd hgd φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨gs, h1, hh1, hgs⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D S T JA JB ξ hA hB 1 g
  have h1e : h1 = 1 := Subtype.ext (Units.ext (hh1.trans rfl))
  obtain ⟨gdd, h2, hh2, hgdd⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D (dblSp S) T JA (JBd S JB) ξ hA (dblGram_xi D S JB ξ hB) 1
    (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)
  have h2e : h2 = 1 := Subtype.ext (Units.ext (hh2.trans rfl))
  have hgdd' : gdd = io S (gs, 1) := partner_dbl S JB g gd hgd gs hgs gdd hgdd
  subst h1e h2e hgdd'
  have t1 := hom 1 g gs 1 hh1 hgs φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  have t2 := homd 1 (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd) (io S (gs, 1)) 1 hh2 hgdd _ hΦ
  have hφ₂' := GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection D.host.F κ φ₂ hφ₂
  have th₁ := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hrat φ₁ hφ₁
  have th₂ := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hrat _ hφ₂'
  have key := t2.2.trans ((congrArg (ωd (io S (gs, 1), 1)) (GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((GlobalTheory.T.doubledWeilDatum_firstFactor_on_doublingTensor D ψ hψ S T χS χT ω hω ωd hωd gs _ _ th₁ th₂).trans
      ((congrArg (fun f => GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f
        (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co _ t1.1 φ₂ hφ₂).symm)))
  refine GlobalTheory.T.thetaTransform_injOn_adelicSchwartzSpace D ψ hψ (κ ⊕ κ) _ t2.1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ t1.1 φ₂ hφ₂) fun w => ?_
  have := congrFun key ((ddr co).e.symm w)
  simpa only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] using this

end GlobalTheory.DblRestr

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realGram_hermitianSpaceDoubled_blockDiagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  atlas_forward_decl GlobalTheory.DblRestr.restr_boxFun
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DblSchr

theorem doubledModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JB))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) co dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JA) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) dd χT (GlobalTheory.WeilM.diagCols (Fin S.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om hom
  obtain ⟨ωd, hωd, omd₀, homd⟩ := GlobalTheory.T.exists_doubledPairWeilDatum_schrodingerTransport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco
  refine ⟨dblD _ co, omdOf omd₀, isDblCoord_dblD _ co,
    ⟨GlobalTheory.WeilM.isLagr_diagCols _ _, GlobalTheory.T.isUnitarySplitting_transportedDoubledWeilDatum D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ωd hωd omd₀ homd,
      GlobalTheory.T.siegelRule_diagonal_doubledSchroedingerModel D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ωd hωd omd₀ homd⟩,
    GlobalTheory.T.realGram_hermitianSpaceDoubled_blockDiagonal D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om hom ωd hωd omd₀ homd⟩

end GlobalTheory.DblSchr
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JB))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) co dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JA) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) dd χT (GlobalTheory.WeilM.diagCols (Fin S.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  atlas_forward_decl GlobalTheory.DblSchr.doubledModel
end
