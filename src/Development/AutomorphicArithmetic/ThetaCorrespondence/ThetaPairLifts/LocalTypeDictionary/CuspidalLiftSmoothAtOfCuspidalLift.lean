import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalLiftsSmoothEverywhere
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFirstStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsSmoothAutomorphic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspTypeApproximationByFockLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelThirdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFifth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFifthStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasTypeAtCuspOfCuspValueType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFirstStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalOfCuspType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalOfCuspTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFirstStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaThirdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFourth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFourthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFifth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFifthStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardThetaLiftIsCuspidalOfIntegrable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftHasKType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFirstStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsSmoothAutomorphicFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelThird
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelThirdStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftHasTypeAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalLiftsSmoothEverywhereStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspThetaConvX
theorem integrableOn_theta_kernel_mul_cusp_form : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ h
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  have hw := (hG.arrows.X i j hi hj).weil
  have hr : GlobalTheory.Grow.RapidDec (G.V i j).V φ :=
    GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  have key := GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hw hΦ hM.1
    hM.2 hr ((GlobalTheory.Grid.ofSgn true _).symm h)
  convert key using 3 with g
  simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.id_apply]
end GlobalTheory.CuspThetaConvX
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_kernel_mul_cusp_form_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) := by
  first | exact @_root_.GlobalTheory.CuspThetaConvX.integrableOn_theta_kernel_mul_cusp_form | exact _root_.GlobalTheory.CuspThetaConvX.integrableOn_theta_kernel_mul_cusp_form | (intros; apply _root_.GlobalTheory.CuspThetaConvX.integrableOn_theta_kernel_mul_cusp_form <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.XArrowCusp
theorem theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsCuspFun (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint
  refine GlobalTheory.CuspLocApprox.isCuspFun_of_locApprox fun C hC ε hε => ?_
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ :=
    _root_.GlobalTheory.T.cusp_type_approximation_by_fock_lift hLC hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε
  have hX := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).X t i j hi hj
  choose F' hF' hE using fun l => hX (f l) (hf l) (F l) (hF l)
  refine ⟨n, fun l => F' l ((G.X i j).It (p l) (v l)), fun l => ?_, fun x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ _ _ _ (F' l) (hF' l) ((G.X i j).It (p l) (v l))
    exact ⟨h1.toIsAutFun.cont, h1.toIsAutFun.left, h2⟩
  · have e : ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω x g
          (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν =
        ∑ l, F' l ((G.X i j).It (p l) (v l)) x :=
      Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
    rw [← e]
    exact happ x hx
end GlobalTheory.XArrowCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsCuspFun (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @_root_.GlobalTheory.XArrowCusp.theta_lift_isCuspidal | exact _root_.GlobalTheory.XArrowCusp.theta_lift_isCuspidal | (intros; apply _root_.GlobalTheory.XArrowCusp.theta_lift_isCuspidal <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory
theorem type_automorphism_lifts_to_theta : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) :=
  _root_.GlobalTheory.T.twisted_theta_lift_isSmoothAutomorphic
end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_type_automorphism : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @_root_.GlobalTheory.type_automorphism_lifts_to_theta | exact _root_.GlobalTheory.type_automorphism_lifts_to_theta | (intros; apply _root_.GlobalTheory.type_automorphism_lifts_to_theta <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftTypeX
theorem theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ τ, IsTypeAt R.θ (G.V (i + 1) j).V τ ((G.V (i + 1) j).S τ) (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  intro hL hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint τ
  have hV : (G.V (i + 1) j).V.SigOK := (hG.spaces.vert i j (by omega) hj).sigOK
  have hAut := _root_.GlobalTheory.T.exists_lift_of_type_automorphism hL hP D hSz G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint
  refine GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ _ τ _ _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hV (goodAt_of_node _ hV τ) hAut ?_
  intro C hC δ hδ
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ := _root_.GlobalTheory.T.cusp_type_approximation_by_fock_lift hL hP D hSz G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by linarith)
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hR hG
  choose F' hF' hE using fun l => hCA.X t i j hi hj (f l) (hf l) (F l) (hF l)
  have hψ0 : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V (i + 1) j).V τ ((G.V (i + 1) j).S τ)
      (∑ l, F' l ((G.X i j).It (p l) (v l))) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ _ τ _).sum_mem fun l _ => _root_.GlobalTheory.T.cusp_value_has_prescribed_type hP R.θ hR.inf _ hV _ (hF' l) _ τ
  obtain ⟨ψ, hψ, hψC⟩ := hψ0 C hC (δ / 2) (by linarith)
  refine ⟨ψ, hψ, fun x hx => ?_⟩
  have h1 := happ x hx
  have h2 := hψC x hx
  have e : (∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω x g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν) = (∑ l, F' l ((G.X i j).It (p l) (v l))) x := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
  rw [e] at h1
  calc _ = ‖((∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω x g Φ * φ g ∂(G.meas t i j).ν) - (∑ l, F' l ((G.X i j).It (p l) (v l))) x) + ((∑ l, F' l ((G.X i j).It (p l) (v l))) x - ψ x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring
end GlobalTheory.ThetaLiftTypeX
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ τ, IsTypeAt R.θ (G.V (i + 1) j).V τ ((G.V (i + 1) j).S τ) (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @_root_.GlobalTheory.ThetaLiftTypeX.theta_lift_hasKType | exact _root_.GlobalTheory.ThetaLiftTypeX.theta_lift_hasKType | (intros; apply _root_.GlobalTheory.ThetaLiftTypeX.theta_lift_hasKType <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaArrowConv
theorem theta_integral_integrableOn_automorphic_quotient : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ h
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨hν, hfd⟩ := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hrd := GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  exact GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hω hΦ hν hfd hrd h
end GlobalTheory.ThetaArrowConv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_integrableOn_automorphic_quotient : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThetaArrowConv.theta_integral_integrableOn_automorphic_quotient | exact _root_.GlobalTheory.ThetaArrowConv.theta_integral_integrableOn_automorphic_quotient | (intros; apply _root_.GlobalTheory.ThetaArrowConv.theta_integral_integrableOn_automorphic_quotient <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaArrowApprox
theorem theta_lift_approx_of_approx_data (hL1 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) (hL2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨hν, hfd⟩ := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hvol := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν hfd
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (G.V i j).V.rank (G.V i (j + 1)).V.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (G.V i j).V (G.V i (j + 1)).V
  obtain ⟨C0, hC0, hK⟩ := (H _ _ rfl rfl).real R.ψ hRB.inf hU
  obtain ⟨Hc, hHc⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ hC
  have hrd := GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  obtain ⟨B, hB⟩ := hrd.2.2 Ae
  set M : ℝ := max Hc 1 with hM
  set Kc : ℝ := C0 * M ^ Ae * 2 ^ Ae with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have kb : ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ h ∈ C, ∀ g,
      ‖thetaKO (G.th t i j).ω h g f‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * GlobalTheory.Grow.quotHeight _ g ^ Ae := by
    intro f hf h hh g
    have hM1 : 0 ≤ GlobalTheory.Grow.height _ h := (GlobalTheory.Grow.height_pos _ h).le
    have hMh : GlobalTheory.Grow.height _ h ^ Ae ≤ M ^ Ae := pow_le_pow_left₀ hM1 ((hHc h hh).trans (le_max_left _ _)) Ae
    have h1 : ∀ g', ‖thetaKO (G.th t i j).ω h g' f‖ ≤
        (C0 * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * M ^ Ae) * GlobalTheory.Grow.height _ g' ^ Ae := by
      intro g'
      refine ((hK _ _ _ hω μ 𝓕 hμ f hf).2 h g').trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMh (mul_nonneg hC0 ENNReal.toReal_nonneg))
        (pow_nonneg (GlobalTheory.Grow.height_pos _ g').le _)
    have := GlobalTheory.Grow.norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf.1 h) h1 g
    refine this.trans (le_of_eq ?_)
    rw [hKc]; ring
  set s0 : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hs0
  set Vl : ℝ := (G.meas t i (j + 1)).ν.real (G.meas t i (j + 1)).fd with hVl
  have hVl0 : 0 ≤ Vl := measureReal_nonneg
  have hs00 : 0 ≤ s0 := ENNReal.toReal_nonneg
  set K0 : ℝ := Kc * s0 with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg hKc0 hs00
  set ε1 : ℝ := δ / (3 * (K0 * Vl + 1)) with hε1
  have hε10 : 0 < ε1 := by positivity
  obtain ⟨n1, F, v, hF, happ⟩ := hL1 D R.θ hRB.inf hP (G.V i (j + 1)) φ hφ Ae ε1 hε10
  set B' : ℝ := max B 0 with hB'
  set η : ℝ := δ / (3 * (Kc * (B' + ε1) * Vl + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n2, f, p, hf, hlev, hsob⟩ :=
    hL2 D R.ψ R.θ hRB.inf hω.std false (G.V i j) (G.V i (j + 1)) U hU Φ hΦU μ 𝓕 hμ d η hη0
  have hsob' : (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d
      (Φ - ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l))).toReal < η :=
    ENNReal.toReal_lt_of_lt_ofReal hsob
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB0 : ∀ g, ‖φ g‖ * GlobalTheory.Grow.quotHeight _ g ^ Ae ≤ B' := fun g => (hB g).trans (le_max_left _ _)
  let e := (finProdFinEquiv : Fin n1 × Fin n2 ≃ Fin (n1 * n2))
  refine ⟨n1 * n2, fun l => f (e.symm l).2, fun l => p (e.symm l).2, fun l => F (e.symm l).1,
    fun l => v (e.symm l).1, fun l => hf _, fun l => hF _, fun h hh => ?_⟩
  have hLCa := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).th t i j hi hj
  have hintl : ∀ l : Fin (n1 * n2), IntegrableOn (fun g => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν := by
    intro l
    obtain ⟨_, _, hall⟩ := hLCa _ (hf (e.symm l).2) _ (hF (e.symm l).1)
    exact (hall _ _ h).1
  rw [← integral_finset_sum _ (fun l _ => hintl l),
    ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hintl l)]
  set Φ' := ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l) with hΦ'
  have hsum : ∀ g, ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g = thetaKO (G.th t i j).ω h g Φ' * ∑ a, F a (v a) g := by
    intro g
    refine (Equiv.sum_comp e.symm (fun ab : Fin n1 × Fin n2 => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f ab.2) (p ab.2)) * F ab.1 (v ab.1) g)).trans ?_
    rw [Fintype.sum_prod_type, hΦ']
    unfold thetaKO
    rw [map_sum, Finset.sum_apply, Finset.sum_mul_sum, Finset.sum_comm]
  have hq : ∀ g, 0 < GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := fun g => pow_pos (GlobalTheory.Grow.quotHeight_pos _ g) _
  have bound : ∀ g, ‖thetaKO (G.th t i j).ω h g Φ * φ g - ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g‖ ≤ K0 * ε1 + Kc * η * (B' + ε1) := by
    intro g
    rw [hsum g]
    have hab : thetaKO (G.th t i j).ω h g Φ - thetaKO (G.th t i j).ω h g Φ' =
        thetaKO (G.th t i j).ω h g (Φ - Φ') := by
      unfold thetaKO; rw [map_sub, Pi.sub_apply]
    have e1 : ∀ a b x y : ℂ, a * x - b * y = a * (x - y) + (a - b) * y := fun a b x y => by ring
    rw [e1, hab]
    have ha : ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := kb Φ hΦU h hh g
    have hxy : ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ ε1 := happ g
    have hd : ‖thetaKO (G.th t i j).ω h g (Φ - Φ')‖ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
      (kb _ hlev h hh g).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsob'.le hKc0) (hq g).le)
    have hy : ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ B' + ε1 := by
      have h3 : ‖∑ a, F a (v a) g‖ ≤ ‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖ := by
        simpa using norm_sub_le (φ g) (φ g - ∑ a, F a (v a) g)
      calc ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae
          ≤ (‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖) * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
            mul_le_mul_of_nonneg_right h3 (hq g).le
        _ = ‖φ g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae +
            ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := add_mul _ _ _
        _ ≤ B' + ε1 := add_le_add (hB0 g) hxy
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖φ g - ∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = K0 * (‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ K0 * ε1 := mul_le_mul_of_nonneg_left hxy hK00
    · rw [norm_mul]
      calc _ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        _ = Kc * η * (‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * η * (B' + ε1) := mul_le_mul_of_nonneg_left hy (by positivity)
  refine (norm_setIntegral_le_of_norm_le_const hvol fun g _ => bound g).trans_lt ?_
  have t1 : K0 * ε1 * Vl ≤ δ / 3 := by
    have h0 : K0 * Vl + 1 ≠ 0 := by positivity
    calc K0 * ε1 * Vl = (K0 * Vl) * ε1 := by ring
      _ ≤ (K0 * Vl + 1) * ε1 := mul_le_mul_of_nonneg_right (by linarith) hε10.le
      _ = δ / 3 := by rw [hε1]; field_simp
  have t2 : Kc * η * (B' + ε1) * Vl ≤ δ / 3 := by
    have h0 : Kc * (B' + ε1) * Vl + 1 ≠ 0 := by positivity
    calc Kc * η * (B' + ε1) * Vl = (Kc * (B' + ε1) * Vl) * η := by ring
      _ ≤ (Kc * (B' + ε1) * Vl + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη0.le
      _ = δ / 3 := by rw [hη]; field_simp
  have : (K0 * ε1 + Kc * η * (B' + ε1)) * Vl = K0 * ε1 * Vl + Kc * η * (B' + ε1) * Vl := by ring
  rw [this]
  linarith
theorem theta_lift_approximates : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ :=
  _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approx_of_approx_data _root_.GlobalTheory.T.twist_cusp_form_approx_weighted GlobalTheory.FockApprox.theta_approx_fock
end GlobalTheory.ThetaArrowApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_by_theta_lifts : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  first | exact @_root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates | exact _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates | (intros; apply _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftTypeTh
theorem thetaLift_hasTypeAt : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint τ
  have hV : (G.V i j).V.SigOK := sigOK_vert G hG hi (by omega)
  intro C hC δ hδ
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ := _root_.GlobalTheory.T.approximation_by_theta_lifts hL hP D hSz G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by linarith)
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hR hG
  choose F' hF' hE using fun l => hCA.th t i j hi hj (f l) (hf l) (F l) (hF l)
  have hψ0 : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ)
      (∑ l, F' l ((G.th t i j).It (p l) (v l))) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ _ τ _).sum_mem fun l _ => _root_.GlobalTheory.T.cusp_value_has_prescribed_type hP R.θ hR.inf _ hV _ (hF' l) _ τ
  obtain ⟨ψ, hψ, hψC⟩ := hψ0 C hC (δ / 2) (by linarith)
  refine ⟨ψ, hψ, fun x hx => ?_⟩
  have h1 := happ x hx
  have h2 := hψC x hx
  have e : (∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω x g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν) = (∑ l, F' l ((G.th t i j).It (p l) (v l))) x := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
  rw [e] at h1
  calc _ = ‖((∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω x g Φ * φ g ∂(G.meas t i (j + 1)).ν) - (∑ l, F' l ((G.th t i j).It (p l) (v l))) x) + ((∑ l, F' l ((G.th t i j).It (p l) (v l))) x - ψ x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring
end GlobalTheory.ThetaLiftTypeTh
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_hasTypeAt_places : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThetaLiftTypeTh.thetaLift_hasTypeAt | exact _root_.GlobalTheory.ThetaLiftTypeTh.thetaLift_hasTypeAt | (intros; apply _root_.GlobalTheory.ThetaLiftTypeTh.thetaLift_hasTypeAt <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaArrowType
theorem theta_lift_of_cusp_form_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint τ
  have hV := sigOK_vert G hG i j hi hj.le
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.V i j).V τ ((G.V i j).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hV (goodPar_of_node (G.V i j) hV τ)
    (_root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint)
    (_root_.GlobalTheory.T.thetaLift_hasTypeAt_places hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint τ)
end GlobalTheory.ThetaArrowType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThetaArrowType.theta_lift_of_cusp_form_hasKType | exact _root_.GlobalTheory.ThetaArrowType.theta_lift_of_cusp_form_hasKType | (intros; apply _root_.GlobalTheory.ThetaArrowType.theta_lift_of_cusp_form_hasKType <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
open GlobalTheory.UpArrowConv
namespace GlobalTheory.UpArrowConv
theorem upward_theta_integral_converges : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ h
  have hω := (hG.arrows.dn i hi).weil
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have key := conj_thetaKO_mul_integrableOn hP.cuspRapidDecay hR.inf hω hΦ hm.1.1 hm.2 hφ.1 hφ.2.1
    ((GlobalTheory.Grid.ofSgn true _).symm h)
  have e : (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) =
      fun g => starRingEnd ℂ (thetaKO ((G.dn i).ω.toSgn true) ((GlobalTheory.Grid.ofSgn true _).symm h) g Φ) * φ g :=
    funext fun g => by rw [thetaKO_toSgn]
  rw [e]
  exact key
end GlobalTheory.UpArrowConv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_integral_converges : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpArrowConv.upward_theta_integral_converges | exact _root_.GlobalTheory.UpArrowConv.upward_theta_integral_converges | (intros; apply _root_.GlobalTheory.UpArrowConv.upward_theta_integral_converges <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.UpCuspLift
theorem upward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsCuspFun (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hLC hPr D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have haut := _root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic hLC hPr D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint
  have hCA := hLC D hS G₀ Pl0 T A Ks R G hR hG
  refine GlobalTheory.CuspApproxCompact.isCuspFun_of_approx D _ _ haut.cont haut.left fun C hC δ hδ => ?_
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ :=
    _root_.GlobalTheory.T.twist_cuspType_lift_approx_fockSpace hLC hPr D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint C hC δ hδ
  choose F' hF' hE using fun l => hCA.up i hi (f l) (hf l) (F l) (hF l)
  have hval := fun l => GlobalTheory.LowVanishObj.multT_apply_cusp R.θ _ _ _ (F' l) (hF' l) (G.ItU i (p l) (v l))
  have hc : Continuous (∑ l, F' l (G.ItU i (p l) (v l))) := by
    rw [Finset.sum_fn]
    exact continuous_finset_sum _ fun l _ => (hval l).1.cont
  have hl : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, (∑ l, F' l (G.ItU i (p l) (v l))) (γ * g) = (∑ l, F' l (G.ItU i (p l) (v l))) g := by
    intro γ hγ g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hval l).1.left γ hγ g
  have hmem := fun l => (GlobalTheory.AutFunCompare.isCuspFun_iff _ _ (hval l).1.cont (hval l).1.left).1 (hval l).2
  refine ⟨∑ l, F' l (G.ItU i (p l) (v l)), hc, hl, ?_, ?_⟩
  · exact (GlobalTheory.AutFunCompare.isCuspFun_iff _ _ hc hl).2 (Submodule.sum_mem _ fun l _ => hmem l)
  · intro h hh
    have e : (∑ l, F' l (G.ItU i (p l) (v l))) h =
        ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g
          (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun l _ => ((hE l (p l) (v l) h).2).symm
    rw [e]
    exact happ h hh
end GlobalTheory.UpCuspLift
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsCuspFun (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpCuspLift.upward_theta_lift_isCuspidal | exact _root_.GlobalTheory.UpCuspLift.upward_theta_lift_isCuspidal | (intros; apply _root_.GlobalTheory.UpCuspLift.upward_theta_lift_isCuspidal <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftTypeUp
theorem thetaLift_hasTypeAt : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint τ
  have hV : (G.P (i + 1)).V.SigOK := (hG.spaces.P (i + 1) (by omega)).sigOK
  intro C hC δ hδ
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ := _root_.GlobalTheory.T.twist_cuspType_lift_approx_fockSpace hL hP D hSz G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint C hC (δ / 2) (by linarith)
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hR hG
  choose F' hF' hE using fun l => hCA.up i hi (f l) (hf l) (F l) (hF l)
  have hψ0 : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ)
      (∑ l, F' l (G.ItU i (p l) (v l))) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ _ τ _).sum_mem fun l _ => _root_.GlobalTheory.T.cusp_value_has_prescribed_type hP R.θ hR.inf _ hV _ (hF' l) _ τ
  obtain ⟨ψ, hψ, hψC⟩ := hψ0 C hC (δ / 2) (by linarith)
  refine ⟨ψ, hψ, fun x hx => ?_⟩
  have h1 := happ x hx
  have h2 := hψC x hx
  have e : (∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω x g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν) = (∑ l, F' l (G.ItU i (p l) (v l))) x := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
  rw [e] at h1
  calc _ = ‖((∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω x g Φ) * φ g ∂(G.mP i).ν) - (∑ l, F' l (G.ItU i (p l) (v l))) x) + ((∑ l, F' l (G.ItU i (p l) (v l))) x - ψ x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring
end GlobalTheory.ThetaLiftTypeUp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_preserves_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.ThetaLiftTypeUp.thetaLift_hasTypeAt | exact _root_.GlobalTheory.ThetaLiftTypeUp.thetaLift_hasTypeAt | (intros; apply _root_.GlobalTheory.ThetaLiftTypeUp.thetaLift_hasTypeAt <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.UpTypeLift
theorem upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hc τ
  have hN := hG.spaces.P (i + 1) (by omega)
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hN.sigOK (GlobalTheory.NodePar.goodPar_of_sigOK (G.P (i + 1)) hN.sigOK τ)
    (_root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc)
    (_root_.GlobalTheory.T.theta_lift_preserves_type hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc τ)
end GlobalTheory.UpTypeLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, IsTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | exact _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType | (intros; apply _root_.GlobalTheory.UpTypeLift.upward_theta_lift_hasKType <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownConv
theorem downward_theta_integral_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ h
  obtain ⟨hν, h𝓕⟩ := MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  exact integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ hν h𝓕 hφ.1 hφ.2.1 h
end GlobalTheory.DownConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_downward_theta_integral_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.DownConv.downward_theta_integral_integrableOn | exact _root_.GlobalTheory.DownConv.downward_theta_integral_integrableOn | (intros; apply _root_.GlobalTheory.DownConv.downward_theta_integral_integrableOn <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColConv
theorem columnConvolution_integrableOn_slice : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t j hj Φ hΦ φ hφ h
  obtain ⟨hν, h𝓕⟩ := measX_haar_fd hG j hj.le
  exact thetaKO_mul_cusp_integrableOn_fst hPr.cuspRapidDecay (hG.arrows.col t j hj).weil hR.inf hν h𝓕 hΦ hφ.1 hφ.2.1 h
end GlobalTheory.ColConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnConvolution_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColConv.columnConvolution_integrableOn_slice | exact _root_.GlobalTheory.ColConv.columnConvolution_integrableOn_slice | (intros; apply _root_.GlobalTheory.ColConv.columnConvolution_integrableOn_slice <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ColCuspDefinite
theorem columnLift_isCuspidal_of_definite : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsCuspFun (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G _ hG t j hj Φ _ φ _ _
  have h := hG.spaces.X j (by omega)
  exact GlobalTheory.DefiniteEnd.isCuspFun_of_definite (V := (G.nX j).V) h.sigOK
    (fun τ => Or.inl (by rw [h.sig τ, h.rank, Nat.sub_zero])) _
end GlobalTheory.ColCuspDefinite
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLift_isCuspForm : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsCuspFun (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColCuspDefinite.columnLift_isCuspidal_of_definite | exact _root_.GlobalTheory.ColCuspDefinite.columnLift_isCuspidal_of_definite | (intros; apply _root_.GlobalTheory.ColCuspDefinite.columnLift_isCuspidal_of_definite <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspSmoothLift
theorem cuspidal_lift_smooth_at_of_cuspidal_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_kernel_mul_cusp_form_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_integral_integrableOn_automorphic_quotient hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_upward_theta_integral_converges hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_downward_theta_integral_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro t j hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.columnConvolution_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.columnLift_isAutomorphicFunction hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_isCuspForm hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_hasTypeAtPlaces hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc⟩
end GlobalTheory.CuspSmoothLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  first | exact @_root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | exact _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | (intros; apply _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift <;> assumption)
end
end
