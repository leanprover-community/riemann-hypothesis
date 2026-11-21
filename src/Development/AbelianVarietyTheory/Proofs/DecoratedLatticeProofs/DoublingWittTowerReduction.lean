import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SphericalSectionOfMemCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentityStatement

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Aniso

theorem thetaKO_one_translate {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (f : WO S T → ℂ) : thetaKO om 1 h (om (g, 1) f) = thetaKO om g h f := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem thetaKernel_rationalSource_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (c : GA D S) (h : GA D T) :
    thetaKO om (γ * c) h f = thetaKO om c h f := by
  unfold thetaKO
  have e : om (γ * c, h) = om (γ, (1 : GA D T)) * om (c, h) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (GQ T).one_mem _ (hω.om_pres (c, h) f hf)

theorem thetaInt_translate {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (mT : Measure (GA D T)) (g : GA D S) (f : WO S T → ℂ) :
    thetaInt om mT (om (g, 1) f) 1 = thetaInt om mT f g := by
  simp only [thetaInt, thetaPair, thetaKO_one_translate]

theorem dblInt_thetaInt_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → ∀ g, ThetaPairConv omh mW φ' 1 g) → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (thetaInt omh mW φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro D ψ θ A cA a hDef W χ omh hω m mW hm hmW u hu hinv hK hconv φ hφ hKf
  obtain ⟨φ', hφ', hΛ⟩ := GlobalTheory.T.theta_kernel_exists_for_continuous D ψ θ A cA a hDef W χ omh hω φ hφ hKf m hm u hu hinv

  have hker : ∀ h, thetaKO omh 1 h φ' = 0 := by
    intro h
    have e := hΛ (fun f => thetaKO omh 1 h f)
      (fun f f' _ _ => by simp only [thetaKO, map_add, Pi.add_apply])
      (fun c f _ => by simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul])
      (fun γ hγ g => by
        simp only [thetaKO_one_translate]
        exact thetaKernel_rationalSource_invariant hω hφ hγ g h)
    simp only [thetaKO_one_translate] at e
    rw [← e]
    exact hK φ hφ h
  have hΛ' := hΛ (fun f => thetaInt omh mW f 1)
    (fun f f' hf hf' => by
      simp only [thetaInt, thetaPair]
      have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h (f + f') * (1 : GA D W → ℂ) h)
          = fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h f * (1 : GA D W → ℂ) h) q
            + GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h f' * (1 : GA D W → ℂ) h) q := by
        funext q
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add, Pi.add_apply, add_mul]
      rw [e, average_eq, average_eq, average_eq, integral_add (hconv f hf 1) (hconv f' hf' 1), smul_add])
    (fun c f _ => by
      simp only [thetaInt, thetaPair]
      have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h (c • f) * (1 : GA D W → ℂ) h)
          = fun q => c * GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h f * (1 : GA D W → ℂ) h) q := by
        funext q
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [e, average_eq, average_eq, integral_const_mul, mul_smul_comm])
    (fun γ hγ g => by
      rw [thetaInt_translate, thetaInt_translate]
      simp only [thetaInt, thetaPair]
      have e : (fun h => thetaKO omh (γ * g) h φ * (1 : GA D W → ℂ) h)
          = fun h => thetaKO omh g h φ * (1 : GA D W → ℂ) h := by
        funext h
        rw [thetaKernel_rationalSource_invariant hω hφ hγ g h]
      rw [e])
  have ef : thetaInt omh mW φ = fun g => thetaInt omh mW (omh (g, 1) φ) 1 := by
    funext g
    rw [thetaInt_translate]
  rw [ef, hΛ']
  simp only [thetaInt, thetaPair]
  have e0 : GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h φ' * (1 : GA D W → ℂ) h) = fun _ => 0 := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, hker, zero_mul]
  rw [e0]
  simp

end GlobalTheory.Core.Rk.Aniso

end
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_killing_implies_vanishing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → ∀ g, ThetaPairConv omh mW φ' 1 g) → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (thetaInt omh mW φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  first | exact @GlobalTheory.Core.Rk.Aniso.dblInt_thetaInt_eq_zero | exact GlobalTheory.Core.Rk.Aniso.dblInt_thetaInt_eq_zero | (intros; apply GlobalTheory.Core.Rk.Aniso.dblInt_thetaInt_eq_zero <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_centre_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (z : MvPolynomial ℕ ℂ), (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → omCentreT om θ τ z (f + f') = omCentreT om θ τ z f + omCentreT om θ τ z f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → omCentreT om θ τ z (c • f) = c • omCentreT om θ τ z f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g h, thetaKO om g h (omCentreT om θ τ z f) = centreAct θ τ T z (fun h' => thetaKO om g h' f) h := by
  first | exact @GlobalTheory.Core.Rk.ZcComm.omCentreT_comm | exact GlobalTheory.Core.Rk.ZcComm.omCentreT_comm | (intros; apply GlobalTheory.Core.Rk.ZcComm.omCentreT_comm <;> assumption)
end

section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.RegAdd

theorem analytic_on_auxiliary_eisenstein {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D))
    (hA : EisensteinContinues d b) (h : GA D T) : AnalyticOnNhd ℂ (sphericalEisenstein d b h) (rightOf (rhoH T r)) := by
  have e : sphericalEisenstein d b h = fun s => ∑' q, (fun _ => (1 : ℂ)) q *
      npow ((fun q => GlobalTheory.Eis.term (stab d) (GQ T) (iwAbs (absDet d) (Kmax T b)) h q) q) (s - (-(rhoH T r : ℂ))) := by
    funext s
    simp only [sphericalEisenstein, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add]
  rw [e]
  refine GlobalTheory.Eis.analyticOnNhd_tsum_npow (fun _ => iwAbs_pos _ _ _) fun s hs => ?_
  have := hA.1 s hs h
  simpa only [GlobalTheory.Eis.CosetConv, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add] using this

end GlobalTheory.Core.Rk.RegAdd

open GlobalTheory.Core.Rk.RegAdd in
theorem GlobalTheory.Core.Rk.regRes_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χS χ : (AE D)ˣ →* Circle) (omh : WRep S W), IsInfFam θ → IsWeilDatumO ψ S W χS χ omh → ∀ mW : Measure (GA D W), EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), (∀ φ', IsThetaFunO ψ S W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → (∀ f f', IsThetaFunO ψ S W f → IsThetaFunO ψ S W f' → ∀ g, regRes omh mW θ τ d₀ b' zH P (f + f') g = regRes omh mW θ τ d₀ b' zH P f g + regRes omh mW θ τ d₀ b' zH P f' g) ∧ ∀ (c : ℂ) f, IsThetaFunO ψ S W f → ∀ g, regRes omh mW θ τ d₀ b' zH P (c • f) g = c * regRes omh mW θ τ d₀ b' zH P f g := by
  intro D ψ θ S W W₀ r' d₀ b' χS χ omh hθ hW mW hA τ zH P hR
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.omega_centre_linear D ψ θ S W χS χ omh hθ hW τ zH
  have hhol : ∀ s : ℂ, rhoH W r' < s.re → ∀ h, HolValueAt (sphericalEisenstein d₀ b' h) s (sphericalEisenstein d₀ b' h s) :=
    fun s hs h => holValueAt_self (analytic_on_auxiliary_eisenstein d₀ b' hA h) hs
  have hconv : ∀ φ, IsThetaFunO ψ S W φ → ∀ g (s : ℂ), rhoH W r' < s.re →
      ThetaPairConv omh mW (omCentreT omh θ τ zH φ) (fun h => sphericalEisenstein d₀ b' h s) g :=
    fun φ hφ g s hs => (((hR φ hφ).2 g).2.2 s _ (hhol s hs)).1
  have hcoef : ∀ φ, IsThetaFunO ψ S W φ → ∀ g, CoeffAt (regInt omh mW θ τ d₀ b' zH P φ g) (rhoH W r') (-1)
      (regRes omh mW θ τ d₀ b' zH P φ g) := fun φ hφ g => by
    obtain ⟨H, hH⟩ := ((hR φ hφ).2 g).1
    exact coeffAt_laurent (hH.subset_contDom (Set.mem_univ _)) _
  refine ⟨fun f f' hf hf' g => ?_, fun c f hf g => ?_⟩
  · have e : EqRight (fun s => regInt omh mW θ τ d₀ b' zH P f g s + regInt omh mW θ τ d₀ b' zH P f' g s)
        (regInt omh mW θ τ d₀ b' zH P (f + f') g) := by
      refine ⟨rhoH W r', fun s hs => ?_⟩
      simp only [regInt, thetaPair, hadd f f' hf hf', MeasureTheory.average]
      rw [← mul_add, ← MeasureTheory.integral_add (hconv f hf g s hs).to_average (hconv f' hf' g s hs).to_average]
      congr 1
      refine congrArg _ (funext fun q => ?_)
      simp only [AutomorphicL2Unitary.descend, thetaKO, map_add, LinearMap.add_apply, Pi.add_apply, add_mul]
    exact (((hcoef f hf g).add (hcoef f' hf' g)).congr e).laurent_eq
  · have e : EqRight (fun s => c * regInt omh mW θ τ d₀ b' zH P f g s) (regInt omh mW θ τ d₀ b' zH P (c • f) g) := by
      refine ⟨0, fun s _ => ?_⟩
      simp only [regInt, thetaPair, hsmul c f hf, MeasureTheory.average]
      rw [mul_left_comm, ← MeasureTheory.integral_const_mul]
      congr 1
      refine congrArg _ (funext fun q => ?_)
      simp only [AutomorphicL2Unitary.descend, thetaKO, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact (((hcoef f hf g).const_mul c).congr e).laurent_eq
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularised_integral_linear_properties : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χS χ : (AE D)ˣ →* Circle) (omh : WRep S W), IsInfFam θ → IsWeilDatumO ψ S W χS χ omh → ∀ mW : Measure (GA D W), EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), (∀ φ', IsThetaFunO ψ S W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → (∀ f f', IsThetaFunO ψ S W f → IsThetaFunO ψ S W f' → ∀ g, regRes omh mW θ τ d₀ b' zH P (f + f') g = regRes omh mW θ τ d₀ b' zH P f g + regRes omh mW θ τ d₀ b' zH P f' g) ∧ ∀ (c : ℂ) f, IsThetaFunO ψ S W f → ∀ g, regRes omh mW θ τ d₀ b' zH P (c • f) g = c * regRes omh mW θ τ d₀ b' zH P f g := by
  atlas_forward_decl GlobalTheory.Core.Rk.regRes_linear
end

section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.Core.Rk.RegKill

variable {D : D7}

theorem foldr_ops_zero {X : Type} (l : List ((X → ℂ) → (X → ℂ))) (hl : ∀ f ∈ l, f 0 = 0) :
    l.foldr (fun f acc => f acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.foldr_cons, ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))]
    exact hl f List.mem_cons_self

theorem opPow_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (k : ι →₀ ℕ) :
    opPow A k 0 = 0 := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, hA]

theorem centreAct_zero (θ : InfFam D) (τ : D.what₂.Tau) (T : HSp D) (p : MvPolynomial ℕ ℂ) :
    centreAct θ τ T p (0 : GA D T → ℂ) = 0 := by
  have hR : ∀ Z, RderC θ T τ Z (0 : GA D T → ℂ) = 0 := by
    intro Z
    funext g
    simp [RderC, Rder]
  have hg : ∀ k, gelf θ T τ k (0 : GA D T → ℂ) = 0 := by
    intro k
    funext g
    simp only [gelf]
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun idx _ => ?_
    rw [foldr_ops_zero]
    · rfl
    · intro f hf
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact hR _
  unfold centreAct polyAct
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [opPow_zero _ hg, smul_zero]

theorem laurent_zero (s₀ : ℂ) (n : ℤ) : laurent (fun _ : ℂ => (0 : ℂ)) s₀ n = 0 :=
  CoeffAt.laurent_eq ⟨_, isExtAt_const 0 s₀, laurentConst_of_tendsto (by simpa using tendsto_const_nhds)⟩

section
variable {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

theorem thetaKO_one_om (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    thetaKO om 1 h (om (g, 1) f) = thetaKO om g h f := by
  unfold thetaKO
  have e : (((1 : GA D S), h) : GA D S × GA D T) * (g, 1) = (g, h) := by ext <;> simp
  rw [← Module.End.mul_apply, ← map_mul, e]

theorem thetaKO_rat {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} (hω : IsWeilDatumO ψ S T χS χT om)
    {γ : GA D S} (hγ : γ ∈ GQ S) (g : GA D S) (h : GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    thetaKO om (γ * g) h f = thetaKO om g h f := by
  unfold thetaKO
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by ext <;> simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

end

theorem dblInt_regRes_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), P ≠ 0 → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (regRes omh mW θ τ d₀ b' zH P φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro D ψ θ A cA a hDef W W₀ r' d₀ b' χ omh hW m mW hm hmW u hu hinv hK hAux τ zH P hP hReg φ hφ hfin
  obtain ⟨φ', hφ', hcol⟩ := GlobalTheory.T.theta_kernel_exists_for_continuous D ψ θ A cA a hDef W χ omh hW φ hφ hfin m hm u hu hinv
  have hZ := GlobalTheory.T.omega_centre_linear D ψ θ (dblSp A) W 1 χ omh hDef.inf hW τ zH
  have hzero : ∀ h, thetaKO omh 1 h φ' = 0 := by
    intro h
    have e := hcol (fun f => thetaKO omh 1 h f)
      (fun f f' _ _ => by simp [thetaKO, map_add])
      (fun c f _ => by simp [thetaKO, map_smul])
      (fun γ hγ g => by
        simp only [thetaKO_one_om]
        exact thetaKO_rat omh hW hγ g h hφ)
    rw [← e]
    simp only [thetaKO_one_om]
    exact hK φ hφ h
  have hshift : ∀ f, IsThetaFunO ψ (dblSp A) W f → ∀ g,
      regRes omh mW θ τ d₀ b' zH P (omh (g, 1) f) 1 = regRes omh mW θ τ d₀ b' zH P f g := by
    intro f hf g
    have hf1 := hW.om_pres (g, 1) f hf
    unfold regRes
    congr 1
    funext s
    unfold regInt thetaPair
    congr 2
    funext q
    unfold AutomorphicL2Unitary.descend
    beta_reduce
    congr 1
    rw [hZ.2.2 _ hf1, hZ.2.2 _ hf]
    simp only [thetaKO_one_om]
  have hrat : ∀ f, IsThetaFunO ψ (dblSp A) W f → ∀ γ ∈ GQ (dblSp A), ∀ g,
      regRes omh mW θ τ d₀ b' zH P f (γ * g) = regRes omh mW θ τ d₀ b' zH P f g := by
    intro f hf γ hγ g
    have hF := (hReg f hf).1
    unfold regRes
    congr 1
    funext s
    unfold regInt thetaPair
    congr 2
    funext q
    unfold AutomorphicL2Unitary.descend
    beta_reduce
    rw [thetaKO_rat omh hW hγ g _ hF]
  have hlin := GlobalTheory.T.regularised_integral_linear_properties D ψ θ (dblSp A) W W₀ r' d₀ b' 1 χ omh hDef.inf hW mW hAux τ zH P hReg
  have e := hcol (fun f => regRes omh mW θ τ d₀ b' zH P f 1)
    (fun f f' hf hf' => hlin.1 f f' hf hf' 1)
    (fun c f hf => hlin.2 c f hf 1)
    (fun γ hγ g => by
      rw [hshift _ hφ, hshift _ hφ, hrat _ hφ γ hγ])
  have hfun : (fun g => regRes omh mW θ τ d₀ b' zH P (omh (g, 1) φ) 1) = regRes omh mW θ τ d₀ b' zH P φ :=
    funext (hshift φ hφ)
  rw [hfun] at e
  rw [e]
  have hI : regInt omh mW θ τ d₀ b' zH P φ' 1 = fun _ => 0 := by
    funext s
    unfold regInt thetaPair
    have hint : (fun h => thetaKO omh 1 h (omCentreT omh θ τ zH φ') * sphericalEisenstein d₀ b' h s) = fun _ => (0 : ℂ) := by
      funext h
      rw [hZ.2.2 _ hφ']
      have h0 : (fun h' => thetaKO omh 1 h' φ') = (0 : GA D W → ℂ) := funext hzero
      rw [h0, centreAct_zero]
      simp
    rw [hint]
    simp [AutomorphicL2Unitary.descend]
  show laurent (regInt omh mW θ τ d₀ b' zH P φ' 1) (rhoH W r') (-1) = 0
  rw [hI]
  exact laurent_zero _ _

end GlobalTheory.Core.Rk.RegKill

end
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kill_witt_decomposition : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), P ≠ 0 → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (regRes omh mW θ τ d₀ b' zH P φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  atlas_forward_decl GlobalTheory.Core.Rk.RegKill.dblInt_regRes_eq_zero
end

section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.Core.Rk.WittDec

variable {D : D7}

theorem isoFrame_le {W : HSp D} {r : ℕ} {C : Matrix (Fin W.rank) (Fin r) D.host.E} (h : IsIsoFrame W C) :
    r ≤ W.rank := by
  have := h.2.1.fintype_card_le_finrank
  simpa using this

theorem isoFrame_extend {W W₀ : HSp D} {r s : ℕ} (d : HypDec W W₀ r)
    {C₀ : Matrix (Fin W₀.rank) (Fin s) D.host.E} (hC₀ : IsIsoFrame W₀ C₀) :
    ∃ C : Matrix (Fin W.rank) (Fin (r + s)) D.host.E, IsIsoFrame W C := by
  classical
  set M : Matrix (Fin W.rank) (Fin r ⊕ Fin s) D.host.E := Matrix.fromCols d.e (d.i₀ * C₀) with hM
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hi₀e : d.eᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have he'i₀ : d.e'ᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e'
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have hC₀iso : C₀ᴴ * HSpace.gram W₀ * C₀ = 0 := hC₀.2.2
  have hiso : Mᴴ * HSpace.gram W * M = 0 := by
    rw [hM, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    have h1 : d.eᴴ * HSpace.gram W * d.e = 0 := d.ee
    have h2 : d.eᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by rw [← Matrix.mul_assoc, hi₀e, Matrix.zero_mul]
    have h3 : (d.i₀ * C₀)ᴴ * HSpace.gram W * d.e = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e,
        Matrix.mul_zero]
    have h4 : (d.i₀ * C₀)ᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by
      rw [Matrix.conjTranspose_mul, show C₀ᴴ * d.i₀ᴴ * HSpace.gram W * (d.i₀ * C₀) =
        C₀ᴴ * (d.i₀ᴴ * HSpace.gram W * d.i₀) * C₀ by simp only [Matrix.mul_assoc], d.iso, hC₀iso]
    rw [h1, h2, h3, h4, Matrix.fromBlocks_zero]
  have hker : ∀ v, M *ᵥ v = 0 → v = 0 := by
    intro v hv
    rw [hM, Matrix.fromCols_mulVec] at hv
    have ha : v ∘ Sum.inl = 0 := by
      have h := congrArg (fun x => (d.e'ᴴ * HSpace.gram W) *ᵥ x) hv
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rwa [d.e'e, ← Matrix.mul_assoc, he'i₀, Matrix.zero_mul, Matrix.zero_mulVec, add_zero,
        Matrix.one_mulVec] at h
    have hb' : d.i₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [ha, Matrix.mulVec_zero, zero_add] at hv
      rw [Matrix.mulVec_mulVec]; exact hv
    have hb'' : HSpace.gram W₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [← d.iso, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_zero]
    have hc : C₀ *ᵥ (v ∘ Sum.inr) = 0 := Matrix.eq_zero_of_mulVec_eq_zero (gram_det_ne W₀) hb''
    have hinj₀ : Function.Injective C₀.mulVec := Matrix.mulVec_injective_iff.2 hC₀.2.1
    have hb : v ∘ Sum.inr = 0 := hinj₀ (by rw [hc, Matrix.mulVec_zero])
    funext x
    cases x with
    | inl i => exact congrFun ha i
    | inr j => exact congrFun hb j
  refine ⟨M.submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · have := hC₀.1; omega
  · apply Matrix.mulVec_injective_iff.1
    intro v w h
    have hsub : M.submatrix id finSumFinEquiv.symm *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, h, sub_self]
    rw [Matrix.submatrix_mulVec_equiv] at hsub
    have h0 := hker _ (by simpa using hsub)
    have h1 : v - w = 0 := by
      funext i
      have := congrFun h0 (finSumFinEquiv.symm i)
      simpa using this
    exact sub_eq_zero.1 h1
  · show (M.submatrix id finSumFinEquiv.symm)ᴴ * HSpace.gram W * M.submatrix id finSumFinEquiv.symm = 0
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun hiso (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem aniso_or_hypDec (W : HSp D) :
    IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r' := by
  classical
  by_cases hA : IsAniso W
  · exact Or.inl hA
  right
  have hex : ∃ r, ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C := by
    by_contra h
    push_neg at h
    exact hA fun r C => h r C
  obtain ⟨r₁, C₁, hC₁⟩ := hex
  let P : ℕ → Prop := fun r => ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C
  have hPr : P (Nat.findGreatest P W.rank) := Nat.findGreatest_spec (isoFrame_le hC₁) ⟨C₁, hC₁⟩
  have hmax : ∀ s, P s → s ≤ Nat.findGreatest P W.rank := fun s hs =>
    Nat.le_findGreatest (isoFrame_le hs.choose_spec) hs
  obtain ⟨C, hC⟩ := hPr
  obtain ⟨W₀, ⟨hrk, ι, hι, C', hC', horth⟩, -⟩ :=
    GlobalTheory.WittLow.wittLowEx D W (Nat.findGreatest P W.rank) ⟨C, hC.2.1, hC.2.2⟩
  have hpos : 0 < Nat.findGreatest P W.rank := hC.1
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hsplit : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W₀ C' (frameMat W W₀ ι) := by
    refine ⟨⟨hpos, hC'.1, hC'.2⟩, GlobalTheory.AutFunCounterexample.gram_pull W W₀ ι hι, ?_, by omega⟩
    show C'ᴴ * HSpace.gram W * frameMat W W₀ ι = 0
    have h : (frameMat W W₀ ι)ᴴ * HSpace.gram W * C' = 0 := horth
    have h2 := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h2
  obtain ⟨d, -, -, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W₀ _ C' _ hsplit
  refine ⟨W₀, _, d, fun s C₀ hC₀ => ?_, hpos⟩
  obtain ⟨C₂, hC₂⟩ := isoFrame_extend d hC₀
  have h1 := hmax _ ⟨C₂, hC₂⟩
  have h2 := hC₀.1
  omega

theorem maj_and_witt : ∀ (D : D7) (W : HSp D), HSpace.SigOK W →
    (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧
      (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') :=
  fun _ W _ => ⟨GlobalTheory.Doubling.exists_isMaj W, aniso_or_hypDec W⟩

end GlobalTheory.Core.Rk.WittDec
end
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_exists_and_witt_decomposition : ∀ (D : D7) (W : HSp D), HSpace.SigOK W → (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧ (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') := by
  atlas_forward_decl GlobalTheory.Core.Rk.WittDec.maj_and_witt
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section
namespace GlobalTheory.Core.Rk.ResKill

theorem dblInt_smul_left {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} (c : ℂ)
    (E : GA D (dblSp V) → ℂ) (f : GA D V → ℂ) :
    GlobalTheory.Eis.dblInt V μ m (c • E) f f = c * GlobalTheory.Eis.dblInt V μ m E f f := by
  have h := GlobalTheory.Eis.dblInt_smul (V := V) (μ := μ) (m := m) (E := E) (f₁ := f) (f₂ := f) c 1 1
  simpa using h

theorem res_killed : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → ∀ (B W : HSp D) (t : ℕ) (_ : HypDec B W t), HSpace.SigOK B → HSpace.SigOK W → 0 < W.rank → 0 < t → A.rank = W.rank + t → ∀ (χ : (AE D)ˣ →* Circle) (omB : WRep (dblSp A) B) (omW : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) B 1 χ omB → IsWeilDatumO ψ (dblSp A) W 1 χ omW → ∀ ν 𝓕, IsCovolOne (ratL B A) ν 𝓕 → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omW m u → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsKFinVec omB (Khat A a) φ → GlobalTheory.Eis.EisPoleLE A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) 1 ∧ ∃ E₁, GlobalTheory.Eis.EisCoeffAt A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) (-1) E₁ ∧ GlobalTheory.Eis.dblInt A χ⁻¹ m E₁ (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro hPr D ψ θ A cA a hDef h2 B W t d hsB hsW hW ht hA χ omB omW hWB hWW ν 𝓕 hcov m hm u hu hinv hK φ hφ hKφ
  obtain ⟨b, hb⟩ := GlobalTheory.RegSW.Model.exists_isMaj B
  obtain ⟨νK, hνH, hνP⟩ := GlobalTheory.RegSW.Model.exists_haar_Kmax B b
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t (dblSp A).rank
  have hrk := d.rank_add
  have hIwA : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a hDef.maj
  have hIwB : HasIw d (Kmax B b) := GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D B W t d b h2 hb
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hPr D ψ A B W t d (by omega) (by omega) hW χ omB omW hWB hWW a b hDef.maj hb hIwA hIwB
    ν 𝓕 hcov μ₁ 𝓕₁ hμ₁ νK hνH hνP Measure.haar inferInstance
  have hproj : ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK omB νK φ) := fun φ h => (hP1 φ h).1
  have hφ' : IsThetaFunO ψ (dblSp A) W (ikeda ψ d μ₁ 𝓕₁ (projK omB νK φ)) := (hP1 _ (hproj φ hφ)).2
  have hKφ' : IsKFinVec omW (Khat A a) (ikeda ψ d μ₁ 𝓕₁ (projK omB νK φ)) :=
    (GlobalTheory.T.theta_majorant_average_identity D ψ (dblSp A) B W t d 1 χ omB omW hWB hWW b hb νK hνP μ₁ 𝓕₁ hμ₁ hproj).2 (Khat A a) φ hφ hKφ
  refine ⟨hP2 φ hφ hKφ, ?_⟩
  obtain ⟨-, hWitt⟩ := GlobalTheory.T.majorant_exists_and_witt_decomposition D W hsW
  rcases hWitt with hAn | ⟨W₀, r', d₀, hAn₀, hr'⟩
  · obtain ⟨hconv, κ, -, hE⟩ := hP3 hAn
    refine ⟨_, hE φ hφ hKφ, ?_⟩
    rw [dblInt_smul_left, GlobalTheory.T.theta_killing_implies_vanishing D ψ θ A cA a hDef W χ omW hWW m Measure.haar hm inferInstance u hu hinv hK hconv _ hφ'
      hKφ', mul_zero]
  · obtain ⟨b', hb'⟩ := GlobalTheory.RegSW.Model.exists_isMaj W
    have hIw₀ : HasIw d₀ (Kmax W b') := GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D W W₀ r' d₀ b' h2 hb'
    obtain ⟨hAux, hReg, κ, -, hE⟩ := hP4 W₀ r' d₀ hAn₀ hr' b' hb' hIw₀ θ hDef.inf
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
    obtain ⟨zG, zH, P, hzP⟩ := hReg τ
    obtain ⟨hRI, hE'⟩ := hE τ zG zH P hzP
    refine ⟨_, hE' φ hφ hKφ, ?_⟩
    rw [dblInt_smul_left, GlobalTheory.T.theta_kill_witt_decomposition D ψ θ A cA a hDef W W₀ r' d₀ b' χ omW hWW m Measure.haar hm inferInstance u hu hinv hK
      hAux τ zH P hzP.2.2.2 hRI _ hφ' hKφ', mul_zero]

end GlobalTheory.Core.Rk.ResKill
end
end
