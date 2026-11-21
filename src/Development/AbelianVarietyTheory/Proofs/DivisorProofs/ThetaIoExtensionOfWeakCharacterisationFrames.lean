import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairRecordCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecFockCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPNeZeroCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan

section
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeightCore

open GlobalTheory.JointHarm GlobalTheory.AdTh.MinorWeight

theorem delta_extremal_weight_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ) (t : T0), R.ωP i t (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * diagonal (fun j => cexp ((a j : ℂ) * I)) * (R.MW i (sg0 D A)).fr τ)) (R.ptP i t (RealDat.Delta i)) = cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • R.ptP i t (RealDat.Delta i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i hV τ a t
  have hA := GlobalTheory.PairWeightArith.arithAt D i
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 h.lev i t
  have hε := h.models.order i
  have hθ := h.models.inf
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.JointHarm.weights_of_minors D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) hε
  have hpq : ∀ ρ, ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := fun ρ =>
    (hA ρ).rank.1.trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm
  have hmn : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := pure_one _ (R.vP i t) ▸ h.thP.pt_theta i t 1
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hth
  have hB : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ => by
    obtain ⟨e, he, h1, -⟩ := h.models.BV i ρ
    rw [h1, ← diagonal_one]
    congr 1
    funext j
    rcases he j with hj | hj
    · rw [hj.1]; rfl
    · exact absurd j.2 (not_lt.2 hj.2)
  have hBi : ∀ ρ, (R.BV i ρ)⁻¹ * R.BV i ρ = 1 := fun ρ =>
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse (hB ρ))
  unfold RealDat.ptP
  generalize R.MW i (sg0 D A) = M at hε hx hv ⊢
  have h1 : ∀ ρ, M.fr ρ * (M.fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have hK := diag_mem (ε := M.ε τ) a
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem M τ hK)
  generalize atTau R.θ (Wc D i) τ _ = g at a1 a2 a3 ⊢
  let θs : D.what₂.Tau → Fin (Wc D i).rank → ℝ := fun ρ => if ρ = τ then a else 0
  have hg : ∀ ρ, M.fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) * (M.fr ρ)⁻¹ =
      diagonal fun j => cexp ((θs ρ j : ℂ) * I) := fun ρ => by
    by_cases e : ρ = τ
    · subst e
      rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
        Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      simp only [θs, if_true]
    · rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a3 ρ e, Matrix.mul_one, h1]
      simp [θs, e]
  have e1 : ∀ ρ, (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ = 1 := fun ρ => by
    rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) = 1 from GlobalTheory.PointAtPlaceHom.infMat_one _ _, Matrix.mul_one, hBi]
  have key := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ _ _ _ _ _ _ M (R.BV i) (h.thP.ωP i t) hθ (D.sp.V_sig _) (D.sp.W_sig _) hB _ _ hpq hε
    _ _ (fun ρ => (hI ρ).chiV) (fun ρ => (hI ρ).chiW) x₁ x₂ x₃ (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1)
    (fun ρ => (hx ρ).2.2.1) _ hth hv 1 (one_mem _) g a1 (fun ρ => hg ρ ▸ diag_mem _)).2 (RealDat.Delta i)
  simp only [hg, e1] at key
  rw [key, RealDat.Delta, fact_diagonal M.ε _ _ _ _ x₁ x₂ x₃ hmn hpq hε (fun ρ => (hA ρ).aPlus_antitone) (fun ρ => (hA ρ).aM_anti)
    _ (fun _ _ => Complex.exp_ne_zero _), map_smul]
  congr 1
  rw [Finset.prod_eq_single τ (fun ρ _ e => by simp [θs, e]) (fun e => (e (Finset.mem_univ _)).elim), Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hr := revNeg_shape (Nat.le.intro (hpq τ)) (hε τ) j
  have hj := j.2
  rw [extWt, (hx τ).2.2.2.1, ← Complex.exp_int_mul, wtK, hr]
  congr 1
  by_cases hp : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
  · simp [θs, hp, mul_assoc]
  · rw [if_neg hp, if_neg hp, if_neg (by have := hpq τ; omega),
      show (Wc D i).rank - 1 - ((Wc D i).rank - 1 - (j - ((Wc D i).sig (tauE D τ)).1)) =
        j - ((Wc D i).sig (tauE D τ)).1 by omega]
    simp [θs, mul_assoc]

end GlobalTheory.AdTh.MinorWeightCore
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minorProduct_fockVector_extremalTorusWeight : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ) (t : T0), R.ωP i t (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * diagonal (fun j => cexp ((a j : ℂ) * I)) * (R.MW i (sg0 D A)).fr τ)) (R.ptP i t (RealDat.Delta i)) = cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • R.ptP i t (RealDat.Delta i) := by
  atlas_forward_decl GlobalTheory.AdTh.MinorWeightCore.delta_extremal_weight_core
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtCore
open GlobalTheory.AdTh.IoExtPf

theorem ioExt_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ i, VStd D i) → (∀ i, LowSm (R.MW i (sg0 D A)) ∧ ExtLine (R.MW i (sg0 D A))) → IoExt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i
  obtain ⟨hs, hl⟩ := hM i
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := hR.thP.ioP i A.μ0
  obtain ⟨hth, hvac, hcW, hcV, hbW⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth hvac
    (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A Ks R F hR i (hV i))
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
    (R.vP i A.μ0)
  let f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := pt ∘ₗ (R.ioP i).flip w
  have hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))
  refine ⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩
  have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
  let u : lowT (R.MW i (sg0 D A)) τ := ⟨⟨_, hs τ hm⟩, hm⟩
  have h1 := hK τ _ ha v u rfl w
  rw [hio, GlobalTheory.T.minorProduct_fockVector_extremalTorusWeight D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf] at h1
  have h2 := inj_factor (R.MW i (sg0 D A)) hs hl τ f
    (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)))
    (fun k hk v u hu => hK τ k hk v u hu w) v hv0
    (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by
      rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
        sub_self])
  exact congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ))
    (sub_eq_zero.1 h2)

end GlobalTheory.AdTh.IoExtCore
end

section
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IoExtStd

theorem thetaIoExtension_of_weakCharacterisation_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE hF
  have hB := GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 Ks R F hC hE
  have hcore := hB.1
  have hsh := GlobalTheory.DefLift.holShape_fixed D G Pl0 T0 A3.A Ks R.toRealDat hcore.models.order
  exact GlobalTheory.AdTh.IoExtCore.ioExt_core D G Pl0 T0 A3.A Ks R.toRealDat F.lv2 hcore
    (fun i => GlobalTheory.StdFrame.vStd_of_orthonormal_span D i (hF i))
    (fun i => ⟨GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A3.A Ks R.toRealDat i _,
      GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _ (hsh i).1⟩)

end GlobalTheory.IoExtStd
end

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  atlas_forward_decl GlobalTheory.IoExtStd.thetaIoExtension_of_weakCharacterisation_frames
end
