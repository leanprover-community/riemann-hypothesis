import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRankStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlThetaLiftIsClosed
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.BernAll
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacTwistMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTransposeInvTranspose
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatProd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairSatPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramified

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

namespace UpperTheory.Gal.TP.Loc

theorem isUnitaryChar_mul {G : Type} [Group G] {a b : G →* ℂˣ} (ha : IsUnitaryChar a) (hb : IsUnitaryChar b) :
    IsUnitaryChar (a * b) := fun g => by
  simp [MonoidHom.mul_apply, ha g, hb g]

theorem isUnitaryChar_inv {G : Type} [Group G] {a : G →* ℂˣ} (ha : IsUnitaryChar a) : IsUnitaryChar a⁻¹ := fun g => by
  simp [ha g]

theorem liftIso_of (hP : PairOfLift) (hS : SrcGood) (hI : ContraIrr) (hU : ContraUnit) : LiftIso := by
  intro k _ _ _ _ n t ν b V _ _ W _ _ σ π hnt sν uν sb ub hs hi hu hs' hi' hL
  obtain ⟨a1, a2, a3⟩ := hS k n (ν * b) V σ (sν.mul sb) (isUnitaryChar_mul uν ub) hs hi hu
  exact GlobalTheory.T.theta_lift_general_linear PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgUd.All.bernsteinUnitaryProductIrreducible
    k n t b⁻¹ _ _ (contra (src (ν * b) σ)) (contra π) hnt sb.inv (isUnitaryChar_inv ub) (isSmooth_contra _)
    (hI k n V _ a1 a2).1 (hU k n V _ a1 a2 a3).1 (isSmooth_contra _) (hI k _ W π hs' hi').1
    (hP k n (n + t) ν b V W σ π sν sb hs' hL)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem liftSat_of (hL : LiftIso) (hS : SrcGood) (hI : ContraIrr) (hU : ContraUnit) (hC : SatContra) (hT : SatTwist)
    (hV : SatInvT) (hD : SatDet) (hP : SatProd) (hG : SegInv) : LiftSat := by
  intro K _ _ w n d ν b V _ _ W _ _ σ π hd nν uν nb ub hs hi hu hs' hi' hl ϖ hϖ B hB
  obtain ⟨t, rfl⟩ : ∃ t, d = n + t := ⟨d - n, by omega⟩
  have sν := isSmoothChar_of_isUnram nν
  have sb := isSmoothChar_of_isUnram nb
  obtain ⟨e⟩ := hL _ n t ν b V W σ π (by omega) sν uν sb ub hs hi hu hs' hi' hl
  obtain ⟨a1, a2, a3⟩ := hS _ n (ν * b) V σ (sν.mul sb) (isUnitaryChar_mul uν ub) hs hi hu
  have nm : IsUnram (ν * b) := fun x hx => by rw [MonoidHom.mul_apply, nν x hx, nb x hx, one_mul]
  have ni : IsUnram b⁻¹ := fun x hx => by rw [MonoidHom.inv_apply, nb x hx, inv_one]
  have s1 : GlobalTheory.LFun.HasSatGL w (src (ν * b) σ) ((B.map (·⁻¹)).map (· * (ν * b) ϖ)) :=
    hT K w n (ν * b) V _ nm ϖ hϖ _ (hV K w n V σ B hB)
  have s2 := hC K w n V _ a1 a2 a3 _ s1
  have s3 := hD K w t b⁻¹ ni ϖ hϖ
  have ud : IsUnitarisable (detRep (Fin t) b⁻¹) := (isUnitarisable_ofChar_iff _).2 fun _ => isUnitaryChar_inv ub _
  have s4 := hP K w n t _ _ _ _ (isSmooth_contra _) (hI _ n V _ a1 a2).1
    ((isSmooth_ofChar_iff _).2 sb.inv.detChar) (isIrreducible_ofChar _) _ _ s2 s3
  have s5 := GlobalTheory.PrinSat.hasSatGL_of_equiv e s4
  have u5 : IsUnitarisable (contra π) :=
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv e.symm (GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂ (hU _ n V _ a1 a2 a3).1 ud)
  have s6 := hC K w (n + t) _ _ (isSmooth_contra π) (hI _ _ W π hs' hi').1 u5 _ s5
  obtain ⟨e'⟩ := (hI _ _ W π hs' hi').2
  have s7 := GlobalTheory.PrinSat.hasSatGL_of_equiv e' s6
  rw [Multiset.map_add, hG] at s7
  simpa [Multiset.map_map, mul_comm] using s7

end UpperTheory.Gal.TP.Loc

end
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.leftSmooth :
    UpperTheory.Gal.TP.Loc.LeftSmooth := by
  intro k _ _ _ _ n d Φ
  obtain ⟨hlc, hcs⟩ := Φ.2
  have key : ∀ f : GL (Fin n) k → Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k,
      Continuous (fun p : GL (Fin n) k × Matrix (Fin n) (Fin d) k => f p.1 p.2) → (∀ X, f 1 X = X) →
      ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ),
        (Φ : Matrix (Fin n) (Fin d) k → ℂ) (f g X) = (Φ : Matrix (Fin n) (Fin d) k → ℂ) X := by
    intro f hf h1
    apply hcs.isCompact.eventually_forall_of_forall_eventually
    intro X₀ _
    have e1 := (hlc.comp_continuous hf).eventually_eq (1, X₀)
    have e2 := (hlc.comp_continuous
      (continuous_snd : Continuous (Prod.snd : GL (Fin n) k × Matrix (Fin n) (Fin d) k → _))).eventually_eq (1, X₀)
    filter_upwards [e1, e2] with p hp1 hp2
    simp only [Function.comp] at hp1 hp2
    rw [hp1, hp2, h1]
  have hU1 := key (fun g X => (g : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  have hU2 := key (fun g X => ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  filter_upwards [hU1, hU2] with g hg1 hg2
  intro X
  by_cases hX : X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · exact hg1 X hX
  by_cases hgX : (g : Matrix (Fin n) (Fin n) k) * X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · have := hg2 _ hgX
    rw [← Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hgX]
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def mulHomeo {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ}
    (a : (Matrix (Fin n) (Fin n) k)ˣ) (c : (Matrix (Fin d) (Fin d) k)ˣ) :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun X := a.val * X * c.val
  invFun Y := (a⁻¹).val * Y * (c⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv Y := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private def transHomeo {k : Type} [TopologicalSpace k] {n d : ℕ} :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin d) (Fin n) k where
  toFun X := X.transpose
  invFun Y := Y.transpose
  left_inv X := Matrix.transpose_transpose X
  right_inv Y := Matrix.transpose_transpose Y
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

private theorem comp_homeo_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : Y → ℂ} (hf : f ∈ SB Y) : (fun x => f (e x)) ∈ SB X :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem UpperTheory.Gal.TP.Loc.keepsSB :
    UpperTheory.Gal.TP.Loc.KeepsSB := by
  intro k _ _ _ _ n d
  refine ⟨fun ν b g h Φ hΦ => ?_, fun Ψ hΨ => comp_homeo_mem_SB transHomeo hΨ⟩
  have hc := comp_homeo_mem_SB (mulHomeo g⁻¹ (GlobalTheory.SplitFlip.invT h)) hΦ
  have key : GlobalTheory.SplitFlip.omA ν b g h Φ =
      ((↑(ν (GlobalTheory.SplitFlip.gdet g))⁻¹ * ↑(b (GlobalTheory.SplitFlip.gdet h)) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (-↑(Fintype.card (Fin d)) / 2) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (-↑(Fintype.card (Fin n)) / 2) : ℂ) •
        fun X => Φ (mulHomeo g⁻¹ (GlobalTheory.SplitFlip.invT h) X)) := by
    funext X
    rfl
  rw [key]
  exact (SB _).smul_mem _ hc
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.modelDict :
    UpperTheory.Gal.TP.Loc.ModelDict := by
  intro k _ _ _ _ n d ν b g h Ψ X
  have hM : ((((GlobalTheory.SplitFlip.invT g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      ((GlobalTheory.SplitFlip.invT h : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)).transpose =
      ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) * X.transpose * (g : Matrix (Fin n) (Fin n) k) := by
    rw [GlobalTheory.SplitFlip.invT_inv_val, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hg := nabs_pos k (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos k (Matrix.GeneralLinearGroup.det h)
  unfold GlobalTheory.SplitFlip.omA om
  rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv]
  beta_reduce
  rw [hM]
  simp only [GlobalTheory.SplitFlip.apow, GlobalTheory.SplitFlip.gdet, Fintype.card_fin]
  rw [Complex.ofReal_cpow hg.le, Complex.ofReal_cpow hh.le]
  simp only [map_inv, inv_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hb : ((b (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.separates :
    UpperTheory.Gal.TP.Loc.Separates := by
  intro k _ _ _ _ n V _ _ ρ hρ v hv
  exact GlobalTheory.ContraRefl.exists_smooth_form_ne hρ (GlobalTheory.ThetaLiftGL.compactOpen_basis k n) hv
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.srcGood :
    UpperTheory.Gal.TP.Loc.SrcGood := by
  intro k _ _ _ _ n c V _ _ σ hc hu hs hirr hun
  have hcont : Continuous (GlobalTheory.SplitFlip.invT : GL (Fin n) k →* GL (Fin n) k) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun h : GL (Fin n) k => ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_coe_inv.matrix_transpose
    · show Continuous fun h : GL (Fin n) k => (h : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_val.matrix_transpose
  refine ⟨?_, ?_, ?_⟩
  · exact isSmooth_twist (isSmooth_comp hs _ hcont) hc.detChar
  · exact GlobalTheory.TypeTwo.EndTwist.isIrreducible_twist
      (GlobalTheory.InvTransposeEnds.isIrreducible_comp hirr _ fun h => ⟨GlobalTheory.SplitFlip.invT h, GlobalTheory.SplitFlip.invT_invT h⟩) _
  · obtain ⟨B, h1, h2, h3⟩ := hun
    refine ⟨B, h1, h2, fun g v w => ?_⟩
    rw [src_apply, src_apply, LinearMap.map_smul B, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have hn := hu (Matrix.GeneralLinearGroup.det g)
    rw [show ((c (Matrix.GeneralLinearGroup.det g) : ℂ) * (starRingEnd ℂ) (c (Matrix.GeneralLinearGroup.det g) : ℂ)) = 1 by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num, one_mul]
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.contraIrr :
    UpperTheory.Gal.TP.Loc.ContraIrr := by
  intro k _ _ _ _ n V _ _ ρ hs hi
  have hadm := (GlobalTheory.Laid.bzfin_holds k).1 (Fin n) V ρ hs hi
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k n
  exact ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm hi, ⟨GlobalTheory.ContraRefl.evEquiv hG hadm⟩⟩
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc

theorem UpperTheory.Gal.TP.Loc.contraUnit :
    UpperTheory.Gal.TP.Loc.ContraIrr → UpperTheory.Gal.TP.Loc.ContraUnit := by
  intro hci k _ _ _ _ n V _ _ ρ hsm hirr hu
  obtain ⟨B, hherm, hpos, hinv⟩ := hu
  have hnd : ∀ w : V, (∀ v : V, B v w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hpos w hne
    rw [hw w] at h1
    simp at h1
  obtain ⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    generalize (⊥ : Subrepresentation ρ) = a
    generalize (⊤ : Subrepresentation ρ) = b
    obtain ⟨A, hA⟩ := a
    obtain ⟨A', hA'⟩ := b
    congr 1
    ext x
    rw [hne x]
    simp only [Submodule.zero_mem]
  have hcirr : (contra ρ).IsIrreducible := (hci k n V ρ hsm hirr).1
  have hbij := GlobalTheory.HermDualSelf.sesqMap_bijective ρ hsm B hinv hnd ⟨w0, hw0⟩ hcirr
  have hcomm := GlobalTheory.HermDualSelf.sesqMap_comm ρ hsm B hinv
  set S := GlobalTheory.HermDualSelf.sesqMap ρ hsm B hinv with hS
  let e := LinearEquiv.ofBijective S hbij
  let T : ↥(GlobalTheory.PRep.smoothPart ρ.dual) →ₗ⋆[ℂ] V := e.symm.toLinearMap
  have hST : ∀ f, S (T f) = f := fun f => e.apply_symm_apply f
  have hTS : ∀ w, T (S w) = w := fun w => e.symm_apply_apply w
  have hTg : ∀ g f, T (contra ρ g f) = ρ g (T f) := by
    intro g f
    rw [← hST f, ← hcomm, hTS, hTS]
  refine ⟨⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => B (T f') (T f))
    ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, ⟨e, fun g x => hcomm g x⟩⟩
  · intro f₁ f₂ f'
    simp [map_add]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f₁ f₂
    simp [map_add]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm (T f') (T f)
  · intro f hf
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hpos _ (fun h => hf (by rw [← hST f, h, map_zero]))
  · intro g f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [hTg, hTg]
    exact hinv g _ _
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.satContra :
    UpperTheory.Gal.TP.Loc.ContraUnit → UpperTheory.Gal.TP.Loc.SatContra := by
  intro hCU K _ _ w n V _ _ ρ hs hi hu B hB
  obtain ⟨-, C, hC⟩ := hCU (w.adicCompletion K) n V ρ hs hi hu
  obtain ⟨b, -, hp, hinv⟩ := hu
  refine UpperTheory.V.Af.Gk.satConj K n w V (smoothPart ρ.dual) ρ (contra ρ) b.flip C ?_ ?_ hC B hB
  · intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 : b x x = 0 := hx
    rw [h2] at h1
    simp at h1
  · intro g x y
    exact hinv g y x
end

section
noncomputable section

namespace UpperTheory.Gal.TP.Loc

theorem satInvT : SatInvT := by
  intro K _ _ w n V _ _ ρ B h
  refine UpperTheory.V.InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun g x => ?_) h
  have hg : GlobalTheory.SplitFlip.invT g = GlobalTheory.CuspRep.invT n _ g := Units.ext rfl
  change ρ (GlobalTheory.SplitFlip.invT g) x = ρ (GlobalTheory.CuspRep.invT n _ g) x
  rw [hg]

end UpperTheory.Gal.TP.Loc

end
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem range_map_eq {α : Type} (t : ℕ) (F : ℕ → α) :
    (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => F (i : ℕ)) = (Finset.range t).val.map F := by
  have h : (Finset.range t).val = (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => (i : ℕ)) := by
    have h' : Finset.range t = (Finset.univ : Finset (Fin t)).map Fin.valEmbedding := by
      ext i
      simp only [Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
      exact ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩
    rw [h', Finset.map_val]
    rfl
  rw [h, Multiset.map_map]
  rfl

theorem UpperTheory.Gal.TP.Loc.satDet :
    UpperTheory.Gal.TP.Loc.SatDet := by
  intro K _ _ w t c hc ϖ hϖ
  have hv : valuation (w.adicCompletion K) (ϖ : w.adicCompletion K) = uniformizer (w.adicCompletion K) :=
    GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ
  have hord : Formalism.UG.ordV K w (ϖ : w.adicCompletion K) = 1 := by
    rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v (ϖ : w.adicCompletion K) = _ from hϖ]
    rfl
  have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K w t _ _ _ (hasSatake_detRep hc hv)
  have hm : GlobalTheory.LFun.seg w (c ϖ) t = (Finset.univ : Finset (Fin t)).val.map
      (fun i : Fin t => c ϖ * absPow (w.adicCompletion K) (((i : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ) := by
    rw [GlobalTheory.LFun.seg, ← range_map_eq]
    refine Multiset.map_congr rfl fun i _ => ?_
    congr 1
    ext
    rw [GlobalTheory.SatInd.val_absPow_completion, hord]
    simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Formalism.UG.qV]
    congr 1
    push_cast
    ring
  rw [hm]
  exact h
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem range_val_map_rev (t : ℕ) :
    (Finset.range t).val.map (fun i : ℕ => t - 1 - i) = (Finset.range t).val := by
  have hinj : ∀ i ∈ (Finset.range t).val, ∀ j ∈ (Finset.range t).val, t - 1 - i = t - 1 - j → i = j := by
    intro i hi j hj h
    simp only [Finset.mem_val, Finset.mem_range] at hi hj
    omega
  rw [Multiset.Nodup.ext (Multiset.Nodup.map_on hinj (Finset.range t).nodup) (Finset.range t).nodup]
  intro y
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hy
    exact ⟨t - 1 - y, by omega, by omega⟩

private theorem npowU_neg {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) :
    GlobalTheory.LFun.npowU w (-z) = (GlobalTheory.LFun.npowU w z)⁻¹ := by
  ext
  rw [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.coe_npowU]
  unfold GlobalTheory.LFun.npow
  exact Complex.cpow_neg _ _

theorem UpperTheory.Gal.TP.Loc.segInv :
    UpperTheory.Gal.TP.Loc.SegInv := by
  intro K _ _ w x t
  unfold GlobalTheory.LFun.seg
  rw [Multiset.map_map]
  conv_rhs => rw [← range_val_map_rev t, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  simp only [Finset.mem_val, Finset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv, ← npowU_neg]
  congr 2
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ t)]
  push_cast
  ring
end

section
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.compUnit :
    UpperTheory.Gal.TP.Loc.CompUnit := by
  intro E _ _ _ n U hU w hw τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.DefU.Petersson.exists_invariant_pos_form E n
  obtain ⟨hirr, f, h0, hf, h2⟩ := hτ
  have key : ∀ g, ∃ x : GlobalTheory.UnitaryBC.UA E n, ∀ v, f (τ.ρ g v) = GlobalTheory.UnitaryBC.RU E n x (f v) := fun g =>
    ⟨(e.symm g).1, fun v => by
      have h3 := h2 (e.symm g) v
      have hy : ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype) (e.symm g) = g := by
        have := he (e.symm g)
        rw [e.apply_symm_apply] at this
        exact this.symm
      rw [hy] at h3
      exact h3⟩
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    have hst : ∀ g, ∀ v ∈ LinearMap.ker f, τ.ρ g v ∈ LinearMap.ker f := fun g v hv => by
      obtain ⟨x, hx⟩ := key g
      rw [LinearMap.mem_ker, hx, LinearMap.mem_ker.1 hv, map_zero]
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) hst with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  let f' : τ.V →ₗ[ℂ] GlobalTheory.DefU.autU E n := f.codRestrict _ (fun v => hU.aut _ (hf v))
  have hf' : ∀ v, f' v = 0 → v = 0 := fun v h =>
    hinj ((congrArg Subtype.val h).trans (map_zero f).symm)
  have heq : ∀ g, ∃ x, ∀ v, f' (τ.ρ g v) = GlobalTheory.DefU.autRep E n x (f' v) := fun g => by
    obtain ⟨x, hx⟩ := key g
    exact ⟨x, fun v => Subtype.ext (hx v)⟩
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B (f' u) (f' v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp), ?_, ?_, ?_⟩
  · intro v u
    simpa using (hh (f' u) (f' v)).symm
  · intro v hv
    have hne : B (f' v) (f' v) ≠ 0 := fun h => hv (hf' v (hd _ h))
    have him : (B (f' v) (f' v)).im = 0 := by
      have := congrArg Complex.im (hh (f' v) (f' v))
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    have hre : (B (f' v) (f' v)).re ≠ 0 := fun h => hne (Complex.ext h him)
    exact lt_of_le_of_ne (hp _) (Ne.symm (by simpa using hre))
  · intro g v u
    obtain ⟨x, hx⟩ := heq g
    simp only [LinearMap.mk₂'ₛₗ_apply, hx]
    exact hi x _ _
end

section
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem map_surj {k k' : Type} [Field k] [Field k'] (c : k →+* k') (hs : Function.Surjective c) (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) c) := by
  intro g
  let e : k ≃+* k' := RingEquiv.ofBijective c ⟨c.injective, hs⟩
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin n) (e.symm : k' →+* k) g, ?_⟩
  apply Units.ext
  ext i j
  have : c (e.symm ((g : Matrix (Fin n) (Fin n) k') i j)) = (g : Matrix (Fin n) (Fin n) k') i j :=
    e.apply_symm_apply _
  simpa using this

private theorem map_cont {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Field k']
    [TopologicalSpace k'] [IsTopologicalRing k'] (c : k →+* k') (hc : Continuous c) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) c) := by
  have h : Continuous (RingHom.mapMatrix (m := Fin n) c : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k') :=
    Continuous.matrix_map continuous_id hc
  exact Continuous.units_map (RingHom.mapMatrix (m := Fin n) c : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k').toMonoidHom h

private theorem irr_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem UpperTheory.Gal.TP.Loc.pullGood :
    UpperTheory.Gal.TP.Loc.PullGood := by
  intro k k' _ _ _ _ _ _ c hc hs n V _ _ ρ
  refine ⟨fun h => isSmooth_comp h _ (map_cont c hc n), fun h => irr_comp ρ _ (map_surj c hs n) h, ?_⟩
  rintro ⟨B, h1, h2, h3⟩
  exact ⟨B, h1, h2, fun g v w => h3 _ v w⟩
end

section
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.liftSatU :
    UpperTheory.Gal.TP.Loc.PairSat → UpperTheory.Gal.TP.Loc.CompUnit → UpperTheory.Gal.TP.Loc.LiftSatU := by
  intro hPS hCU E _ _ _ n d hnd Bs χX χW mX mW lam U U' hU hL w hw hX hW B hB
  obtain ⟨v, hvw⟩ : ∃ v, w.under (𝓞 (maximalRealSubfield E)) = v := ⟨_, rfl⟩
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
    obtain ⟨u, hne, hu⟩ := id hw
    subst hvw
    exact ⟨w, u, hne.symm, rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
  obtain ⟨t, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.GalOfCusp.isCMExt_real E) hv hvw
  obtain ⟨τ, hτ, hs⟩ := hB
  obtain ⟨⟨τ', hτ'⟩, -⟩ := GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E d U' hL.aut _ hw
  exact ⟨τ', hτ', hPS E n d hnd v t χX χW τ τ' (hL.loc v t τ τ' hτ hτ')
    (hCU E n U hU _ hw τ hτ) hX hW B hs⟩
end

section
namespace UpperTheory.Gal.TP.Loc

theorem liftIso_holds : LiftIso :=
  liftIso_of (pairOfLift leftSmooth keepsSB modelDict separates) srcGood contraIrr (contraUnit contraIrr)

theorem liftSat_holds : LiftSat :=
  liftSat_of liftIso_holds srcGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr)) satTwist satInvT satDet
    satProd segInv

theorem pairSat_holds : PairSat :=
  pairSat liftSat_holds pullGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr))

theorem liftSatU_holds : LiftSatU := liftSatU pairSat_holds compUnit

end UpperTheory.Gal.TP.Loc
end
