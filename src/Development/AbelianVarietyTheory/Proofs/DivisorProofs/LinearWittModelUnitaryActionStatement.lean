import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_unitary_conjugate : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ W.J → ℂ, ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val) := by
  first | exact @GlobalTheory.LinWShape.shape_right | exact GlobalTheory.LinWShape.shape_right | (intros; apply GlobalTheory.LinWShape.shape_right <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ShapeUXBas

theorem shapeX : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι
  suffices H : ∀ g ∈ UAt σ X (evFin F v), ∃ κ₀ : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ₀ • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) by
    classical
    refine ⟨fun g => if hg : g ∈ UAt σ X (evFin F v) then (H g hg).choose else 0, fun g hg => ?_⟩
    simp only [dif_pos hg]
    exact (H g hg).choose_spec
  intro g hg
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have hAE := (GlobalTheory.T.theta_action_exists hPr) F E σ B n d X W M χX χW om r s r' s' hP v
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := by
    intro u _
    simp [mat]

  have hex : ∀ φ : (Fin n × Fin d → Fv F v) → ℂ, ∃ φ₁ : (Fin n × Fin d → Fv F v) → ℂ,
      φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧
        Acts (evFin F v) (om (g, 1)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin n × Fin d → Fv F v)
    · obtain ⟨φ₁, h, -⟩ := hAE.1 g hg 1 h1W φ hφ
      exact ⟨φ₁, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose A hA using hex
  have huniq : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → φ₁ = A φ := fun φ hφ φ₁ hφ₁ h =>
    (hAE.1 g hg 1 h1W φ hφ).unique ⟨hφ₁, h⟩ (hA φ hφ)
  have hASB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), A φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun φ hφ => (hA φ hφ).1
  have restA : ∀ φ r, φ ∈ SB (Fin n × Fin d → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (A φ) r :=
    fun φ r hφ hr => ⟨hr.1, by rw [← (hA φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩

  have hvac := hP.good.vac v
  have hlin : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ,
      A (c • φ + φ') = c • A φ + A φ' := by
    intro φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (M.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin n × Fin d → Fv F v) :=
      Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin n × Fin d → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hA _ hsum).2 r r0, et, map_add, map_smul, (hA φ hφ).2 r r1, (hA φ' hφ').2 r r2, et]

  have hact : ∀ γ : Matrix (Fin n) (Fin d) (AE F E),
      actAB (cA σ) (g, (1 : UA σ W.J)) γ = mat g * γ := by
    intro γ
    simp [actAB, mat]
  have atMul : ∀ (P : Matrix (Fin n) (Fin n) (AE F E)) (γ : Matrix (Fin n) (Fin d) (AE F E)),
      At (evFin F v) γ → At (evFin F v) (P * γ) := by
    intro P γ hγ u hu
    rw [← Matrix.mul_smul, hγ u hu, Matrix.mul_zero]
  have hcov : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (mat g * γ)) (A φ) := by
    intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo M.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz M B.ψ hstd γ _ hr.2⟩
    rw [← (hA _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hA φ hφ).2 r hr, hact,
      GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (atMul _ γ hγ) (A φ) r (restA φ r hφ hr)]

  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  have hsb : ∀ (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have hT : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ Y,
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) Y =
          ι φ (Y + (b⁻¹).val * γ.map (piW t) * ((c⁻¹).val)ᵀ) :=
    fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ) Y
  have hM : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW (t.comp σ)) = 0 →
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) ((b⁻¹).val * x.map (piW t) * ((c⁻¹).val)ᵀ) =
          B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x γ) * ι φ ((b⁻¹).val * x.map (piW t) * ((c⁻¹).val)ᵀ) :=
    fun γ hγ h0 φ hφ x hx hx0 =>
      hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hγ φ) x hx hx0

  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁

  set A' := X.J.map (t.comp σ) with hA'def
  set B' := W.J.map (t.comp σ) with hB'def
  have hsymp : ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ l, (-(A' * x.map (piW t) * B'ᵀ)) k l * u.map (piW (t.comp σ)) k l)) := by
    intro x u hx hx0 hu1
    have hu1' : u.map (piW ((t.comp σ).comp σ)) = 0 := by rw [comp_conj_conj hcm]; exact hu1
    have e := GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) X.J W.J hP.herm.herm hP.skew.skew x u hx0 hu1'
    rw [comp_conj_conj hcm] at e
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (GlobalTheory.ShapeUV.at_neg_hTens _ _ x u hx), comp_conj_conj hcm]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, e]
    rfl

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w)
    have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w)
    have e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA' : IsUnit A'ᵀ.det := by
    have e : A'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB' : IsUnit B'.det := by
    have e : B'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) W.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))

  set A'' := A' * b.val with hA''def
  set B'' := B' * c.val with hB''def
  have hA'' : IsUnit A''ᵀ.det := by
    rw [hA''def, Matrix.transpose_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (Matrix.isUnits_det_units b).mul hA'
  have hB'' : IsUnit B''.det := by
    rw [hB''def, Matrix.det_mul]
    exact hB'.mul (Matrix.isUnits_det_units c)
  have hkey : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), A' * (b.val * Y * (c.val)ᵀ) * B'ᵀ = A'' * Y * B''ᵀ := by
    intro Y
    simp only [hA''def, hB''def, Matrix.transpose_mul, Matrix.mul_assoc]
  have hc1 : (c.val)ᵀ * ((c⁻¹).val)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hb1 : (b⁻¹).val * b.val = 1 := Units.inv_mul b
  have hcoY : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (b.val * Y * (c.val)ᵀ) * ((c⁻¹).val)ᵀ = Y := by
    intro Y
    simp only [Matrix.mul_assoc, hc1, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hb1, Matrix.one_mul]
  let Lm : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hchar : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)),
      -(∑ k, ∑ j, (-(A'' * Y * B''ᵀ)) k j * ((A''ᵀ)⁻¹ * Lm l * B''⁻¹) k j) = l Y := by
    intro l Y
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [GlobalTheory.ShapeUV.sum_conj_mul, GlobalTheory.ShapeUV.linForm_sum l Y]
    have e : A''ᵀ * ((A''ᵀ)⁻¹ * Lm l * B''⁻¹) * B'' = Lm l := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hB'', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA'']
    rw [e]
    rfl

  set gt := (mat g).map (piW t) with hgt
  set gti := (mat g⁻¹).map (piW t) with hgti
  have hmatinv : mat g⁻¹ * mat g = 1 := by simp [mat]
  have hmatinv' : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgg : gti * gt = 1 := by
    rw [hgti, hgt, ← Matrix.map_mul, hmatinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have hg'val : (locMat t b g).val = (b⁻¹).val * gt * b.val := locMat_val t b g
  have hgg' : (locMat t b g).val * ((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbb : b.val * (b⁻¹).val = 1 := Units.mul_inv b
  have hco2 : ∀ C : Matrix (Fin n) (Fin d) (Fv F v),
      (b⁻¹).val * (gt * (b.val * C * (c.val)ᵀ)) * ((c⁻¹).val)ᵀ = (locMat t b g).val * C := by
    intro C
    rw [hg'val]
    simp only [Matrix.mul_assoc, hc1, Matrix.mul_one]
  have hgiY : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v),
      gti * (b.val * ((locMat t b g).val * Y) * (c.val)ᵀ) = b.val * Y * (c.val)ᵀ := by
    intro Y
    rw [hg'val]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val (b⁻¹).val, hbb, Matrix.one_mul, ← Matrix.mul_assoc gti gt, hgg, Matrix.one_mul]

  have h2lin : ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ,
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A (c • x + y)) ((locMat t b g).val * Y)) =
        c • (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A x) ((locMat t b g).val * Y)) +
          (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A y) ((locMat t b g).val * Y)) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have h2tr : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), ∀ x ∈ SB (Fin n × Fin d → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x ∈ SB (Fin n × Fin d → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x) = (fun Y => ι x (Y + C)) ∧
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) =>
          ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U (b.val * C * (c.val)ᵀ) 0)) x))
            ((locMat t b g).val * Y)) =
        fun Y => ι (A x) ((locMat t b g).val * (Y + C)) := by
    intro C x hx
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      rw [hT _ (hUat _ 0) (hU1 _ 0) x hx Y, hU0, hcoY]
    · funext Y
      have h0 : (mat g * U (b.val * C * (c.val)ᵀ) 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      rw [hcov _ (hUat _ 0) x hx, hT _ (atMul _ _ (hUat _ 0)) h0 (A x) (hASB x hx), Matrix.map_mul, hU0,
        ← hgt, hco2, Matrix.mul_add]
  have h2mu : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v), ∀ x ∈ SB (Fin n × Fin d → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x ∈
        SB (Fin n × Fin d → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x) =
        (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun (Y : Matrix (Fin n) (Fin d) (Fv F v)) =>
          ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (U 0 ((A''ᵀ)⁻¹ * Lm l * B''⁻¹))) x))
            ((locMat t b g).val * Y)) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (A x) ((locMat t b g).val * Y) := by
    intro l x hx
    set P := (A''ᵀ)⁻¹ * Lm l * B''⁻¹ with hP
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      have hm := hM (U 0 P) (hUat 0 P) (hU0 0 P) x hx (U (b.val * Y * (c.val)ᵀ) 0) (hUat _ 0) (hU1 _ 0)
      rw [hU0, hcoY] at hm
      rw [hm, hsymp _ _ (hUat _ 0) (hU1 _ 0) (hU0 0 P), hU0, hU1, hkey, hchar]
    · funext Y
      have h0 : (mat g * U 0 P).map (piW t) = 0 := by
        rw [Matrix.map_mul, hU0, Matrix.mul_zero]
      set Z := b.val * ((locMat t b g).val * Y) * (c.val)ᵀ with hZ
      have hm := hM _ (atMul _ _ (hUat 0 P)) h0 (A x) (hASB x hx) (U Z 0) (hUat Z 0) (hU1 Z 0)
      rw [hU0, hZ, hcoY] at hm
      have hx' : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (U Z 0) (mat g * U 0 P) =
          symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g⁻¹ * U Z 0) (U 0 P) := by
        conv_lhs => rw [show U Z 0 = mat g * (mat g⁻¹ * U Z 0) by
          rw [← Matrix.mul_assoc, hmatinv', Matrix.one_mul]]
        exact GlobalTheory.ShapeUV.symp_mul_mul _ _ _ _ _ hU _ _
      have h1 : (mat g⁻¹ * U Z 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      have h2 : (mat g⁻¹ * U Z 0).map (piW t) = b.val * Y * (c.val)ᵀ := by
        rw [Matrix.map_mul, hU0, ← hgti, hZ, hgiY]
      rw [hcov _ (hUat 0 P) x hx, hm, hx', hsymp _ _ (atMul _ _ (hUat Z 0)) h1 (hU0 0 P), h2, hU1, hkey, hchar]
  obtain ⟨κ₀, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun φ (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A φ) ((locMat t b g).val * Y)) hL.bij h2lin _ _ h2tr h2mu
  refine ⟨κ₀, fun φ hφ φ₁ hφ₁ hact1 => ?_⟩
  rw [huniq φ hφ φ₁ hφ₁ hact1]
  funext Y
  have e := congrFun (hc φ hφ) (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)
  simp only [Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← Matrix.mul_assoc, hgg', Matrix.one_mul] at e
  exact e

end GlobalTheory.ShapeUXBas
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_conjugate_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) := by
  atlas_forward_decl GlobalTheory.ShapeUXBas.shapeX
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open GlobalTheory.LatVac GlobalTheory.MixedForm
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitScalX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem lin_zero_basis (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (χX χW : Chr F E)
    (om : Rep σ X W) (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t b c ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ι φ₁ 0 = (chrW χW (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ι φ 0 := by
  obtain ⟨Λ, hΛ, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨φ₂, hφ₂, rfl⟩ := hι.bij.surjOn hf
  refine form_scalar h M ψ χX χW om hW t (LinearMap.proj 0 ∘ₗ ι) (conjForm (Λ ∘ₗ ι)) (fun w hw φ hφ => ?_)
    (fun w hw φ hφ => ?_) (star φ₂) (star_mem_SB hφ₂) ?_ g hg y hy φ φ₁ hφ hA
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.mult u hu ((e2 t).trans hw) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ) 0 (fun a _ => smul_zero a) (Matrix.map_zero _ (map_zero _))
    rw [e1] at this
    simpa [symp, hTens] using this
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.trans u hu ((e2 _).trans hw) _ (star_mem_SB hφ) _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ _ (star_mem_SB hφ))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu _)
    rw [e1] at this
    change star (Λ (ι _)) = star (Λ (ι _))
    rw [star_schr (psiAt ψ v) (fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _), funext this,
      hΛ _ (hι.bij.mapsTo (star_mem_SB hφ))]
  · change star (Λ (ι (star (star φ₂)))) ≠ 0
    rwa [star_star, star_ne_zero]

theorem chrW_comp_conj (h : IsCMExt F E σ) {K : Subgroup (AF F)ˣ} {χ : Chr F E} {m : ℕ} (hχ : ResEtaPow K χ m)
    (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW χ (t.comp σ) x = (chrW χ t x)⁻¹ := by
  obtain ⟨ε, e1, e2, e3, e4, e5, e6, e7⟩ := exists_idem h t
  have e8 : piW (t.comp σ) ε = 0 := by simpa [e7] using congrArg (piW (t.comp σ)) e2
  have key : ∀ a a' : Fv F v, a * a' = 1 → (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a - 1))) *
      (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a' - 1))) = 1 := fun a a' haa => by
    have e : liftV v (a - 1) + liftV v (a' - 1) + liftV v (a - 1) * liftV v (a' - 1) = 0 := by
      rw [liftV_mul, evFin_liftV, ← map_add, ← map_add, show a - 1 + (a' - 1) + (a - 1) * (a' - 1) = 0 by
        linear_combination haa, map_zero]
    have e' := congrArg (algebraMap (AF F) (AE F E)) e
    rw [map_add, map_add, map_mul, map_zero] at e'
    linear_combination ε * e' + algebraMap (AF F) (AE F E) (liftV v (a - 1)) *
      algebraMap (AF F) (AE F E) (liftV v (a' - 1)) * e1
  have hat : ∀ a : Fv F v, At (evFin F v) (1 + ε * algebraMap (AF F) (AE F E) (liftV v a) - 1) := fun a u hu => by
    rw [add_sub_cancel_left, ← mul_smul_comm, Algebra.smul_def, ← map_mul,
      show u * liftV v a = 0 from at_liftV v a u hu, map_zero, mul_zero]
  let z : (AE F E)ˣ := ⟨_, _, key _ _ x.mul_inv, key _ _ x.inv_mul⟩
  have hz : At (evFin F v) ((z : AE F E) - 1) := hat _
  have hzi : At (evFin F v) (((z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := hat _
  have z1 : piW t (z : AE F E) = x := by
    change piW t (1 + _) = _
    rw [map_add, map_mul, map_one, e5, piW_algebraMap, evFin_liftV]; ring
  have z2 : piW (t.comp σ) (z : AE F E) = 1 := by
    change piW _ (1 + _) = _
    rw [map_add, map_mul, map_one, e8, zero_mul, add_zero]
  obtain ⟨n1, n2⟩ := GlobalTheory.T.local_norm_unramified_factorization F E σ h v t z hz
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) z with ha
  have n1' : At (evFin F v) ((a : AF F) - 1) := n1
  have n2' : evFin F v (a : AF F) = x := by rw [← mul_one (x : Fv F v), ← z1, ← z2]; exact n2
  have h1 := hχ a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩)), Circle.coe_eq_one] at h1
  set A : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a with hA
  have hAv : (A : AE F E) = algebraMap (AF F) (AE F E) a := rfl
  have w0 : At (evFin F v) (((A * z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := fun u hu => by
    have a1 : u • ((A : AE F E) - 1) = 0 := by
      rw [hAv, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul,
        show u * ((a : AF F) - 1) = 0 from n1' u hu, map_zero]
    rw [Units.val_mul, show (A : AE F E) * (z⁻¹ : (AE F E)ˣ) - 1 =
      ((A : AE F E) - 1) * (z⁻¹ : (AE F E)ˣ) + ((z⁻¹ : (AE F E)ˣ) - 1) by ring, smul_add, ← smul_mul_assoc, a1,
      hzi u hu, zero_mul, add_zero]
  have zz : ∀ τ : E →ₐ[F] Fv F v, piW τ ((A * z⁻¹ : (AE F E)ˣ) : AE F E) * piW τ (z : AE F E) = x := fun τ => by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right, hAv, piW_algebraMap, n2']
  have w1 : piW t ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
    have := zz t
    rw [z1] at this
    exact (mul_eq_right₀ x.ne_zero).1 this
  have w2 : piW (t.comp σ) ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = x := by
    have := zz (t.comp σ)
    rwa [z2, mul_one] at this
  have c1 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v t z hz z2
  have c2 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v (t.comp σ) (A * z⁻¹) w0 (by rw [comp_conj_conj h]; exact w1)
  rw [show Units.map (piW t).toMonoidHom z = x from Units.ext z1] at c1
  rw [show Units.map (piW (t.comp σ)).toMonoidHom (A * z⁻¹) = x from Units.ext w2] at c2
  rw [c1, c2, map_mul, h1, one_mul, map_inv, map_inv]

theorem scalar_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hT v t b c ι hι κ hκ g hg
  have h := hT.base.cm
  have hJ : (X.J.map t).det ≠ 0 := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.herm.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn (indicator_intM_mem_SB (k := Fv F v) (R := Fin n) (D := Fin d))
  have hφ0 : ι φ 0 ≠ 0 := by
    rw [e, Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ intM (Fv F v) (Fin n) (Fin d) from
      fun _ _ => zero_mem _)]
    exact one_ne_zero
  set x : (Fv F v)ˣ := GlobalTheory.SplitFlip.gdet (locMat t b g) with hx
  have hx1 : (x : Fv F v) = ((mat g).map (piW t)).det := by
    change (locMat t b g).val.det = _
    rw [locMat_val, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
      one_mul]
  have hx2 : ((x⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    have hu := congrArg Matrix.det (GlobalTheory.Div.CoordOpp.unit_map σ g t)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hx1, mul_right_comm, mul_eq_right₀ hJ] at hu
    exact Units.inv_eq_of_mul_eq_one_right hu
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ M _ _ om _ _ _ _ hT v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero_basis h M B.ψ hT.base.std _ _ om hT.weil t b c ι hι g hg _ hx2 φ φ₁ hφ hA
  rw [hκ g hg φ hφ φ₁ hφ₁ hA, chrW_comp_conj h hT.resW, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) x⁻¹ ^ ((d : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow x (-(d : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _)]
    push_cast
    rfl
  rw [k2] at k1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_zero] at k1
  exact mul_right_cancel₀ hφ0 k1

end GlobalTheory.SplitScalX

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_unitary_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  atlas_forward_decl GlobalTheory.SplitScalX.scalar_left
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.KSplit.om_linW_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hp v
  have oneX : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ X.J) - 1) = 0
    simp [mat]
  have oneW : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  have hspl := hp.weil.isUSplitting
  obtain ⟨φ', ⟨hφ', hA'⟩, -⟩ := hex 1 oneX h hh φ hφ
  obtain ⟨φ'', ⟨hφ'', hA''⟩, -⟩ := hex g hg 1 oneW φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R := ⟨hR.1, by rw [← hA' R hR]; exact hspl.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  obtain ⟨κW, hW⟩ := GlobalTheory.T.linear_model_unitary_conjugate hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  obtain ⟨κX, hX⟩ := GlobalTheory.T.linear_model_compact_conjugate_exists hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  have sW := GlobalTheory.T.linear_model_compact_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κW hW h hh
  have sX := GlobalTheory.T.linear_model_unitary_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κX hX g hg
  rw [e1, hX g hg φ' hφ' φ'' hφ'' hA'', hW h hh φ hφ φ' hφ' hA', sW, sX]
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, inv_inv, Matrix.mul_assoc]
  ring
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_witt_model_unitary_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  first | exact @GlobalTheory.KSplit.om_linW_split | exact GlobalTheory.KSplit.om_linW_split | (intros; apply GlobalTheory.KSplit.om_linW_split <;> assumption)
end
