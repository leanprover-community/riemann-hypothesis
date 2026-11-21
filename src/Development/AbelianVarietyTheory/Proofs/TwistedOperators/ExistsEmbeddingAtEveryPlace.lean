import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness

section
section
open ValuativeRel

noncomputable section
namespace GlobalTheory.SvNAnyChar

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  let ψ1 : AddChar k ℂ := ψ0.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψ1 : ∀ t, ψ1 t = ψ0 (c * t) := fun t => rfl
  have hψ1c : Continuous ψ1 := by
    have e : (ψ1 : k → ℂ) = fun t => ψ0 (c * t) := funext hψ1
    rw [e]; exact hψ.comp (continuous_const.mul continuous_id)
  have hcond : ∀ x : k, (∀ y ∈ 𝒪[k], ψ1 (x * y) = 1) ↔ x ∈ 𝒪[k] := fun x => by
    simp only [hψ1]; exact hc x
  let S : (κ → k) × (κ → k) →+ (κ → k) × (κ → k) :=
    AddMonoidHom.prodMap (AddMonoidHom.id _) (DistribMulAction.toAddMonoidHom _ c⁻¹)
  have hS : ∀ w, S w = (w.1, c⁻¹ • w.2) := fun w => rfl
  let mc : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k := DistribMulAction.toAddMonoidHom _ c
  let wT' := S.comp wT
  let wM' := (S.comp wM).comp mc
  have hT' : ∀ Y, wT' Y = ((wT Y).1, c⁻¹ • (wT Y).2) := fun Y => rfl
  have hM' : ∀ z, wM' z = ((wM (c • z)).1, c⁻¹ • (wM (c • z)).2) := fun z => rfl
  have hschr : ∀ w (φ : (κ → k) → ℂ), GlobalTheory.WeilM.schr ψ0 w φ = GlobalTheory.WeilM.schr ψ1 (S w) φ := by
    intro w φ; funext x
    simp only [GlobalTheory.WeilM.schr, hS, hψ1, dotProduct_smul, smul_eq_mul]
    congr 2
    field_simp
  obtain ⟨ι, hbij, htr, hmul⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians ψ1 hψ1c hcond wT' wM'
    (fun Y Y' => by
      have e := hT Y Y'
      simp only [hT', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, mul_zero])
    (fun z z' => by
      have e := hM (c • z) (c • z')
      simp only [hM', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, mul_zero])
    (fun Y z => by
      have e := hTM Y (c • z)
      simp only [hT', hM', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp)
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (w.1, c • w.2)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      show S (wT Y) + S (wM (c • c⁻¹ • z)) = w
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, ← map_add, h, hS]
      simp [smul_smul, inv_mul_cancel₀ hc0])
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · rw [hschr]; exact htr Y φ hφ
  · have e : S (wM z) = wM' (c⁻¹ • z) := by
      show S (wM z) = S (wM (c • c⁻¹ • z))
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [hschr, e, hmul _ φ hφ]
    funext Y'
    congr 1
    rw [hψ1]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.SvNAnyChar
end
end

open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_decomposition_weil : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  atlas_forward_decl GlobalTheory.SvNAnyChar.main
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ShapeUVAny

open GlobalTheory.ShapeUV

theorem shapeV_any : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v t ι hι g hg
  have hcm : IsCMExt F E σ := hTr.base.cm
  have hstd := hTr.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  have hAE := (GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    simp [mat]

  have hex : ∀ φ : (Fin a × Fin (a + a') → Fv F v) → ℂ, ∃ φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
      φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om (g, 1)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)
    · obtain ⟨φ₁, h, -⟩ := hAE.1 g hg 1 h1W φ hφ
      exact ⟨φ₁, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose A hA using hex
  have huniq : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → φ₁ = A φ := fun φ hφ φ₁ hφ₁ h =>
    (hAE.1 g hg 1 h1W φ hφ).unique ⟨hφ₁, h⟩ (hA φ hφ)
  have hASB : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), A φ ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
    fun φ hφ => (hA φ hφ).1
  have restA : ∀ φ r, φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (A φ) r :=
    fun φ r hφ hr => ⟨hr.1, by rw [← (hA φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩

  have hvac := hTr.geo.hM.vac v
  have hlin : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      A (c • φ + φ') = c • A φ + A φ' := by
    intro φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
      Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hA _ hsum).2 r r0, et, map_add, map_smul, (hA φ hφ).2 r r1, (hA φ' hφ').2 r r2, et]

  have hact : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E),
      actAB (cA σ) (g, (1 : UA σ G.W.J)) γ = mat g * γ := by
    intro γ
    simp [actAB, mat]
  have atMul : ∀ (M : Matrix (Fin a) (Fin a) (AE F E)) (γ : Matrix (Fin a) (Fin (a + a')) (AE F E)),
      At (evFin F v) γ → At (evFin F v) (M * γ) := by
    intro M γ hγ u hu
    rw [← Matrix.mul_smul, hγ u hu, Matrix.mul_zero]
  have hcov : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (mat g * γ)) (A φ) := by
    intro γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo G.M.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M B.ψ hstd γ _ hr.2⟩
    rw [← (hA _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hA φ hφ).2 r hr, hact,
      GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v _ (atMul _ γ hγ) (A φ) r (restA φ r hφ hr)]

  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  simp only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have hsb : ∀ (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
      φ ∈ SB (Fin a × Fin (a + a') → Fv F v) → schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (Fin a × Fin (a + a') → Fv F v) :=
    fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v w φ hφ
  have hT : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) Y = ι φ (Y + γ.map (piW t)) :=
    fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ) Y
  have hM : ∀ γ : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 →
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x →
        x.map (piW (t.comp σ)) = 0 →
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ) (x.map (piW t)) =
          B.ψ (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x γ) * ι φ (x.map (piW t)) :=
    fun γ hγ h0 φ hφ x hx hx0 =>
      hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v γ hγ φ) x hx hx0

  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁

  set A' := G.V.J.map (t.comp σ) with hA'def
  set B' := G.W.J.map (t.comp σ) with hB'def
  have hsymp : ∀ x u : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (-(∑ k, ∑ l, (-(A' * x.map (piW t) * B'ᵀ)) k l * u.map (piW (t.comp σ)) k l)) := by
    intro x u hx hx0 hu1
    have hu1' : u.map (piW ((t.comp σ).comp σ)) = 0 := by rw [comp_conj_conj hcm]; exact hu1
    have e := GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm (t.comp σ) G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx0 hu1'
    rw [comp_conj_conj hcm] at e
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v (t.comp σ) _ (at_neg_hTens _ _ x u hx), comp_conj_conj hcm]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, e]
    rfl

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : G.V.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hV.sig w)
    have e : (G.V.J.map (B.emb w).1).det = (B.emb w).1 G.V.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : G.W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hTr.geo.hW.sig w)
    have e : (G.W.J.map (B.emb w).1).det = (B.emb w).1 G.W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA' : IsUnit A'ᵀ.det := by
    have e : A'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.V.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdV (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB' : IsUnit B'.det := by
    have e : B'.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) G.W.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h =>
      hdW (((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  let Lm : (Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hchar : ∀ (l : Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)),
      -(∑ k, ∑ j, (-(A' * Y * B'ᵀ)) k j * ((A'ᵀ)⁻¹ * Lm l * B'⁻¹) k j) = l Y := by
    intro l Y
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rw [sum_conj_mul, linForm_sum l Y]
    have e : A'ᵀ * ((A'ᵀ)⁻¹ * Lm l * B'⁻¹) * B' = Lm l := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hB', Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA']
    rw [e]
    rfl

  set gt := (mat g).map (piW t) with hgt
  set gti := (mat g⁻¹).map (piW t) with hgti
  have hmatinv : mat g⁻¹ * mat g = 1 := by simp [mat]
  have hmatinv' : mat g * mat g⁻¹ = 1 := by simp [mat]
  have hgg : gti * gt = 1 := by
    rw [hgti, hgt, ← Matrix.map_mul, hmatinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgg' : gt * gti = 1 := by
    rw [hgti, hgt, ← Matrix.map_mul, hmatinv', Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv : gt⁻¹ = gti := Matrix.inv_eq_left_inv hgg
  have hU : (mat g)ᵀ * incM F G.V.J * (mat g).map (cA σ) = incM F G.V.J := g.2

  have h2lin : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (c • x + y)) (gt * Y)) = c • (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A x) (gt * Y)) + (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A y) (gt * Y)) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have h2tr : ∀ C : Matrix (Fin a) (Fin (a + a')) (Fv F v), ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x) = (fun Y => ι x (Y + C)) ∧
      (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U C 0)) x)) (gt * Y)) =
        fun Y => ι (A x) (gt * (Y + C)) := by
    intro C x hx
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      rw [hT _ (hUat C 0) (hU1 C 0) x hx Y, hU0]
    · funext Y
      have h0 : (mat g * U C 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      rw [hcov _ (hUat C 0) x hx, hT _ (atMul _ _ (hUat C 0)) h0 (A x) (hASB x hx), Matrix.map_mul, hU0,
        Matrix.mul_add]
  have h2mu : ∀ (l : Matrix (Fin a) (Fin (a + a')) (Fv F v) →ₗ[Fv F v] Fv F v), ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x ∈
        SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x) =
        (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (U 0 ((A'ᵀ)⁻¹ * Lm l * B'⁻¹))) x))
          (gt * Y)) = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (A x) (gt * Y) := by
    intro l x hx
    set P := (A'ᵀ)⁻¹ * Lm l * B'⁻¹ with hP
    refine ⟨hsb _ x hx, ?_, ?_⟩
    · funext Y
      have hm := hM (U 0 P) (hUat 0 P) (hU0 0 P) x hx (U Y 0) (hUat Y 0) (hU1 Y 0)
      rw [hU0] at hm
      rw [hm, hsymp _ _ (hUat Y 0) (hU1 Y 0) (hU0 0 P), hU0, hU1, hchar]
    · funext Y
      have h0 : (mat g * U 0 P).map (piW t) = 0 := by
        rw [Matrix.map_mul, hU0, Matrix.mul_zero]
      have hm := hM _ (atMul _ _ (hUat 0 P)) h0 (A x) (hASB x hx) (U (gt * Y) 0) (hUat (gt * Y) 0) (hU1 (gt * Y) 0)
      rw [hU0] at hm
      have hx' : symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (U (gt * Y) 0) (mat g * U 0 P) =
          symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (mat g⁻¹ * U (gt * Y) 0) (U 0 P) := by
        conv_lhs => rw [show U (gt * Y) 0 = mat g * (mat g⁻¹ * U (gt * Y) 0) by
          rw [← Matrix.mul_assoc, hmatinv', Matrix.one_mul]]
        exact symp_mul_mul _ _ _ _ _ hU _ _
      have h1 : (mat g⁻¹ * U (gt * Y) 0).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul, hU1, Matrix.mul_zero]
      have h2 : (mat g⁻¹ * U (gt * Y) 0).map (piW t) = Y := by
        rw [Matrix.map_mul, hU0, ← hgti, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
      rw [hcov _ (hUat 0 P) x hx, hm, hx', hsymp _ _ (atMul _ _ (hUat (gt * Y) 0)) h1 (hU0 0 P), h2, hU1, hchar]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun φ (Y : Matrix (Fin a) (Fin (a + a')) (Fv F v)) => ι (A φ) (gt * Y)) hL.bij h2lin _ _ h2tr h2mu
  refine ⟨c, fun φ hφ φ₁ hφ₁ hact1 Y => ?_⟩
  rw [huniq φ hφ φ₁ hφ₁ hact1, hinv]
  have e := congrFun (hc φ hφ) (gti * Y)
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [← Matrix.mul_assoc, hgg', Matrix.one_mul] at e
  exact e

end GlobalTheory.ShapeUVAny
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) := by
  atlas_forward_decl GlobalTheory.ShapeUVAny.shapeV_any
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.UnitWShapeSplit

open GlobalTheory.UnitWShape

theorem shape_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v t ι hι h hh
  obtain ⟨S, hSB, huniq, hlin, hcomm⟩ := exists_localOp hP F E σ B a a' G X om om' hTr v h hh
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := heisW B G X om om' hTr v t h S hSB hcomm
  obtain ⟨hT0, hM0, hST, hSM⟩ := hA ι hι
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  set ht := (mat h).map (piW t) with hht
  have hdet : IsUnit ht.det := by
    have h1 : IsUnit (mat h).det := (Units.isUnit h.1).map Matrix.detMonoidHom
    have h2 := h1.map (piW t)
    rw [RingHom.map_det] at h2
    exact h2
  have hsb := fun (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v w φ hφ
  have hL2 : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (c • x + y)) (Y * htᵀ)) = c • (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) (Y * htᵀ)) + fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S y) (Y * htᵀ) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have hT2 : ∀ C, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x) = (fun Y => ι x (Y + C)) ∧
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x)) (Y * htᵀ)) = fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) ((Y + C) * htᵀ) := by
    intro C x hx
    refine ⟨hsb _ x hx, hT0 C x hx, ?_⟩
    funext Y
    simp only [hST C x hx, Matrix.add_mul]
  have hM2 : ∀ l, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x) = (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x)) (Y * htᵀ)) =
        fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * htᵀ) := by
    intro l x hx
    refine ⟨hsb _ x hx, hM0 l x hx, ?_⟩
    funext Y
    simp only [hSM l x hx, Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one,
      Matrix.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun x Y => ι (S x) (Y * htᵀ)) hbij hL2
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C)) (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l)) hT2 hM2
  refine ⟨c, fun φ hφ φ₁ _ hAct Y => ?_⟩
  rw [huniq φ hφ φ₁ hAct]
  have e := congrFun (hc φ hφ) (Y * (ht⁻¹)ᵀ)
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one,
    Matrix.mul_one] at e

end GlobalTheory.UnitWShapeSplit
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) := by
  atlas_forward_decl GlobalTheory.UnitWShapeSplit.shape_split
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.SchurCharV in

theorem GlobalTheory.SchurCharV.exists_char_of_schur_any : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι H
  have hcm : IsCMExt F E σ := hT.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hT.geo.hV.cartan w)
  set L := GlobalTheory.SplitUnitLift.liftU hcm t G.V.J 1 herm hJ with hLdef
  have hLmem : ∀ x, L x ∈ UAt σ G.V (evFin F v) := fun x => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ x
  have hLt : ∀ x, (mat (L x)).map (piW t) = x.val := fun x => GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ x
  have hEx := (GlobalTheory.T.theta_action_exists hP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]
  have hpres : ∀ p : UA σ G.V.J × UA σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ
  have hvac := hT.geo.hM.vac v
  set φv := G.M.vac v
  have hφv : φv ∈ SB (Fin a × Fin (a + a') → Fv F v) := hvac.1
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hιv : ι φv ≠ 0 := fun h0 => hvac.2.1 (hbij.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  choose c hc using fun x : GL (Fin a) (Fv F v) => H (L x) (hLmem x)
  have hrel : ∀ x, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (L x, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c x * ι φ ((x⁻¹ : GL (Fin a) (Fv F v)).val * Y) := by
    intro x φ hφ φ₁ hφ₁ hA Y
    rw [hc x φ hφ φ₁ hφ₁ hA Y, hLt x, Matrix.coe_units_inv]
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx (L y) (hLmem y) 1 h1mem φv hφv
    obtain ⟨φ₃, ⟨hφ₃, hA₃⟩, -⟩ := hEx (L x) (hLmem x) 1 h1mem φ₂ hφ₂
    have hA : Acts (evFin F v) (om (L (x * y), 1)) φv φ₃ := by
      have e : ((L (x * y), 1) : UA σ G.V.J × UA σ G.W.J) = (L x, 1) * (L y, 1) := by
        rw [Prod.mk_mul_mk, map_mul, one_mul]
      rw [e, map_mul]
      exact GlobalTheory.InertAvgDual.acts_comp v _ _ (hpres _) hA₂ hA₃
    have e1 := hrel (x * y) φv hφv φ₃ hφ₃ hA ((x * y).val * Y₀)
    have e2 := hrel x φ₂ hφ₂ φ₃ hφ₃ hA₃ ((x * y).val * Y₀)
    have e3 := hrel y φv hφv φ₂ hφ₂ hA₂ (y.val * Y₀)
    have k1 : ((x * y)⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have k2 : (x⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = y.val * Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_left]
    have k3 : (y⁻¹ : GL (Fin a) (Fv F v)).val * (y.val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    rw [e2, e3] at e1
    exact mul_right_cancel₀ hY₀ (e1.symm.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have hA : Acts (evFin F v) (om (L 1, 1)) φv φv := by
      rw [map_one, show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      exact GlobalTheory.InertAvgDual.acts_one v φv
    have e := hrel 1 φv hφv φv hφv hA Y₀
    rw [inv_one, Units.val_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e.symm
  let cH : GL (Fin a) (Fv F v) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) cH.toHomUnits
  have hcχ : ∀ x, c x = (χ (Matrix.GeneralLinearGroup.det x) : ℂ) := fun x => by rw [← hχ x]; rfl
  let A : (Fv F v)ˣ →* ℂˣ :=
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (((a + a' : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  refine ⟨(χ * A)⁻¹, ?_⟩
  intro g hg
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  refine ⟨g', rfl, ?_⟩
  intro φ hφ φ₁ hφ₁ hA
  have hgL : g = L g' := eq_liftU_of_UAt hcm t G.V herm hJ g hg
  rw [hgL] at hA
  funext Y
  rw [hrel g' φ hφ φ₁ hφ₁ hA Y, hcχ g']
  have hpow : ∀ d : (Fv F v)ˣ, GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) *
      GlobalTheory.SplitFlip.apow d (-((a + a' : ℕ) : ℂ) / 2) = 1 := fun d => by
    rw [← GlobalTheory.SplitFlip.apow_add, show ((a + a' : ℕ) : ℂ) / 2 + -((a + a' : ℕ) : ℂ) / 2 = 0 by ring,
      GlobalTheory.SplitFlip.apow_zero]
  simp only [GlobalTheory.SplitFlip.omA, MonoidHom.inv_apply, inv_inv, MonoidHom.mul_apply, Units.val_mul, map_one,
    MonoidHom.one_apply, Units.val_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]
  have hAv : ∀ d, ((A d : ℂˣ) : ℂ) = GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) := fun d => rfl
  rw [hAv]
  linear_combination (-(χ (GlobalTheory.SplitFlip.gdet g') : ℂ) * ι φ ((g'⁻¹ : GL (Fin a) (Fv F v)).val * Y)) * hpow (GlobalTheory.SplitFlip.gdet g')
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_invariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  atlas_forward_decl GlobalTheory.SchurCharV.exists_char_of_schur_any
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LatVac
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.MixedForm

theorem char_eq_local_any : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι ν₀ hν
  have h := hT.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  haveI : Nonempty (Fin a) := ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) hT.geo.lt⟩⟩
  obtain ⟨φ, hφ, hφ0⟩ : ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ 0 ≠ 0 := by
    obtain ⟨Λ, -, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v a (a + a')
    obtain ⟨Y₀, hY⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (by rw [show f = 0 from funext hc, map_zero])
    have hf' : (fun Y => f (Y + Y₀)) ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
      ⟨hf.1.comp_continuous (continuous_add_const Y₀), hf.2.comp_homeomorph (Homeomorph.addRight Y₀)⟩
    obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn hf'
    exact ⟨φ, hφ, by rw [e]; simpa using hY⟩
  refine ⟨t.comp σ, Or.inr (MonoidHom.ext fun x => ?_)⟩
  obtain ⟨g', rfl⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a) x
  set g := GlobalTheory.LeviAtPlace.leviHom h t G.V.J hJ hT.geo.hV.herm g' with hgdef
  have hg : g ∈ UAt σ G.V (evFin F v) := GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  have g1 : (mat g).map (piW t) = g'.1 := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  have g2 : (((Matrix.GeneralLinearGroup.det g')⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_snd,
      GlobalTheory.LeviAtPlace.conjComp, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      Matrix.nonsing_inv_mul _ hJ, Matrix.det_one, one_mul, Matrix.det_transpose, ← map_inv]
    rfl
  obtain ⟨g'', e, hact⟩ := hν g hg
  obtain rfl : g' = g'' := Units.ext (g1.symm.trans e)
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero h G.M B.ψ hT.base.std _ _ om hT.weil t ι hι g hg _ g2 φ φ₁ hφ hA
  rw [hact φ hφ φ₁ hφ₁ hA, chrW_div, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g')⁻¹ ^ (((a + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g') (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _), Fintype.card_fin]
    push_cast
    rfl
  rw [k2] at k1
  simp only [GlobalTheory.SplitFlip.omA, map_one, GlobalTheory.SplitFlip.apow_one, MonoidHom.one_apply, Units.val_one, mul_one,
    Matrix.mul_zero, Matrix.zero_mul] at k1
  have k3 := mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero _ _) (mul_right_cancel₀ hφ0 k1)
  rw [MonoidHom.inv_apply, ← inv_eq_iff_eq_inv]
  exact Units.ext k3

end GlobalTheory.MixedForm

end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weil_linear_model_measure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  atlas_forward_decl GlobalTheory.MixedForm.char_eq_local_any
end

section
open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

section Lin

open GlobalTheory.LinWAt
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny

theorem exists_isLinW (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      G.M.IsLinW B.ψ t 1 1 ι := by
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hTr.base.std v
  have hcoT : ∀ Y, coW G t (uT Y) = 0 := fun Y => coW_eq_zero G t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.lagrangian_decomposition_weil (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1
    ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj G.M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact coW_eq_zero G t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx (hM z).1,
      coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

end Lin

section Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem surjV (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)) :
    ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  have hcm := hTr.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hTr.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hTr.geo.hV.cartan w)
  exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ g', GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ g'⟩

theorem isUnit_det_map_J_of_isTriple (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) : IsUnit (G.W.J.map t).det := by
  have w := Classical.arbitrary (InfinitePlace F)
  exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.W.J t (B.emb w).1 Complex.I Complex.I_ne_zero (G.W.θ w)
    (hTr.geo.hW.cartan w)

theorem surjW (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)) :
    ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  have hcm := hTr.base.cm
  have herm : ∀ i j, σ (G.W.J j i) = algebraMap F E (-1) * G.W.J i j := fun i j => by
    rw [map_neg, map_one, neg_one_mul]; exact hTr.geo.hW.skew i j
  exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.W (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h',
    GlobalTheory.SplitUnitLift.liftU_piW hcm t G.W.J (-1) herm (isUnit_det_map_J_of_isTriple hTr v t) h'⟩

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.UnitaryInjAtPlace in

theorem injW (hTr : IsTriple B G X om om') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ := isUnit_det_map_J_of_isTriple hTr v t
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end Points

end GlobalTheory.SplitTransport

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

section Scalars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem omA_left (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    GlobalTheory.SplitFlip.omA ν 1 g 1 Φ = (((ν (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) •
      GlobalTheory.SplitWeil.om 1 (1 : GL (Fin m) k) g Φ := by
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, GlobalTheory.SplitFlip.apow, Pi.smul_apply, smul_eq_mul, map_one,
    Units.val_one, one_mul, mul_one, inv_one, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_one, Fintype.card_fin,
    MonoidHom.one_apply, GlobalTheory.SplitFlip.gdet]
  simp [GlobalTheory.SplitWeil.nabs]
  rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  push_cast
  ring

theorem om_right (β : kˣ →* ℂˣ) (g : GL (Fin m) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    ∃ s : ℂ, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) Φ = s • GlobalTheory.SplitFlip.omA 1 β 1 (GlobalTheory.SplitFlip.invT g) Φ := by
  have h1 : (β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)
  refine ⟨((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) /
    ((β (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.invT g)) (-(Fintype.card (Fin n) : ℂ) / 2)), ?_⟩
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitFlip.invT_invT, inv_one,
    Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]
  simp [GlobalTheory.SplitWeil.nabs] at h1 h2 ⊢
  field_simp
  rw [mul_div_assoc, div_self (GlobalTheory.SplitFlip.apow_ne_zero _ _), mul_one]

theorem omA_right (β : kˣ →* ℂˣ) (h' : GL (Fin m) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    ∃ s : ℂ, GlobalTheory.SplitFlip.omA 1 β 1 h' Φ = s • GlobalTheory.SplitWeil.om 1 (GlobalTheory.SplitFlip.invT h') (1 : GL (Fin n) k) Φ := by
  have h2 : ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^
      ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have := GlobalTheory.SplitWeil.Model.nabs_pos (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  refine ⟨(β (GlobalTheory.SplitFlip.gdet h') : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h') (-(Fintype.card (Fin n) : ℂ) / 2) /
    ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h')) ^
      ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ), ?_⟩
  funext X
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, inv_one,
    Units.val_one, map_one, MonoidHom.one_apply, one_mul, Matrix.one_mul, GlobalTheory.SplitFlip.apow_one, mul_one]
  simp only [ne_eq] at h2
  simp [GlobalTheory.SplitWeil.nabs] at h2 ⊢
  have h3 : ((↑((MeasureTheory.distribHaarChar k) (Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h'))) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  field_simp

end Scalars

end GlobalTheory.SplitTransport

namespace GlobalTheory.SplitTransport

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

theorem transport : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      ∃ (χ : GL (Fin a) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →* ℂˣ)
        (ι : ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ]
          (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        IsOpen {g | χ g = 1} ∧
        Set.BijOn ι (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : Set _)
          (GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) : Set _) ∧
        ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
          N ≤ GlobalTheory.WeilM.SB _ → (GlobalTheory.Published.ThetaSub om v N ↔ GlobalTheory.ThetaGLSub.IsSub χ (N.map ι)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v ⟨t⟩
  obtain ⟨ι, hι⟩ := exists_isLinW hP hTr v t
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.local_weil_linear_model_invariant hP F E σ B a a' G X om om' hTr v t ι hι (GlobalTheory.T.local_weil_linear_model_action hP F E σ B a a' G X om om' hTr v t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.local_weil_linear_model_measure hP F E σ B a a' G X om om' hTr v t ι hι ν₀ hV
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  obtain ⟨β₀, hW⟩ := GlobalTheory.LocalUnitSubgroupClosure.core hTr v t ι (hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _)) (surjW hTr v t) (injW hTr v t)
    (GlobalTheory.T.local_weil_linear_model_unitary hP F E σ B a a' G X om om' hTr v t ι hι)

  have hνc : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hTr.chars.heckeα.1.div' hTr.chars.heckeβ.1
  have hs0 : GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t') :=
    GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (GlobalTheory.ChrWSmooth.continuous_chrW hνc t')
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs0
    · rw [h]; exact hs0.inv
  set χ : GL (Fin a) (Fv F v) →* ℂˣ := GlobalTheory.SmGL.detChar (Fin a) ν₀ with hχ
  have hχv : ∀ g, χ g = ν₀ (Matrix.GeneralLinearGroup.det g) := fun g => rfl
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hinj := hbij.injOn
  have hmaps : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
    fun φ hφ => hbij.mapsTo hφ
  refine ⟨χ, ι, ?_, hbij, ?_⟩
  · have := hνs.detChar (n := Fin a)
    exact this
  intro N hN

  have hAugSB : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v) := by
    rw [augAt, Submodule.span_le]
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hVsc : ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
      ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
        ι (φ₁ - φ) = (((χ g')⁻¹ : ℂˣ) : ℂ) • (GlobalTheory.SplitWeil.om 1 1 g' (ι φ) - (χ g' : ℂ) • ι φ) := by
    intro g hg φ hφ φ₁ hφ₁ hA
    obtain ⟨g', hg', hact⟩ := hV g hg
    refine ⟨g', hg', ?_⟩
    rw [map_sub, hact φ hφ φ₁ hφ₁ hA, omA_left, smul_sub, smul_smul, hχv]
    simp
  have hmapAug : (augAt om v).map ι = GlobalTheory.ThetaGLSub.aug (a + a') χ := by
    apply le_antisymm
    · rw [augAt, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, rfl⟩
      obtain ⟨g', -, e⟩ := hVsc g hg φ hφ φ₁ hφ₁ hA
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g', ι φ, hmaps φ hφ, rfl⟩)
    · rw [GlobalTheory.ThetaGLSub.aug, Submodule.span_le]
      rintro _ ⟨h, Φ, hΦ, rfl⟩
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΦ
      obtain ⟨g, hg, hgt⟩ := surjV hTr v t h
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) φ hφ
      obtain ⟨g', hg', e⟩ := hVsc g hg φ hφ φ₁ hφ₁ hA
      have : g' = h := Units.ext (hg'.symm.trans hgt)
      subst this
      refine ⟨(χ g' : ℂ) • (φ₁ - φ), Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩), ?_⟩
      rw [map_smul, e, smul_smul]
      simp
  have hiffAug : augAt om v ≤ N ↔ GlobalTheory.ThetaGLSub.aug (a + a') χ ≤ N.map ι := by
    rw [← hmapAug]
    refine ⟨Submodule.map_mono, fun h x hx => ?_⟩
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 (h (Submodule.mem_map_of_mem hx))
    rwa [hinj (hN hy) (hAugSB hx) e] at hy

  have hiffW : (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) ↔
      ∀ g : GL (Fin (a + a')) (Fv F v), ∀ Φ ∈ N.map ι, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin a) (Fv F v)) Φ ∈ N.map ι := by
    constructor
    · intro H g Φ hΦ
      obtain ⟨φ, hφN, rfl⟩ := Submodule.mem_map.1 hΦ
      obtain ⟨h, hh, hht⟩ := surjW hTr v t (GlobalTheory.SplitFlip.invT g)
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (GlobalTheory.LocalUnitSubgroupClosure.one_mem_UAt _ _) h hh φ (hN hφN)
      obtain ⟨h', hh', hact⟩ := hW h hh
      have : h' = GlobalTheory.SplitFlip.invT g := Units.ext (hh'.symm.trans hht)
      subst this
      obtain ⟨s, hs⟩ := om_right β₀ g (ι φ)
      rw [hs, ← hact φ (hN hφN) φ₁ hφ₁ hA, ← map_smul]
      exact Submodule.mem_map_of_mem (N.smul_mem s (H h hh φ hφN φ₁ hφ₁ hA))
    · intro H h hh φ hφN φ₁ hφ₁ hA
      obtain ⟨h', -, hact⟩ := hW h hh
      obtain ⟨s, hs⟩ := omA_right β₀ h' (ι φ)
      have h1 : ι φ₁ ∈ N.map ι := by
        rw [hact φ (hN hφN) φ₁ hφ₁ hA, hs]
        exact Submodule.smul_mem _ _ (H _ _ (Submodule.mem_map_of_mem hφN))
      obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h1
      rwa [hinj (hN hy) hφ₁ e] at hy
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨hiffAug.1 h1, ?_, hiffW.1 h3⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmaps φ (hN hφ)
  · rintro ⟨h1, -, h3⟩
    exact ⟨hiffAug.2 h1, hN, hiffW.2 h3⟩

end GlobalTheory.SplitTransport
end
end
