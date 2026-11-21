import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariantStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalDeterminedByUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_functional_good_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι := by
  first | exact @GlobalTheory.LinWAt.exists_isLinW | exact GlobalTheory.LinWAt.exists_isLinW | (intros; apply GlobalTheory.LinWAt.exists_isLinW <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_good_place_equivariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) := by
  first | exact @GlobalTheory.ShapeUV.shapeV | exact GlobalTheory.ShapeUV.shapeV | (intros; apply GlobalTheory.ShapeUV.shapeV <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_unramified_vector : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) := by
  first | exact @GlobalTheory.UnitWShape.shape | exact GlobalTheory.UnitWShape.shape | (intros; apply GlobalTheory.UnitWShape.shape <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_spherical_value : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  first | exact @GlobalTheory.SchurCharV.exists_char_of_schur | exact GlobalTheory.SchurCharV.exists_char_of_schur | (intros; apply GlobalTheory.SchurCharV.exists_char_of_schur <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_local_uniqueness : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  first | exact @GlobalTheory.MixedForm.char_eq_local | exact GlobalTheory.MixedForm.char_eq_local | (intros; apply GlobalTheory.MixedForm.char_eq_local <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  first | exact @GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary | exact GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary | (intros; apply GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_weil_functional_translation_equivariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) →
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  first | exact @GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero | exact GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero | (intros; apply GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SurjAtPlaceV

open GlobalTheory.LeviAtPlace

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t g'
  have h := hTr.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨leviHom h t G.V.J hJ hTr.geo.hV.herm g', lift_sub_one_at v _, ?_⟩
  rw [leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]

end GlobalTheory.SurjAtPlaceV
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_group_surjects_general_linear : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  first | exact @GlobalTheory.SurjAtPlaceV.surj_at_place | exact GlobalTheory.SurjAtPlaceV.surj_at_place | (intros; apply GlobalTheory.SurjAtPlaceV.surj_at_place <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinA

theorem omA_h_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β g 1 Φ = GlobalTheory.SplitFlip.omA ν 1 g 1 Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem omA_g_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (h : GL D k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β 1 h Φ = GlobalTheory.SplitFlip.omA 1 β 1 h Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem one_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem isSmoothChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsSmoothChar χ) : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := by
  have e : (χ⁻¹).ker = χ.ker := by ext x; simp [MonoidHom.mem_ker]
  unfold GlobalTheory.SmGL.IsSmoothChar at h ⊢
  rw [e]; exact h

theorem isUnitaryChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsUnitaryChar χ) : GlobalTheory.SmGL.IsUnitaryChar χ⁻¹ := by
  intro x
  have := h x
  simp [this]

theorem localOps_eq_omA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t, ι, hι⟩ := GlobalTheory.T.exists_linear_functional_good_place hP F E σ B a a' G X om om' hTr v hv
  obtain ⟨ν₀, hV⟩ := GlobalTheory.T.linear_weil_functional_spherical_value hP F E σ B a a' G X om om' hTr v hv t ι hι (GlobalTheory.T.linear_weil_functional_good_place_equivariant hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨t', ht'⟩ := GlobalTheory.T.linear_weil_functional_local_uniqueness hP F E σ B a a' G X om om' hTr v hv t ι hι ν₀ hV
  obtain ⟨β₀, hW⟩ := GlobalTheory.T.linear_weil_functional_translation_equivariant hP F E σ B a a' G X om om' hTr v hv t ι hι (GlobalTheory.T.linear_weil_functional_unramified_vector hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨hβs, hβu⟩ := GlobalTheory.T.linear_weil_functional_determined_by_unramified hP F E σ B a a' G X om om' hTr v hv t ι hι β₀ hW
  obtain ⟨hs, hu⟩ := GlobalTheory.T.local_character_smooth_unitary hP F E σ B a a' G X om om' hTr v hv t'
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs
    · rw [h]; exact isSmoothChar_inv _ hs
  have hνu : GlobalTheory.SmGL.IsUnitaryChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hu
    · rw [h]; exact isUnitaryChar_inv _ hu
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  refine ⟨ν₀, β₀, ι, ⟨t', ht'⟩, hνs, hνu, hβs, hβu, hι.bij, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', -, hg'⟩ := hV g hg
    exact ⟨g', fun φ hφ φ₁ hφ₁ hA => by rw [hg' φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro g'
    obtain ⟨g, hg, hgt⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear hP F E σ B a a' G X om om' hTr v hv t g'
    refine ⟨g, hg, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (one_mem_UAt σ G.W _) φ hφ
    obtain ⟨g'', hg'', hgeq⟩ := hV g hg
    have : g'' = g' := Units.ext (hg''.symm.trans hgt)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hgeq φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro h'
    obtain ⟨h, hh, hht⟩ := GlobalTheory.T.local_unitary_group_surjects_general_linear_right hP F E σ B a a' G X om om' hTr v hv t h'
    refine ⟨h, hh, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (one_mem_UAt σ G.V _) h hh φ hφ
    obtain ⟨h'', hh'', hheq⟩ := hW h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hheq φ hφ φ₁ hφ₁ hA, omA_g_one ν₀ β₀]⟩

end GlobalTheory.WeilLinA
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_characters_linear_bar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  first | exact @GlobalTheory.WeilLinA.localOps_eq_omA | exact GlobalTheory.WeilLinA.localOps_eq_omA | (intros; apply GlobalTheory.WeilLinA.localOps_eq_omA <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvV

theorem irrV : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hnr N hAN hNS hstab
  obtain ⟨ν₀, β₀, ι, ⟨t, ht⟩, s1, u1, s2, u2, hbij, hg1, hg2, hh⟩ := GlobalTheory.T.exists_local_characters_linear_bar hP F E σ B a a' G X om om' hT v hv
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hν : ν₀ (unifAt v) ≠ 1 := by
    have h1 := hnr t 1 one_ne_zero
    rw [zpow_one] at h1
    rcases ht with rfl | rfl
    · exact h1
    · intro h; apply h1; simpa using congrArg (·⁻¹) h
  set augL : Submodule ℂ (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) := Submodule.span ℂ
    {z | ∃ (g : GL (Fin a) (Fv F v)) (Ψ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ - Ψ} with haugL
  have augS : augAt om v ≤ SB _ :=
    Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ
  have c1 : augAt om v ≤ augL.comap ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    obtain ⟨g', hg'⟩ := hg1 g hg
    show ι (φ₁ - φ) ∈ augL
    rw [map_sub, hg' φ hφ φ₁ hφ₁ hA]
    exact Submodule.subset_span ⟨g', ι φ, hbij.mapsTo hφ, rfl⟩
  have c2 : augL ≤ (augAt om v).map ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
    obtain ⟨g, hg, hgg⟩ := hg2 g'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hgg φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, ?_⟩
    rw [map_sub, he]
  have c3 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ augL → φ ∈ augAt om v := by
    intro φ hφ h
    obtain ⟨ψ, hψ, he⟩ := c2 h
    rwa [← hbij.injOn (augS hψ) hφ he]
  set N' := N.map ι with hN'
  have n1 : augL ≤ N' := c2.trans (Submodule.map_mono hAN)
  have n2 : N' ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rintro _ ⟨φ, hφ, rfl⟩; exact hbij.mapsTo (hNS hφ)
  have n3 : ∀ (h' : GL (Fin (a + a')) (Fv F v)), ∀ Ψ ∈ N', GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' Ψ ∈ N' := by
    rintro h' _ ⟨φ, hφ, rfl⟩
    obtain ⟨h, hhW, hk⟩ := hh h'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hk φ (hNS hφ)
    exact ⟨φ₁, hstab h hhW φ hφ φ₁ hφ₁ hA, he⟩
  have hle : a ≤ a + a' := Nat.le_add_right a a'
  rcases GlobalTheory.T.span_character_translates_coinvariant hP.bernsteinUnitaryProductIrreducible (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 s2 u2 N' n1 n2 n3 with hA | hB
  · left
    refine le_antisymm (fun φ hφ => ?_) hAN
    have hφS := hNS hφ
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : Ψ₀ ∈ N' := by
      have := N'.sub_mem (Submodule.mem_map_of_mem hφ) (n1 hd)
      rwa [sub_sub_cancel] at this
    have h1 := hA Ψ₀ h0 hr
    refine c3 φ hφS ?_
    have := augL.add_mem hd h1
    rwa [sub_add_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφS => ?_)
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : ι φ ∈ N' := by
      have := N'.add_mem (n1 hd) (hB Ψ₀ hΨ₀ hr)
      rwa [sub_add_cancel] at this
    obtain ⟨n, hn, he⟩ := h0
    rwa [← hbij.injOn (hNS hn) hφS he]

end GlobalTheory.IrrCoinvV
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_submodule_first_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  atlas_forward_decl GlobalTheory.IrrCoinvV.irrV
end
