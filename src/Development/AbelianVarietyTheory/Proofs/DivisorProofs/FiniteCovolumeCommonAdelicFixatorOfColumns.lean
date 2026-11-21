import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCoreUnitaryGroupEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrame

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixFrames_equiv_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  obtain ⟨e, econt, eprop, erat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  have hJ₀ := GlobalTheory.UAut.det_isUnit hF.herm₀
  set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0
  have p0Z : p0 * adMat F Z = 1 := by
    rw [hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z := fun g => by
    rw [Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]
  have inj : Function.Injective e := fun g h hgh => by
    apply matHom_injective _ σ J₀
    apply Units.ext
    rw [hrec g, hrec h, hgh]
  have DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 =
      adMat F (cT (σ : E →+* E) D * J) := by
    intro x hx
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact (fixG σ J D).inv_mem hx
    have := GlobalTheory.UAut.form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x := by
    intro x hx
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := (Subgroup.mem_inf.1 hx).1
    have hxD : (matHom _ σ J x).1 * adMat F D = adMat F D := (Subgroup.mem_inf.1 hx).2
    obtain ⟨g₀, b, h1, h2, -, -⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1
    have hb : b = 0 := by
      rw [h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C := (eprop g₀).1
    have aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D := (eprop g₀).2.1
    refine ⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩
    · rw [aC, hxC]
    · rw [(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]
    · rw [aD, hxD]
  let f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D) :=
    e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)
  have fbij : Function.Bijective f :=
    ⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>
      let ⟨g, hg⟩ := surj x.1 x.2; ⟨g, Subtype.ext hg⟩⟩
  let me := MulEquiv.ofBijective f fbij
  have hme : ∀ x, e (me.symm x) = x.1 := fun x => congrArg Subtype.val (me.apply_symm_apply x)
  have cM : Continuous (matHom (AF F) σ J) := (isEmbedding_matHom (AF F) σ J).continuous
  have contInv : Continuous me.symm := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    rw [(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]
    constructor
    · have : (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) =
          fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]; rw [hrec, hme]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
    · have : (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) =
          fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]
        rw [← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
  refine ⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩
  intro g
  change g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J
  refine ⟨erat g, fun hg => ?_⟩
  obtain ⟨g₀, b, -, -, h3, h4⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF (e g) (eprop g).1
  have : g₀ = g := matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))
  exact this ▸ h4 hg

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  atlas_forward_decl GlobalTheory.SphEis.fixFrames_equiv_core
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem covolume_ne_top_of_continuousMulEquiv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ e Γ Λ _ hmem hfin π 𝓜 hπ h𝓜
  let E : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  set μ : Measure G := π.map E.symm with hμdef
  have hμ : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map π e.symm
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving E μ π := by
    refine ⟨E.measurable, ?_⟩
    rw [hμdef, Measure.map_map E.measurable E.symm.measurable]
    simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
    exact Measure.AbsolutelyContinuous.rfl
  let φ : Λ → Γ := fun l => ⟨e.symm l, (hmem _).2 (by simpa using l.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have := congrArg (fun x : Γ => e (x : G)) hab
      simpa [φ] using this
    · intro g
      refine ⟨⟨e g, (hmem g).1 g.2⟩, ?_⟩
      apply Subtype.ext; simp [φ]
  have hsemi : ∀ l : Λ, Function.Semiconj E (φ l • ·) (l • ·) := by
    intro l x
    show e ((e.symm l : G) * x) = (l : H) * e x
    simp [map_mul]
  have hF := h𝓜.preimage_of_equiv hqmp hφ hsemi
  have hlt := hfin μ hμ _ hF
  have : μ (E ⁻¹' 𝓜) = π 𝓜 := by
    rw [hμdef, MeasurableEquiv.map_apply]
    congr 1
    ext x; simp
  rw [this] at hlt
  exact hlt.ne

end GlobalTheory.SphEis
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_ne_top_of_continuousMulEquiv_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  first | exact @GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv | exact GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv | (intros; apply GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv <;> assumption)
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem isClosed_fixG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k : ℕ} (C : Matrix (Fin n) (Fin k) E) :
    IsClosed ((fixG σ J C : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  exact isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const

theorem finCovol_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF π DM hπ hDM
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup F E σ n J j m C D Z J₀ hF
  have hcl : IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) :=
    (isClosed_fixG σ J C).inter (isClosed_fixG σ J D)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := hcl.locallyCompactSpace
  haveI : Countable (ratPts σ J₀) := inferInstance
  exact GlobalTheory.T.covolume_ne_top_of_continuousMulEquiv_subgroup (GAd σ J₀) _ e (ratPts σ J₀) _ (fun g => by rw [he g]; rfl)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E σ hF.cm m J₀ hF.herm₀ μ hμ 𝓕 h𝓕) π DM hπ hDM

end GlobalTheory.SphEis
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  atlas_forward_decl GlobalTheory.SphEis.finCovol_fixG
end
