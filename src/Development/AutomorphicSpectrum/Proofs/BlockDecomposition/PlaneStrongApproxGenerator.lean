import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSpecialUnitarySupport
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import GroundTheory.GlobalFields.Adele.WeakApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryProductReflections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionsGenerateSubgroup
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousLocalLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicPlaneOpenNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneAdelicApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryQuadraticPairPerturbNearby
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneApproxPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicUnitaryGroupCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem idem_mul_eq_of_subset : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b →
    A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a := by
  intro F _ _ A₁ B₁ A₂ B₂ a b ha hb h1 h2
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, -, hb3, -⟩ := hb
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul]
    refine ainf_ext fun w => ?_
    change fstA F b w * fstA F a w = fstA F a w
    by_cases hw : w ∈ A₁
    · rw [hb1 w (h1 hw), one_mul]
    · rw [ha2 w hw, mul_zero]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ A₂
    · rw [hb3 v (h2 hv), one_mul]
    · rw [ha4 v hv, mul_zero]

end GlobalTheory.CompanionTheory.SaGen
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_idempotent_mul_absorb : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b → A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.Supp

open GlobalTheory.CompanionTheory.Sa2Prod

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem trunc_mul_trunc {c d : R} (h : c * d = 0) {A : Matrix n n R} (hA : (c + d) • (A - 1) = A - 1) :
    trunc c A * trunc d A = A := by
  have e : trunc c A * trunc d A = 1 + (c + d) • (A - 1) + (c * d) • ((A - 1) * (A - 1)) := by
    unfold trunc
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, add_smul, smul_add]
    rw [mul_comm d c]
    abel
  rw [e, h, zero_smul, add_zero, hA]
  abel

end Ring

section Idem

variable {F : Type} [Field F] [NumberField F]

theorem idem_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {a : AF F}
    (ha : IsPlacesIdem S₁ S₂ a) : a * a = a := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_mul]
    change fstA F a w * fstA F a w = fstA F a w
    by_cases h : w ∈ S₁
    · rw [ha.1 w h, one_mul]
    · rw [ha.2.1 w h, zero_mul]
  · rw [map_mul, map_mul]
    by_cases h : v ∈ S₂
    · rw [ha.2.2.1 v h, one_mul]
    · rw [ha.2.2.2 v h, zero_mul]

theorem idem_orth {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂) :
    a * b = 0 := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_mul, map_zero]
    change fstA F a w * fstA F b w = 0
    by_cases h : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ h), mul_zero]
    · rw [ha.2.1 w h, zero_mul]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases h : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ h), mul_zero]
    · rw [ha.2.2.2 v h, zero_mul]

theorem idem_eq_add [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) : δ = a + b := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_add]
    change fstA F δ w = fstA F a w + fstA F b w
    by_cases h : w ∈ A₁
    · rw [hδ.1 w (Finset.mem_union_left _ h), ha.1 w h, hb.2.1 w (Finset.disjoint_left.1 h₁ h), add_zero]
    · by_cases h' : w ∈ B₁
      · rw [hδ.1 w (Finset.mem_union_right _ h'), ha.2.1 w h, hb.1 w h', zero_add]
      · rw [hδ.2.1 w (by simp [h, h']), ha.2.1 w h, hb.2.1 w h', add_zero]
  · rw [map_add, map_add]
    by_cases h : v ∈ A₂
    · rw [hδ.2.2.1 v (Finset.mem_union_left _ h), ha.2.2.1 v h, hb.2.2.2 v (Finset.disjoint_left.1 h₂ h), add_zero]
    · by_cases h' : v ∈ B₂
      · rw [hδ.2.2.1 v (Finset.mem_union_right _ h'), ha.2.2.2 v h, hb.2.2.1 v h', zero_add]
      · rw [hδ.2.2.2 v (by simp [h, h']), ha.2.2.2 v h, hb.2.2.2 v h', add_zero]

theorem idem_empty {a : AF F} (ha : IsPlacesIdem (∅ : Finset (InfinitePlace F))
    (∅ : Finset (HeightOneSpectrum (𝓞 F))) a) : a = 0 := by
  refine adele_ext (funext fun w => ?_) (finAdele_ext fun v => ?_)
  · rw [map_zero]
    exact ha.2.1 w (Finset.notMem_empty w)
  · rw [map_zero, map_zero]
    exact ha.2.2.2 v (Finset.notMem_empty v)

end Idem

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem supp_split (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {a b : AF F}
    (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J (a + b)) :
    ∃ x ∈ SUSupp σ J a, ∃ y ∈ SUSupp σ J b, g = x * y := by
  have ha' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) a =
      algebraMap (AF F) (AF F ⊗[F] E) a := by rw [← map_mul, ha]
  have hb' : algebraMap (AF F) (AF F ⊗[F] E) b * algebraMap (AF F) (AF F ⊗[F] E) b =
      algebraMap (AF F) (AF F ⊗[F] E) b := by rw [← map_mul, hb]
  refine ⟨truncHA σ J ha' g, truncHA_mem σ J ha' hg.1, truncHA σ J hb' g, truncHA_mem σ J hb' hg.1, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  refine (trunc_mul_trunc (c := algebraMap (AF F) (AF F ⊗[F] E) a) (d := algebraMap (AF F) (AF F ⊗[F] E) b)
    (by rw [← map_mul, hab, map_zero]) ?_).symm
  ext i j
  have := hg.2 i j
  rw [map_add] at this
  rw [Matrix.smul_apply, smul_eq_mul]
  exact this

theorem supp_le_of_disjoint [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J))
    {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) (hNa : SUSupp σ J a ⊆ N) (hNb : SUSupp σ J b ⊆ N) :
    SUSupp σ J δ ⊆ N := by
  intro g hg
  rw [idem_eq_add ha hb h₁ h₂ hδ] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := supp_split σ J (idem_self ha) (idem_self hb) (idem_orth ha hb h₁ h₂) hg
  exact N.mul_mem (hNa hx) (hNb hy)

theorem supp_zero_le (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) :
    SUSupp σ J (0 : AF F) ⊆ N := by
  intro g hg
  have h : g = 1 := by
    refine Subtype.ext (Units.ext ?_)
    ext i j
    have := hg.2 i j
    rw [map_zero, zero_mul] at this
    exact (sub_eq_zero.1 this.symm)
  rw [h]
  exact N.one_mem

theorem supp_le_of_single : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J))
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F},
    IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) →
    (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N := by
  intro F E _ _ _ _ _ σ M J N T₁ T₂ δ hδ h₁ h₂
  classical
  have base : ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) →
      ∀ d : AF F, IsPlacesIdem ∅ S d → SUSupp σ J d ⊆ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ d hd
      rw [idem_empty hd]
      exact supp_zero_le σ J N
    | insert v s hv ih =>
      intro hS d hd
      obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
      obtain ⟨d', hd'⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ s
      refine supp_le_of_disjoint σ J N he hd' (Finset.disjoint_empty_left _)
        (Finset.disjoint_singleton_left.2 hv) ?_ (hS v (Finset.mem_insert_self v s) e he)
        (ih (fun u hu => hS u (Finset.mem_insert_of_mem hu)) d' hd')
      rwa [Finset.empty_union, ← Finset.insert_eq]
  have main : ∀ (S : Finset (InfinitePlace F)), (∀ w ∈ S, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) →
      ∀ d : AF F, IsPlacesIdem S T₂ d → SUSupp σ J d ⊆ N := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ d hd
      exact base T₂ h₂ d hd
    | insert w s hw ih =>
      intro hS d hd
      obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
      obtain ⟨d', hd'⟩ := StrongApprox.exists_isPlacesIdem (F := F) s T₂
      refine supp_le_of_disjoint σ J N he hd' (Finset.disjoint_singleton_left.2 hw)
        (Finset.disjoint_empty_left _) ?_ (hS w (Finset.mem_insert_self w s) e he)
        (ih (fun u hu => hS u (Finset.mem_insert_of_mem hu)) d' hd')
      rwa [Finset.empty_union, ← Finset.insert_eq]
  exact main T₁ h₁ δ hδ

end Main

end GlobalTheory.CompanionTheory.SaGen.Supp
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_support_product : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) → (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.Supp.supp_le_of_single
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.DensePair

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_of_subset {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) :
    b * a = a := by
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul]
    funext w
    change fstA F b w * fstA F a w = fstA F a w
    by_cases hw : w ∈ A₁
    · rw [hb.1 w (h₁ hw), one_mul]
    · rw [ha.2.1 w hw, mul_zero]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.1 v (h₂ hv), one_mul]
    · rw [ha.2.2.2 v hv, mul_zero]

theorem idem_mul_of_disjoint {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁)
    (h₂ : Disjoint A₂ B₂) : a * b = 0 := by
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul, map_zero]
    funext w
    change fstA F a w * fstA F b w = 0
    by_cases hw : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ hw), mul_zero]
    · rw [ha.2.1 w hw, zero_mul]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv), mul_zero]
    · rw [ha.2.2.2 v hv, zero_mul]

def sumIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) : AF F :=
  ∑ w : S₁, (placeMapInf w.1).inj 1 + ∑ v : S₂, (placeMapFin v.1).inj 1

def glue (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : (∀ v : S₂, v.1.adicCompletion F) × (∀ w : S₁, w.1.Completion)) : AF F :=
  ∑ w : S₁, (placeMapInf w.1).inj (p.2 w) + ∑ v : S₂, (placeMapFin v.1).inj (p.1 v)

theorem continuous_glue (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (glue S₁ S₂) := by
  unfold glue
  refine Continuous.add ?_ ?_
  · exact continuous_finset_sum _ fun w _ =>
      (placeMapInf w.1).cont_inj.comp ((continuous_apply w).comp continuous_snd)
  · exact continuous_finset_sum _ fun v _ =>
      (placeMapFin v.1).cont_inj.comp ((continuous_apply v).comp continuous_fst)

theorem glue_proj (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (a : AF F) :
    glue S₁ S₂ (fun v => (placeMapFin v.1).proj a, fun w => (placeMapInf w.1).proj a) = sumIdem S₁ S₂ * a := by
  simp only [glue, sumIdem, PlaceMap.inj_proj, add_mul, Finset.sum_mul]

theorem inf_proj_inf_ne {w u : InfinitePlace F} (h : w ≠ u) (y : u.Completion) :
    (placeMapInf w).proj ((placeMapInf u).inj y) = 0 :=
  singleI_ne h y

theorem inf_proj_fin (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    (placeMapInf w).proj ((placeMapFin v).inj y) = 0 := rfl

theorem fin_proj_inf (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (y : w.Completion) :
    (placeMapFin v).proj ((placeMapInf w).inj y) = 0 :=
  map_zero (evalV F v)

theorem fin_proj_fin_ne {v u : HeightOneSpectrum (𝓞 F)} (h : v ≠ u) (y : u.adicCompletion F) :
    (placeMapFin v).proj ((placeMapFin u).inj y) = 0 :=
  StrongApprox.evalV_single_ne h y

theorem isPlacesIdem_sumIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    IsPlacesIdem S₁ S₂ (sumIdem S₁ S₂) := by
  classical
  have hI : ∀ w, (placeMapInf w).proj (sumIdem S₁ S₂) =
      ∑ u : S₁, (placeMapInf w).proj ((placeMapInf u.1).inj 1) := by
    intro w
    simp only [sumIdem, map_add, map_sum, inf_proj_fin, Finset.sum_const_zero, add_zero]
  have hF : ∀ v, (placeMapFin v).proj (sumIdem S₁ S₂) =
      ∑ u : S₂, (placeMapFin v).proj ((placeMapFin u.1).inj 1) := by
    intro v
    simp only [sumIdem, map_add, map_sum, fin_proj_inf, Finset.sum_const_zero, zero_add]
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · refine (hI w).trans ?_
    rw [Finset.sum_eq_single (⟨w, hw⟩ : S₁)]
    · exact (placeMapInf w).proj_inj 1
    · intro u _ hu
      exact inf_proj_inf_ne (fun h => hu (Subtype.ext h.symm)) 1
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (hI w).trans (Finset.sum_eq_zero fun u _ => ?_)
    exact inf_proj_inf_ne (fun h : w = u.1 => hw (by rw [h]; exact u.2)) 1
  · refine (hF v).trans ?_
    rw [Finset.sum_eq_single (⟨v, hv⟩ : S₂)]
    · exact (placeMapFin v).proj_inj 1
    · intro u _ hu
      exact fin_proj_fin_ne (fun h => hu (Subtype.ext h.symm)) 1
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (hF v).trans (Finset.sum_eq_zero fun u _ => ?_)
    exact fin_proj_fin_ne (fun h : v = u.1 => hv (by rw [h]; exact u.2)) 1

section Two

variable {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂]
  [TopologicalSpace K₂]

theorem proj_idem_one (P : PlaceMap F K₁) {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {d : AF F} (hP : IsPlacesIdem A₁ A₂ (P.inj 1))
    (hd : IsPlacesIdem B₁ B₂ d) (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : P.proj d = 1 := by
  have h := congrArg P.proj (idem_mul_of_subset hP hd h₁ h₂)
  rwa [map_mul, P.proj_inj, mul_one] at h

theorem proj_inj_other (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) (h : P₁.inj 1 * P₂.inj 1 = 0) (x : K₂) :
    P₁.proj (P₂.inj x) = 0 := by
  have e : P₂.inj x = P₂.inj 1 * P₂.inj x := by
    have := P₂.inj_proj (P₂.inj x)
    rwa [P₂.proj_inj] at this
  have h0 : P₁.proj (P₂.inj 1) = 0 := by
    have := congrArg P₁.proj h
    rwa [map_mul, P₁.proj_inj, one_mul, map_zero] at this
  rw [e, map_mul, h0, zero_mul]

end Two

theorem denseRange_pair {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂]
    [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} (h₁ : IsPlacesIdem A₁ A₂ (P₁.inj 1))
    (h₂ : IsPlacesIdem B₁ B₂ (P₂.inj 1)) (d₁ : Disjoint A₁ B₁) (d₂ : Disjoint A₂ B₂) :
    DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) := by
  classical
  have hD := isPlacesIdem_sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)
  have p₁ : P₁.proj (sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)) = 1 :=
    proj_idem_one P₁ h₁ hD Finset.subset_union_left Finset.subset_union_left
  have p₂ : P₂.proj (sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)) = 1 :=
    proj_idem_one P₂ h₂ hD Finset.subset_union_right Finset.subset_union_right
  have z₁ : P₁.inj 1 * P₂.inj 1 = 0 := idem_mul_of_disjoint h₁ h₂ d₁ d₂
  have z₂ : P₂.inj 1 * P₁.inj 1 = 0 := by rw [mul_comm]; exact z₁
  let G := fun p => (P₁.proj (glue (A₁ ∪ B₁) (A₂ ∪ B₂) p), P₂.proj (glue (A₁ ∪ B₁) (A₂ ∪ B₂) p))
  have hG : Continuous G :=
    (P₁.cont_proj.comp (continuous_glue _ _)).prodMk (P₂.cont_proj.comp (continuous_glue _ _))
  have hval : ∀ a : AF F, G (fun v => (placeMapFin v.1).proj a, fun w => (placeMapInf w.1).proj a) =
      (P₁.proj a, P₂.proj a) := by
    intro a
    simp only [G, glue_proj, map_mul, p₁, p₂, one_mul]
  have hsurj : Function.Surjective G := by
    rintro ⟨x₁, x₂⟩
    refine ⟨_, (hval (P₁.inj x₁ + P₂.inj x₂)).trans ?_⟩
    rw [map_add, map_add, P₁.proj_inj, P₂.proj_inj, proj_inj_other P₁ P₂ z₁, proj_inj_other P₂ P₁ z₂, add_zero,
      zero_add]
  have hdense := hsurj.denseRange.comp (GroundTheory.Global.denseRange_algebraMap_prod_pi (A₂ ∪ B₂) (A₁ ∪ B₁)) hG
  convert hdense using 1
  funext f
  have := hval (algebraMap F (AF F) f)
  simp only [AlgHom.commutes] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SaGen.DensePair
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_diagonal_two_places : ∀ {F : Type} [Field F] [NumberField F] {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂] [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}, IsPlacesIdem A₁ A₂ (P₁.inj 1) → IsPlacesIdem B₁ B₂ (P₂.inj 1) → Disjoint A₁ B₁ → Disjoint A₂ B₂ → DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.DensePair.denseRange_pair
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_tensCoord (K : Type) [NontriviallyNormedField K] [Algebra F K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι F E) :
    ∃ ψ : (ι → K) → K ⊗[F] E, Continuous ψ ∧ Function.Surjective ψ ∧
      ∀ c : ι → F, ψ (fun i => algebraMap F K (c i)) = inclR K (∑ i, c i • b i) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (K ⊗[F] E) := IsModuleTopology.toContinuousAdd K (K ⊗[F] E)
  haveI : ContinuousSMul K (K ⊗[F] E) := IsModuleTopology.toContinuousSMul K (K ⊗[F] E)
  let e := (Algebra.TensorProduct.basis K b).equivFun
  refine ⟨e.symm, IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, e.symm.surjective, fun c => ?_⟩
  change (Algebra.TensorProduct.basis K b).equivFun.symm _ = (1 : K) ⊗ₜ[F] (∑ i, c i • b i)
  rw [Module.Basis.equivFun_symm_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]

theorem denseRange_inclR_pair [FiniteDimensional F E] {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁]
    [NontriviallyNormedField K₂] [Algebra F K₂]
    (h : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f))) :
    DenseRange (fun x : E => ((inclR K₁ x, inclR K₂ x) : (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) := by
  classical
  let b := Module.finBasis F E
  obtain ⟨ψ₁, c₁, s₁, h₁⟩ := exists_tensCoord K₁ b
  obtain ⟨ψ₂, c₂, s₂, h₂⟩ := exists_tensCoord K₂ b
  let G : (Fin (Module.finrank F E) → K₁ × K₂) → (K₁ ⊗[F] E) × (K₂ ⊗[F] E) :=
    fun w => (ψ₁ (fun i => (w i).1), ψ₂ (fun i => (w i).2))
  have hGc : Continuous G := (c₁.comp (by fun_prop)).prodMk (c₂.comp (by fun_prop))
  have hGs : Function.Surjective G := by
    rintro ⟨x, y⟩
    obtain ⟨u, rfl⟩ := s₁ x
    obtain ⟨v, rfl⟩ := s₂ y
    exact ⟨fun i => (u i, v i), rfl⟩
  have hD : DenseRange (Pi.map fun (_ : Fin (Module.finrank F E)) (f : F) =>
      (algebraMap F K₁ f, algebraMap F K₂ f)) := DenseRange.piMap fun _ => h
  refine Dense.mono ?_ (hGs.denseRange.comp hD hGc)
  rintro _ ⟨c, rfl⟩
  refine ⟨∑ i, c i • b i, ?_⟩
  exact (Prod.ext (h₁ c) (h₂ c)).symm

end Coord

theorem denseRange_ratPairs : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) := by
  intro F E _ _ _ _ _ σ _ K₁ K₂ _ _ _ _ h M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hP : DenseRange (Pi.map fun (_ : Fin M) (x : E) =>
      ((inclR K₁ x, inclR K₂ x) : (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) :=
    DenseRange.piMap fun _ => denseRange_inclR_pair h
  let g : ((Fin M → (K₁ ⊗[F] E) × (K₂ ⊗[F] E)) × (Fin M → (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) →
      ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)) :=
    fun q => ((fun i => (q.1 i).1, fun i => (q.2 i).1), (fun i => (q.1 i).2, fun i => (q.2 i).2))
  have hgc : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    exact ⟨(fun i => (a i, c i), fun i => (b i, d i)), rfl⟩
  exact hgs.denseRange.comp (hP.prodMap hP) hgc

end GlobalTheory.CompanionTheory.SaGen
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_vector_pair_two_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.denseRange_ratPairs
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem isCMExt_sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (t : E) : σ (σ t) = t := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem hform_incV {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (K : Type) [CommRing K] [Algebra F K] (x y : Fin M → E) :
    Formalism.UG.hform (sigR K σ) (JR K J) (incV K x) (incV K y) = inclR K (hf σ J x y) := by
  simp only [Formalism.UG.hform, hf, incV, JR, map_sum, map_mul, Matrix.map_apply]
  rfl

theorem exists_rational_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E,
      (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧
      (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det := by
  intro F E _ _ _ _ _ σ hσ M J hJ K _ _
  have hcc := isCMExt_sigma_sigma hσ
  obtain ⟨P, d, hP, hd, -, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) (G := J)
    two_ne_zero hcc (fun a b => hJ.1 b a)
  have hd0' := hd0 hJ.2
  let x : Fin M → Fin M → E := fun i k => σ (P k i)
  have hx : ∀ i j, hf σ J (x i) (x j) = (Matrix.diagonal d) i j := by
    intro i j
    rw [← hd]
    simp only [hf, x, hcc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  refine ⟨fun i => incV K (x i), fun i j hij => ?_, fun i => ?_, ?_⟩
  · rw [hform_incV, hx, Matrix.diagonal_apply_ne _ hij, map_zero]
  · rw [hform_incV, hx, Matrix.diagonal_apply_eq]
    exact (IsUnit.mk0 _ (hd0' i)).map _
  · have hm : Matrix.of (fun i => incV (F := F) K (x i)) = ((P.map σ).transpose).map (inclR K) := by
      ext i k
      rfl
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    have : (P.map σ).det = σ P.det := (RingHom.map_det (σ : E →+* E) P).symm
    rw [this]
    exact (IsUnit.mk0 _ ((map_ne_zero σ).2 hP)).map _

end GlobalTheory.CompanionTheory.SaGen
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_basis_base_change : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E, (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧ (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.exists_rational_orth
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.LiftSupp

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_det_eq_of_mul_entries (d : R) {A B : Matrix n n R} (h : ∀ i j, d * A i j = d * B i j) :
    d * A.det = d * B.det := by
  let I : Ideal R := LinearMap.ker (LinearMap.mulLeft R d)
  have hI : ∀ x y : R, d * x = d * y → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
    intro x y hxy
    refine Ideal.Quotient.eq.2 ?_
    change d * (x - y) = 0
    rw [mul_sub, hxy, sub_self]
  have hmap : (Ideal.Quotient.mk I).mapMatrix A = (Ideal.Quotient.mk I).mapMatrix B := by
    ext i j
    exact hI _ _ (h i j)
  have h2 : Ideal.Quotient.mk I A.det = Ideal.Quotient.mk I B.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  have h3 : A.det - B.det ∈ I := Ideal.Quotient.eq.1 h2
  have h4 : d * (A.det - B.det) = 0 := h3
  rw [mul_sub] at h4
  exact sub_eq_zero.1 h4

end Ring

section Tensor

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def pB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem iB_tmul (P : PlaceMap F K) (a : K) (b : E) : iB P (a ⊗ₜ[F] b) = P.inj a ⊗ₜ[F] b := rfl

theorem pB_tmul (P : PlaceMap F K) (a : AF F) (b : E) : pB P (a ⊗ₜ[F] b) = P.proj a ⊗ₜ[F] b := rfl

theorem algebraMap_inj_one (P : PlaceMap F K) :
    algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) = iB P (1 : K ⊗[F] E) := by
  rw [Algebra.TensorProduct.one_def, iB_tmul, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eB_mul_iB (P : PlaceMap F K) (y : K ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * iB P y = iB P y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [iB_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change (P.inj 1 * P.inj a) ⊗ₜ[F] b = _
    rw [← map_mul, one_mul]
  | add x y hx hy => rw [map_add, mul_add, hx, hy]

theorem pB_iB (P : PlaceMap F K) (y : K ⊗[F] E) : pB P (iB P y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [iB_tmul, pB_tmul, P.proj_inj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iB_pB (P : PlaceMap F K) (y : AF F ⊗[F] E) :
    iB P (pB P y) = algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [pB_tmul, iB_tmul, P.inj_proj, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem det_eq_one_of_lift (P : PlaceMap F K) {M : ℕ} {G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)}
    {X : Matrix (Fin M) (Fin M) (K ⊗[F] E)} (hG : ∀ i j, (G - 1) i j = iB P ((X - 1) i j)) (hX : X.det = 1) :
    G.det = 1 := by
  set e := algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) with he
  have hGij : ∀ i j, G i j = iB P ((X - 1) i j) + (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j := by
    intro i j
    rw [← hG]
    simp
  have hmap : (pB (E := E) P).toRingHom.mapMatrix G = X := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hGij]
    change pB P _ = _
    rw [map_add, pB_iB]
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hp : pB P G.det = 1 := by
    have h := RingHom.map_det (pB (E := E) P).toRingHom G
    rw [hmap, hX] at h
    exact h
  have h1 : e * G.det = e := by
    rw [he, ← iB_pB, hp, algebraMap_inj_one]
  have h2 : (1 - e) * G.det = (1 - e) * (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).det := by
    refine mul_det_eq_of_mul_entries (1 - e) fun i j => ?_
    rw [hGij, mul_add, sub_mul, one_mul, he, eB_mul_iB, sub_self, zero_add]
  rw [Matrix.det_one] at h2
  linear_combination h1 + h2

end Tensor

theorem lift_det_one_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type}
    [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L →
    ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) := by
  intro F E _ _ _ _ _ σ _ M J K _ _ P L hL x hx
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_eq_one_of_lift P (hL x) hx), fun i j => ?_⟩
  rw [hL x i j]
  exact eB_mul_iB P _

end GlobalTheory.CompanionTheory.SaGen.LiftSupp
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lift_special_support : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.LiftSupp.lift_det_one_mem_supp
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

section Component

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def projB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem projB_sigR (P : PlaceMap F K) (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) :
    projB P (sigR (AF F) σ y) = sigR K σ (projB P y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [projB, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem projB_inclR (P : PlaceMap F K) (e : E) : projB P (inclR (AF F) e) = inclR K e := by
  simp [projB, inclR]

theorem iB_projB (P : PlaceMap F K) (y : AF F ⊗[F] E) :
    iB P (projB P y) = algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [projB, iB, P.inj_proj, Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem cT_map_projB (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ}
    (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    Formalism.UG.cT (sigR K σ) (A.map (projB P)) = (Formalism.UG.cT (sigR (AF F) σ) A).map (projB P) := by
  ext i j
  simp [Formalism.UG.cT, projB_sigR]

theorem JR_map_projB (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    (JR (F := F) (AF F) J).map (projB P) = JR (F := F) K J := by
  ext i j
  simp [JR, projB_inclR]

end Component

theorem exists_lift_of_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E),
    ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J),
    IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J,
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g := by
  intro F E _ _ _ _ _ σ _ M J K _ _ P L hL g hg
  obtain ⟨hdet, hsupp⟩ := hg
  have hdet' := StrongApprox.mem_SUAdelic.1 hdet
  set G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J g).1 : _) with hG
  let X : GL (Fin M) (K ⊗[F] E) := Formalism.UG.bc (projB P).toRingHom (HA.mat (AF F) σ J g)
  have hXG : (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = G.map (projB P) := rfl
  have hg0 : Formalism.UG.cT (sigR (AF F) σ) G * JR (F := F) (AF F) J * G = JR (F := F) (AF F) J := g.2
  have hX : X ∈ HR K σ J := by
    change Formalism.UG.cT (sigR K σ) (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) * JR (F := F) K J * (X : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = JR (F := F) K J
    have h1 := congrArg (fun A => (projB P).toRingHom.mapMatrix A) hg0
    simp only [map_mul] at h1
    rw [hXG, cT_map_projB, ← JR_map_projB P J]
    exact h1
  let x : HA K σ J := (⟨X, hX⟩ : HR K σ J)
  have hxm : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) = G.map (projB P) := rfl
  refine ⟨x, ?_, ?_⟩
  · rw [hxm]
    have h2 := RingHom.map_det (projB P).toRingHom G
    rw [hdet'] at h2
    simpa using h2.symm
  · have hm : ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = G := by
      ext i j
      have h3 := hL x i j
      have h4 : (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j = projB P ((G - 1) i j) := by
        rw [hxm]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.one_apply_ne hij]
      rw [h4, iB_projB, hsupp i j] at h3
      exact sub_left_injective h3
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.CompanionTheory.SaGen
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_support_of_local_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lift_det_one_approx_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ (a b : Fin M → E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) (incV K a) (incV K b) ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → L x ∈ PlaneSupp σ J (P.inj 1) a b := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.LiftPlane.lift_plane | exact GlobalTheory.CompanionTheory.SaGen.LiftPlane.lift_plane | (intros; apply GlobalTheory.CompanionTheory.SaGen.LiftPlane.lift_plane <;> assumption)
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem sigR_sigR_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  intro F E _ _ _ _ _ σ h K _ _ t
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.CompanionTheory.SaGen
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_involution_involutive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_field_or_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split | exact GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split | (intros; apply GlobalTheory.CompanionTheory.SaGen.Dichotomy.field_or_split <;> assumption)
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.NormOneField

open Polynomial in

theorem normOneGen_of_imag {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (hinv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) (c : R →+* R) (θ : R) (hθ : θ ≠ 0) (hc : c θ = -θ) :
    NormOneGen c := by
  have hU : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha => by
    obtain ⟨b, hb⟩ := hinv a ha
    exact isUnit_iff_exists_inv.2 ⟨b, hb⟩
  intro α p hα _
  by_cases hp : p = 0
  · subst hp
    refine ⟨1, by simp, by simpa using hα, ?_⟩
    simpa using (hU 2 two_ne_zero).mul hα
  have hne : ∀ n : ℕ, (n : R) - θ ≠ 0 := by
    intro n h
    have e : θ = n := (sub_eq_zero.1 h).symm
    have h1 : c θ = θ := by
      rw [e, map_natCast]
    have h2 : (2 : R) * θ = 0 := by linear_combination hc - h1
    exact hθ ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  choose i hi using fun n : ℕ => hinv _ (hne n)
  set m : ℕ → R := fun n => ((n : R) + θ) * i n with hm
  have hnorm : ∀ n, m n * c (m n) = 1 := by
    intro n
    have h1 : c (((n : R) - θ) * i n) = 1 := by rw [hi, map_one]
    rw [map_mul, map_sub, map_natCast, hc] at h1
    simp only [hm, map_mul, map_add, map_natCast, hc]
    linear_combination (((n : R) - -θ) * c (i n)) * hi n + h1
  have hminj : Function.Injective m := by
    intro a b h
    have h' : ((a : R) + θ) * i a = ((b : R) + θ) * i b := h
    have h1 : ((a : R) + θ) * ((b : R) - θ) = ((b : R) + θ) * ((a : R) - θ) := by
      linear_combination ((a : R) - θ) * ((b : R) - θ) * h' - ((a : R) + θ) * ((b : R) - θ) * hi a +
        ((b : R) + θ) * ((a : R) - θ) * hi b
    have h2 : ((2 : R) * ((b : R) - a)) * θ = 0 := by linear_combination h1
    have h3 : (b : R) - a = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hθ)).resolve_left two_ne_zero
    exact (Nat.cast_injective (R := R) (sub_eq_zero.1 h3)).symm
  set q : R[X] := X ^ 2 - C (2 * α) * X + C (p * c p) with hq
  have hq0 : q ≠ 0 := by
    intro h
    have h2 := congrArg (fun r => r.coeff 2) h
    simp [hq, coeff_X, coeff_C] at h2
  have hY : ({α} ∪ {y | q.IsRoot y} : Set R).Finite :=
    (Set.finite_singleton α).union (Polynomial.finite_setOf_isRoot hq0)
  have hg : Function.Injective (fun n => m n * p) := fun a b h =>
    hminj (mul_right_cancel₀ hp h)
  obtain ⟨n, hn⟩ := (hY.preimage hg.injOn).exists_notMem
  refine ⟨m n, hnorm n, hU _ fun h => hn (Or.inl (sub_eq_zero.1 h).symm), hU _ fun h => hn (Or.inr ?_)⟩
  rw [map_mul] at h
  have h4 := hnorm n
  change q.IsRoot (m n * p)
  simp only [hq, IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination (-(m n * p)) * h - (p * c p) * h4

theorem exists_imag {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := hcm.2.1.isComplex w
  have hτ : ¬ ComplexEmbedding.IsReal w.embedding := InfinitePlace.isComplex_iff.1 hw
  have hx : ∃ x : E, σ x ≠ x := by
    by_contra h
    push Not at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hcm.2.2.2 w.embedding x
    rw [h x] at this
    exact this.symm
  obtain ⟨x, hx⟩ := hx
  have hσσ : σ (σ x) = x := w.embedding.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  exact ⟨x - σ x, sub_ne_zero.2 hx.symm, by rw [map_sub, hσσ, neg_sub]⟩

theorem normOne_of_isField : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) →
    NormOneGen (sigR K σ) := by
  intro F E _ _ _ _ _ σ hCM K _ _ hf
  haveI : Nontrivial (K ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  haveI : IsDomain (K ⊗[F] E) := hf.isDomain
  haveI : CharZero (K ⊗[F] E) :=
    charZero_of_injective_algebraMap (R := F) (algebraMap F (K ⊗[F] E)).injective
  obtain ⟨δ, hδ, hσδ⟩ := exists_imag hCM
  have hs : sigR K σ (inclR K δ) = inclR K (σ δ) := by
    simp [sigR, inclR]
  refine normOneGen_of_imag (fun a ha => hf.mul_inv_cancel ha) (sigR K σ) (inclR K δ) ?_ ?_
  · intro h
    have h1 : inclR (F := F) K (δ * δ⁻¹) = 0 := by rw [map_mul, h, zero_mul]
    rw [mul_inv_cancel₀ hδ, map_one] at h1
    exact one_ne_zero h1
  · rw [hs, hσδ, map_neg]

end GlobalTheory.CompanionTheory.SaGen.NormOneField
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_generated_of_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) → NormOneGen (sigR K σ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.NormOneField.normOne_of_isField
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.NormOneSplit

open Polynomial in

theorem exists_good {K : Type} [Field K] [CharZero K] (a p q : K) (ha : a ≠ 0) :
    ∃ m : K, m ≠ 0 ∧ a - m * p ≠ 0 ∧ a - m⁻¹ * q ≠ 0 ∧ 2 * a - m * p - m⁻¹ * q ≠ 0 := by
  set P1 : K[X] := C a - C p * X with hP1
  set P2 : K[X] := C a * X - C q with hP2
  set P3 : K[X] := C (2 * a) * X - C p * X ^ 2 - C q with hP3
  have h1 : P1 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 0) h
    simp [hP1] at this
    exact ha this
  have h2 : P2 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 1) h
    simp [hP2, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact ha this
  have h3 : P3 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 1) h
    simp [hP3, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at this
    exact ha this
  have hP : (X * P1 * P2 * P3 : K[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero X_ne_zero h1) h2) h3
  have hex : ∃ m : K, (X * P1 * P2 * P3 : K[X]).eval m ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hP (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_univ.mono fun m _ => hcon m))
  obtain ⟨m, hm⟩ := hex
  simp only [eval_mul, eval_X] at hm
  have hm0 : m ≠ 0 := fun h => hm (by simp [h])
  have e1 : a - m * p ≠ 0 := by
    intro h
    apply hm
    have : eval m P1 = 0 := by simp [hP1]; linear_combination h
    simp [this]
  have e2 : a * m - q ≠ 0 := by
    intro h
    apply hm
    have : eval m P2 = 0 := by simp [hP2]; linear_combination h
    simp [this]
  have e3 : 2 * a * m - p * m ^ 2 - q ≠ 0 := by
    intro h
    apply hm
    have : eval m P3 = 0 := by simp [hP3]; linear_combination h
    simp [this]
  refine ⟨m, hm0, e1, ?_, ?_⟩
  · intro h
    apply e2
    have : a * m - q = m * (a - m⁻¹ * q) := by field_simp
    rw [this, h, mul_zero]
  · intro h
    apply e3
    have : 2 * a * m - p * m ^ 2 - q = m * (2 * a - m * p - m⁻¹ * q) := by field_simp
    rw [this, h, mul_zero]

section Ring

variable {K R : Type} [Field K] [CharZero K] [CommRing R] [Nontrivial R] [Algebra K R]

theorem normOneGen_of_idem (c : R →+* R) (hK : ∀ a : K, c (algebraMap K R a) = algebraMap K R a)
    (e : R) (he : e * e = e) (hs : e + c e = 1) (hz : e * c e = 0)
    (hsp : ∀ r : R, ∃ a b : K, r = algebraMap K R a * e + algebraMap K R b * c e) :
    NormOneGen c := by
  set f := c e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hcf : c f = e := by
    have h := congrArg c hs
    rw [map_add, map_one] at h
    have : c f = 1 - f := by rw [← h]; ring
    rw [this, ← hs]; ring
  have he0 : e ≠ 0 := by
    intro h
    have hf0 : f = 0 := by rw [hf, h, map_zero]
    rw [h, hf0, add_zero] at hs
    exact zero_ne_one hs
  have hinj : ∀ x : K, algebraMap K R x * e = 0 → x = 0 := by
    intro x hx
    by_contra hne
    apply he0
    calc e = algebraMap K R (x⁻¹ * x) * e := by rw [inv_mul_cancel₀ hne, map_one, one_mul]
      _ = algebraMap K R x⁻¹ * (algebraMap K R x * e) := by rw [map_mul]; ring
      _ = 0 := by rw [hx, mul_zero]
  have hunit : ∀ x y : K, x ≠ 0 → y ≠ 0 → IsUnit (algebraMap K R x * e + algebraMap K R y * f) := by
    intro x y hx hy
    refine IsUnit.of_mul_eq_one (algebraMap K R x⁻¹ * e + algebraMap K R y⁻¹ * f) ?_
    have h1 : algebraMap K R x * algebraMap K R x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have h2 : algebraMap K R y * algebraMap K R y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hy, map_one]
    calc _ = (algebraMap K R x * algebraMap K R x⁻¹) * (e * e)
          + (algebraMap K R y * algebraMap K R y⁻¹) * (f * f)
          + (algebraMap K R x * algebraMap K R y⁻¹ + algebraMap K R y * algebraMap K R x⁻¹) * (e * f) := by ring
      _ = 1 := by rw [h1, h2, he, hff, hz, mul_zero, add_zero, one_mul, one_mul]; exact hs
  intro α p hα hcα
  obtain ⟨a, b, hab⟩ := hsp α
  obtain ⟨p₁, p₂, hp⟩ := hsp p
  have hba : a = b := by
    have h := hcα
    rw [hab, map_add, map_mul, map_mul, hK, hK, hcf, ← hf] at h
    have h' := congrArg (fun t => t * e) h
    have : algebraMap K R (a - b) * e = 0 := by
      rw [map_sub]
      linear_combination (-1 : R) * h' + (algebraMap K R b - algebraMap K R a) * he
        + (algebraMap K R a - algebraMap K R b) * hz
    exact sub_eq_zero.1 (hinj _ this)
  subst hba
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 : α * e = 0 := by
      rw [hab, map_zero, zero_mul, zero_mul, add_zero, zero_mul]
    exact he0 (hα.mul_right_eq_zero.1 h0)
  obtain ⟨m, hm, c1, c2, c3⟩ := exists_good a p₁ p₂ ha
  have hmm : algebraMap K R m * algebraMap K R m⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hm, map_one]
  have hμp : (algebraMap K R m * e + algebraMap K R m⁻¹ * f) * p =
      algebraMap K R (m * p₁) * e + algebraMap K R (m⁻¹ * p₂) * f := by
    rw [hp, map_mul, map_mul]
    linear_combination (algebraMap K R m * algebraMap K R p₁) * he +
      (algebraMap K R m⁻¹ * algebraMap K R p₂) * hff +
      (algebraMap K R m * algebraMap K R p₂ + algebraMap K R m⁻¹ * algebraMap K R p₁) * hz
  refine ⟨algebraMap K R m * e + algebraMap K R m⁻¹ * f, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, hK, hcf]
    rw [← hf]
    linear_combination (algebraMap K R m * algebraMap K R m⁻¹) * he +
      (algebraMap K R m * algebraMap K R m⁻¹) * hff +
      (algebraMap K R m ^ 2 + algebraMap K R m⁻¹ ^ 2) * hz + (e + f) * hmm + hs
  · rw [hμp, hab]
    have := hunit (a - m * p₁) (a - m⁻¹ * p₂) c1 c2
    convert this using 1
    simp only [map_sub]; ring
  · rw [hμp, hab]
    simp only [map_add, map_mul, hK, hcf]
    have := hunit (2 * a - m * p₁ - m⁻¹ * p₂) (2 * a - m * p₁ - m⁻¹ * p₂) c3 c3
    convert this using 1
    simp only [map_sub, map_mul, map_ofNat]; ring

end Ring

end GlobalTheory.CompanionTheory.SaGen.NormOneSplit

open GlobalTheory.CompanionTheory.SaGen.NormOneSplit in

theorem GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) := by
  intro F E _ _ _ _ _ σ hcm K _ _ e he hs hz
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hrank : Module.finrank K (K ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hcm.2.2.1
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hK : ∀ a : K, sigR K σ (algebraMap K (K ⊗[F] E) a) = algebraMap K (K ⊗[F] E) a := by
    intro a
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  refine normOneGen_of_idem (K := K) (sigR K σ) hK e he hs hz ?_
  set f := sigR K σ e with hf
  have he0 : e ≠ 0 := by
    intro h
    have hf0 : f = 0 := by rw [hf, h, map_zero]
    rw [h, hf0, add_zero] at hs
    exact zero_ne_one hs
  have hf0 : f ≠ 0 := by
    intro h
    have h1 : e = 1 := by rw [h, add_zero] at hs; exact hs
    have : f = 1 := by rw [hf, h1, map_one]
    rw [this] at h
    exact one_ne_zero h
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def] at hst
    have h1 : algebraMap K (K ⊗[F] E) s * e = 0 := by
      linear_combination e * hst - algebraMap K (K ⊗[F] E) s * he - algebraMap K (K ⊗[F] E) t * hz
    have h2 : algebraMap K (K ⊗[F] E) t * f = 0 := by
      linear_combination f * hst - algebraMap K (K ⊗[F] E) s * hz - algebraMap K (K ⊗[F] E) t * hff
    have key : ∀ (x : K) (y : K ⊗[F] E), y ≠ 0 → algebraMap K (K ⊗[F] E) x * y = 0 → x = 0 := by
      intro x y hy hxy
      by_contra hx
      apply hy
      calc y = algebraMap K (K ⊗[F] E) (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
        _ = algebraMap K (K ⊗[F] E) x⁻¹ * (algebraMap K (K ⊗[F] E) x * y) := by rw [map_mul]; ring
        _ = 0 := by rw [hxy, mul_zero]
    exact ⟨key s e he0 h1, key t f hf0 h2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hrank])
  intro r
  have hr : r ∈ Submodule.span K (Set.range ![e, f]) := by rw [htop]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hr
  obtain ⟨a, b, hab⟩ := hr
  exact ⟨a, b, by rw [← hab, Algebra.smul_def, Algebra.smul_def]⟩
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_generated_of_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split
end

section
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.IsoSplit

theorem hform_comb {R : Type} [CommRing R] {n : Type} [Fintype n] (c : R →+* R) (Jm : Matrix n n R)
    (a b a' b' : n → R) (s t p q : R) :
    Formalism.UG.hform c Jm (s • a + t • b) (p • a' + q • b') =
      c s * p * Formalism.UG.hform c Jm a a' + c s * q * Formalism.UG.hform c Jm a b' +
        c t * p * Formalism.UG.hform c Jm b a' + c t * q * Formalism.UG.hform c Jm b b' := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hR_incV (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (p q : Fin M → E) :
    hR K σ J (incV K p) (incV K q) = inclR K (hf σ J p q) := by
  have hs : ∀ t : E, sigR K σ (inclR K t) = inclR K (σ t) := by
    intro t
    simp [sigR, inclR]
  simp only [hR, Formalism.UG.hform, hf, incV, JR, Matrix.map_apply, map_sum, map_mul, hs]

theorem hf_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (p q : Fin M → E) (s : E) :
    hf σ J p (s • q) = s * hf σ J p q := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_orthogonal_pair [NumberField E] (σ : E →ₐ[F] E) (hσ : ∀ t, σ (σ t) = t) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hM : 2 ≤ M) (hJ : IsHermND σ J) :
    ∃ x y : Fin M → E, hf σ J x x ≠ 0 ∧ hf σ J y y ≠ 0 ∧ hf σ J x y = 0 ∧ hf σ J y x = 0 := by
  obtain ⟨P, d, -, hPd, -, hd⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ
    (G := J.transpose) (fun a b => hJ.1 a b)
  have hd' := hd (by rw [Matrix.det_transpose]; exact hJ.2)
  have key : ∀ a b, hf σ J (fun k => P k b) (fun k => P k a) = Matrix.diagonal d a b := by
    intro a b
    rw [← hPd]
    simp only [hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
    ring
  have hij : (⟨0, by omega⟩ : Fin M) ≠ ⟨1, by omega⟩ := by simp
  refine ⟨fun k => P k ⟨0, by omega⟩, fun k => P k ⟨1, by omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [key, Matrix.diagonal_apply_eq]; exact hd' _
  · rw [key, Matrix.diagonal_apply_eq]; exact hd' _
  · rw [key, Matrix.diagonal_apply_ne _ hij.symm]
  · rw [key, Matrix.diagonal_apply_ne _ hij]

theorem isoAt_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ K _ _ e he hsum hprod
  have hσ : ∀ t, σ (σ t) = t := by
    intro t
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := exists_orthogonal_pair σ hσ J hM hJ
  set c := sigR K σ with hc
  have hcc : c (c e) = e := by
    have h := congrArg c hsum
    rw [map_add, map_one] at h
    linear_combination h - hsum
  have hce : c e * c e = c e := by rw [← map_mul, he]
  refine ⟨e • incV K x + c e • incV K y,
    e • incV K ((hf σ J y y)⁻¹ • y) + c e • incV K ((hf σ J x x)⁻¹ • x), ?_, ?_⟩
  · change Formalism.UG.hform (sigR K σ) (JR K J) _ _ = 0
    rw [hform_comb]
    change c e * e * hR K σ J _ _ + c e * c e * hR K σ J _ _ + c (c e) * e * hR K σ J _ _ +
      c (c e) * c e * hR K σ J _ _ = 0
    simp only [hR_incV, hxy, hyx, map_zero, hcc]
    linear_combination (inclR K (hf σ J x x) + inclR K (hf σ J y y)) * hprod
  · change Formalism.UG.hform (sigR K σ) (JR K J) _ _ = 1
    rw [hform_comb]
    change c e * e * hR K σ J _ _ + c e * c e * hR K σ J _ _ + c (c e) * e * hR K σ J _ _ +
      c (c e) * c e * hR K σ J _ _ = 1
    simp only [hR_incV, hf_smul_right, hxy, hyx, mul_zero, map_zero, hcc, inv_mul_cancel₀ hx,
      inv_mul_cancel₀ hy, map_one]
    linear_combination he + hce + hsum

end GlobalTheory.CompanionTheory.SaGen.IsoSplit
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_of_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.IsoSplit.isoAt_of_split
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem isClosed_det_eq_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
  intro F E _ _ _ _ _ σ _ M J K _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (K ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing K
  haveI : T2Space (K ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo K (Module.finBasis F E)).isEmbedding.t2Space
  have hc : Continuous fun x : HA K σ J =>
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq hc.matrix_det continuous_const

end GlobalTheory.CompanionTheory.SaGen

end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_one_unitary_closed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.isClosed_det_eq_one
end

section
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem idem_mul_eq : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b → A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a :=
  @GlobalTheory.T.places_idempotent_mul_absorb

theorem supp_le_of_single : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) → (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N :=
  @GlobalTheory.T.special_unitary_support_product

theorem compact_of_singles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → IsCompact (SUSupp σ J e)) → (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) :=
  @GlobalTheory.T.isCompact_special_unitary_support

theorem dense_pair : ∀ {F : Type} [Field F] [NumberField F] {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂] [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}, IsPlacesIdem A₁ A₂ (P₁.inj 1) → IsPlacesIdem B₁ B₂ (P₂.inj 1) → Disjoint A₁ B₁ → Disjoint A₂ B₂ → DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) :=
  @GlobalTheory.T.dense_diagonal_two_places

theorem dense_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) :=
  @GlobalTheory.T.dense_vector_pair_two_places

theorem refl_list : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → NormOneGen c → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ e : Fin M → Fin M → R, (∀ i j, i ≠ j → Formalism.UG.hform c Jm (e i) (e j) = 0) → (∀ i, IsUnit (Formalism.UG.hform c Jm (e i) (e i))) → IsUnit (Matrix.of e).det → ∀ x : GL (Fin M) R, x ∈ Formalism.UG.UJ c Jm → ∃ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) ∧ l.prod = x :=
  @GlobalTheory.T.unitary_product_reflections

theorem pair_of_list : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ a₀ : Fin M → R, IsUnit (Formalism.UG.hform c Jm a₀ a₀) → ∀ H : Subgroup (GL (Fin M) R), (∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H) → ∀ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) → ((l.prod : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 → l.prod ∈ H :=
  @GlobalTheory.T.reflections_generate_subgroup

theorem exists_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E, (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧ (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det :=
  @GlobalTheory.T.orthogonal_basis_base_change

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K), ∃ L : HA K σ J →* HA (AF F) σ J, Continuous L ∧ IsLift P σ J L :=
  @GlobalTheory.T.exists_continuous_local_lift

theorem lift_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) :=
  @GlobalTheory.T.local_lift_special_support

theorem exists_of_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g :=
  @GlobalTheory.T.special_support_of_local_lift

theorem iso_plane : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsoAt K σ J → ∃ a₀ b₀ : Fin M → K ⊗[F] E, ∀ᶠ p in nhds (a₀, b₀), IsoPlane K σ J p.1 p.2 :=
  @GlobalTheory.T.isotropic_plane_open_near

theorem not_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ ε : AF F, ε * P.inj 1 = P.inj 1 → ∀ a b : Fin M → E, IsoPlane K σ J (incV K a) (incV K b) → ¬ IsCompact (PlaneSupp σ J ε a b) :=
  @GlobalTheory.T.unitary_lift_det_one_adelic_approx

theorem near_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (a₀ b₀ : Fin M → K ⊗[F] E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) a₀ b₀ ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → ∀ V ∈ nhds x, ∀ᶠ p in nhds (a₀, b₀), ∃ x' ∈ V, IsQPairOf (sigR K σ) (JR K J) p.1 p.2 ((HA.mat K σ J x').1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
  @GlobalTheory.T.unitary_quadratic_pair_perturb_nearby

theorem lift_plane : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ (a b : Fin M → E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) (incV K a) (incV K b) ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → L x ∈ PlaneSupp σ J (P.inj 1) a b :=
  @GlobalTheory.T.unitary_lift_det_one_approx_pair

theorem sigR_invol : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t :=
  @GlobalTheory.T.tensor_involution_involutive

theorem dichotomy : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 :=
  @GlobalTheory.T.tensor_field_or_split_idempotent

theorem normOne_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) → NormOneGen (sigR K σ) :=
  @GlobalTheory.T.norm_one_generated_of_field

theorem normOne_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) :=
  @GlobalTheory.T.norm_one_generated_of_split_idempotent

theorem iso_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J :=
  @GlobalTheory.T.isotropic_of_split_idempotent

theorem compact_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsField (K ⊗[F] E) → ¬ IsoAt K σ J → IsCompact (Set.univ : Set (HA K σ J)) :=
  @GlobalTheory.T.anisotropic_unitary_group_compact

theorem det_closed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} :=
  @GlobalTheory.T.det_one_unitary_closed

theorem supp_mono {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) {a b : AF F} (h : b * a = a) : SUSupp σ J a ⊆ SUSupp σ J b := by
  rintro g ⟨h1, h2⟩
  refine ⟨h1, fun i j => ?_⟩
  rw [← h2 i j, ← mul_assoc, ← map_mul, h]

theorem hR_incV {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [CommRing K] [Algebra F K]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR K σ J (incV K x) (incV K y) = inclR K (hf σ J x y) := by
  have hs : ∀ t : E, sigR K σ (inclR K t) = inclR K (σ t) := by
    intro t
    simp [sigR, inclR]
  simp only [hR, Formalism.UG.hform, hf, map_sum, map_mul, incV, hs, JR, Matrix.map_apply]

theorem normOneGen_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (K : Type) [Field K] [Algebra F K] : NormOneGen (sigR K σ) := by
  rcases dichotomy σ hCM K with h | ⟨e, h1, h2, h3⟩
  · exact normOne_field σ hCM K h
  · exact normOne_split σ hCM K e h1 h2 h3

theorem compact_of_not_iso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (hni : ¬ IsoAt K σ J) :
    IsCompact (Set.univ : Set (HA K σ J)) := by
  rcases dichotomy σ hCM K with h | ⟨e, h1, h2, h3⟩
  · exact compact_field σ hCM J hJ h hni
  · exact absurd (iso_split σ hCM J hM hJ K e h1 h2 h3) hni

theorem compact_supp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J)
    (hLc : Continuous L) (hL : IsLift P σ J L) (hc : IsCompact (Set.univ : Set (HA K σ J))) :
    IsCompact (SUSupp σ J (P.inj 1)) := by
  have e : SUSupp σ J (P.inj 1) =
      L '' {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_supp σ hCM J P L hL g hg
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact lift_mem_supp σ hCM J P L hL x hx
  rw [e]
  exact (hc.of_isClosed_subset (det_closed σ hCM J) (Set.subset_univ _)).image hLc

theorem local_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) {M : ℕ} (hM : 2 ≤ M) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (K : Type) [Field K] [Algebra F K] (H : Subgroup (GL (Fin M) (K ⊗[F] E)))
    (hH : ∀ y ∈ Formalism.UG.UJ (sigR K σ) (JR K J), IsQPair (sigR K σ) (JR K J) (y : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → y ∈ H)
    (x : GL (Fin M) (K ⊗[F] E)) (hx : x ∈ Formalism.UG.UJ (sigR K σ) (JR K J))
    (hd : (x : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1) : x ∈ H := by
  have hc : ∀ t, sigR K σ (sigR K σ t) = t := sigR_invol σ hCM K
  have hJR : ∀ i j, sigR K σ (JR K J j i) = JR K J i j := fun i j => map_mem_HermR K σ J hJ.1 i j
  obtain ⟨e, h1, h2, h3⟩ := exists_orth σ hCM J hJ K
  obtain ⟨l, hl, rfl⟩ := refl_list (sigR K σ) hc (normOneGen_sigR σ hCM K) (JR K J) hJR e h1 h2 h3 x hx
  exact pair_of_list (sigR K σ) hc (JR K J) hJR (e ⟨0, by omega⟩) (h2 _) H hH l hl hd

theorem pair_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ε : AF F) (N : Subgroup (HA (AF F) σ J)) (hN : IsClosed (N : Set (HA (AF F) σ J)))
    {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [ProperSpace K₂]
    [Algebra F K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂)
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} (hT : IsPlacesIdem T₁ T₂ (P₁.inj 1))
    (hP : ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      PlaneSupp σ J (P₁.inj 1) u₀ u₁ ⊆ N)
    (hd : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)))
    (hε : ε * P₂.inj 1 = P₂.inj 1) (hiso : IsoAt K₂ σ J)
    (L : HA K₁ σ J →* HA (AF F) σ J) (hLc : Continuous L) (hL : IsLift P₁ σ J L)
    (x : HA K₁ σ J) (a₀ b₀ : Fin M → K₁ ⊗[F] E)
    (hx : IsQPairOf (sigR K₁ σ) (JR K₁ J) a₀ b₀ ((HA.mat K₁ σ J x).1 : Matrix (Fin M) (Fin M) (K₁ ⊗[F] E))) :
    L x ∈ N := by
  rw [← SetLike.mem_coe, ← hN.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨a₂, b₂, h2⟩ := iso_plane σ hCM J hJ hiso
  obtain ⟨L₂, -, hL₂⟩ := exists_lift σ hCM J hJ P₂
  have h1 := near_pair σ hCM J hJ a₀ b₀ x hx (L ⁻¹' U) (hLc.continuousAt hU)
  have hprod := Filter.Eventually.prod_nhds h1 h2
  obtain ⟨p, ⟨x', hx'U, hx'⟩, hp2⟩ := (dense_rat σ hCM hd M).mem_nhds hprod
  have hND : PlaneND σ J p.1 p.2 := by
    intro h0
    apply hp2.1
    rw [hR_incV, hR_incV, hR_incV, hR_incV, ← map_mul, ← map_mul, ← map_sub, h0, map_zero]
  exact ⟨L x', hx'U, hP _ _ hND (not_compact σ hCM J hJ P₂ L₂ hL₂ (lift_mem_supp σ hCM J P₂ L₂ hL₂) ε hε _ _ hp2)
    (lift_plane σ hCM J hJ P₁ L hL (lift_mem_supp σ hCM J P₁ L hL) _ _ _ hx')⟩

theorem local_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) {M : ℕ} (hM : 2 ≤ M) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ε : AF F) (N : Subgroup (HA (AF F) σ J)) (hN : IsClosed (N : Set (HA (AF F) σ J)))
    {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [ProperSpace K₂]
    [Algebra F K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂)
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} (hT : IsPlacesIdem T₁ T₂ (P₁.inj 1))
    (hP : ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      PlaneSupp σ J (P₁.inj 1) u₀ u₁ ⊆ N)
    (hd : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)))
    (hε : ε * P₂.inj 1 = P₂.inj 1) (hiso : IsoAt K₂ σ J) :
    SUSupp σ J (P₁.inj 1) ⊆ N := by
  obtain ⟨L, hLc, hL⟩ := exists_lift σ hCM J hJ P₁
  intro g hg
  obtain ⟨x, hxd, rfl⟩ := exists_of_mem_supp σ hCM J P₁ L hL g hg
  let Hs : Subgroup (GL (Fin M) (K₁ ⊗[F] E)) := (N.comap L).map (HR K₁ σ J).subtype
  have hmem : (x : HR K₁ σ J).1 ∈ Hs := by
    refine local_gen σ hCM hM J hJ K₁ Hs ?_ _ x.2 hxd
    rintro y hy ⟨a, b, hab⟩
    exact ⟨⟨y, hy⟩, pair_mem σ hCM J hJ ε N hN P₁ P₂ hT hP hd hε hiso L hLc hL ⟨y, hy⟩ a b hab, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem idem_unique {F : Type} [Field F] [NumberField F] {A₁ : Finset (InfinitePlace F)}
    {A₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem A₁ A₂ b) :
    a = b := by
  have h1 := idem_mul_eq ha hb subset_rfl subset_rfl
  have h2 := idem_mul_eq hb ha subset_rfl subset_rfl
  rw [← h1, mul_comm, h2]

theorem exists_iso_place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (hM : 2 ≤ M) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    (hnc : ¬ IsCompact (SUSupp σ J ε)) :
    ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K)
      (B₁ : Finset (InfinitePlace F)) (B₂ : Finset (HeightOneSpectrum (𝓞 F))),
      B₁ ⊆ S₁ ∧ B₂ ⊆ S₂ ∧ IsPlacesIdem B₁ B₂ (P.inj 1) ∧ IsoAt K σ J := by
  by_contra hno
  apply hnc
  have key : ∀ (B₁ : Finset (InfinitePlace F)) (B₂ : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F),
      B₁ ⊆ S₁ → B₂ ⊆ S₂ → IsPlacesIdem B₁ B₂ e →
      ∀ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K),
        IsPlacesIdem B₁ B₂ (P.inj 1) → IsCompact (SUSupp σ J e) := by
    intro B₁ B₂ e h1 h2 he K n1 n2 n3 P hP
    have hni : ¬ IsoAt K σ J := fun hi => hno ⟨K, n1, n2, n3, P, B₁, B₂, h1, h2, hP, hi⟩
    obtain ⟨L, hLc, hL⟩ := exists_lift σ hCM J hJ P
    have := compact_supp σ hCM J P L hLc hL (compact_of_not_iso σ hCM J hM hJ hni)
    rwa [idem_unique hP he] at this
  refine compact_of_singles σ hCM J hε (fun w hw e he => ?_) (fun v hv e he => ?_)
  · obtain ⟨K, i1, i2, i3, P, hP⟩ := exists_placeMap_inf w
    exact key {w} ∅ e (Finset.singleton_subset_iff.2 hw) (Finset.empty_subset _) he K i1 i2 i3 P hP
  · obtain ⟨K, i1, i2, i3, P, hP⟩ := exists_placeMap_fin v
    exact key ∅ {v} e (Finset.empty_subset _) (Finset.singleton_subset_iff.2 hv) he K i1 i2 i3 P hP

theorem propGen : Sa2.PropGen := by
  intro F E _ _ _ _ _ σ hCM M J hM hJ S₁ S₂ ε hε hnc N hN hSN hP T₁ T₂ δ hδ
  obtain ⟨K₂, i1, i2, i3, P₂, B₁, B₂, hB1, hB2, hB, hiso⟩ := exists_iso_place σ hCM hM J hJ hε hnc
  have hεe : ε * P₂.inj 1 = P₂.inj 1 := idem_mul_eq hB hε hB1 hB2
  have step : ∀ (A₁ : Finset (InfinitePlace F)) (A₂ : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F),
      IsPlacesIdem A₁ A₂ e → (A₁ ⊆ S₁ ∧ A₂ ⊆ S₂ ∨ Disjoint A₁ B₁ ∧ Disjoint A₂ B₂) →
      ∀ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K),
        IsPlacesIdem A₁ A₂ (P.inj 1) → SUSupp σ J e ⊆ N := by
    intro A₁ A₂ e he hc K _ _ _ P hPi
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (supp_mono σ J (idem_mul_eq he hε h1 h2)).trans hSN
    · rw [idem_unique he hPi]
      exact local_mem σ hCM hM J hJ ε N hN P P₂ hPi
        (fun u₀ u₁ hnd hc' => hP u₀ u₁ hnd hc' _ _ _ hPi) (dense_pair P P₂ hPi hB h1 h2) hεe hiso
  refine supp_le_of_single σ J N hδ (fun w _ e he => ?_) (fun v _ e he => ?_)
  · obtain ⟨K, n1, n2, n3, P, hPi⟩ := exists_placeMap_inf w
    refine step {w} ∅ e he ?_ K n1 n2 n3 P hPi
    by_cases hw : w ∈ S₁
    · exact Or.inl ⟨Finset.singleton_subset_iff.2 hw, Finset.empty_subset _⟩
    · exact Or.inr ⟨Finset.disjoint_singleton_left.2 (fun h => hw (hB1 h)), Finset.disjoint_empty_left _⟩
  · obtain ⟨K, n1, n2, n3, P, hPi⟩ := exists_placeMap_fin v
    refine step ∅ {v} e he ?_ K n1 n2 n3 P hPi
    by_cases hv : v ∈ S₂
    · exact Or.inl ⟨Finset.empty_subset _, Finset.singleton_subset_iff.2 hv⟩
    · exact Or.inr ⟨Finset.disjoint_empty_left _, Finset.disjoint_singleton_left.2 (fun h => hv (hB2 h))⟩

end GlobalTheory.CompanionTheory.SaGen
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_generator : Sa2.PropGen := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.propGen
end
