import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), AbsIrrSub ρ W → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)), DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  first | exact @GlobalTheory.semisimple_matrix_rep_decomp | exact GlobalTheory.semisimple_matrix_rep_decomp | (intros; apply GlobalTheory.semisimple_matrix_rep_decomp <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isoSub_span_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  intro k Γ _ _ L _ f a ρ W₁ W₂ h₁ h₂ ⟨e, he⟩
  obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend (W₂.subtype ∘ₗ (e : W₁ →ₗ[k] W₂))
  obtain ⟨g₂, hg₂⟩ := LinearMap.exists_extend (W₁.subtype ∘ₗ (e.symm : W₂ →ₗ[k] W₁))
  have hg₁' : ∀ v : W₁, g₁ v = (e v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₁ v
  have hg₂' : ∀ v : W₂, g₂ v = (e.symm v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₂ v
  have key : ∀ (M : Matrix (Fin a) (Fin a) k) (v : Fin a → k),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v; funext i; exact (RingHom.map_mulVec f M v i).symm
  let φ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₁).map f).mulVecLin
  let ψ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₂).map f).mulVecLin
  have hφ : ∀ w (hw : w ∈ W₁), φ (f ∘ w) = f ∘ (e ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₁).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₁' ⟨w, hw⟩)
  have hψ : ∀ w (hw : w ∈ W₂), ψ (f ∘ w) = f ∘ (e.symm ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₂).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₂' ⟨w, hw⟩)
  set S₁ := (fun v => f ∘ v) '' (W₁ : Set (Fin a → k)) with hS₁
  set S₂ := (fun v => f ∘ v) '' (W₂ : Set (Fin a → k)) with hS₂
  have mφ : ∀ x ∈ Submodule.span L S₁, φ x ∈ Submodule.span L S₂ := by
    intro x hx
    have : Submodule.span L S₁ ≤ (Submodule.span L S₂).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change φ (f ∘ w) ∈ Submodule.span L S₂
      rw [hφ w hw]
      exact Submodule.subset_span ⟨_, (e ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have mψ : ∀ x ∈ Submodule.span L S₂, ψ x ∈ Submodule.span L S₁ := by
    intro x hx
    have : Submodule.span L S₂ ≤ (Submodule.span L S₁).comap ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change ψ (f ∘ w) ∈ Submodule.span L S₁
      rw [hψ w hw]
      exact Submodule.subset_span ⟨_, (e.symm ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have ψφ : ∀ x ∈ Submodule.span L S₁, ψ (φ x) = x := by
    intro x hx
    have : Set.EqOn (ψ ∘ₗ φ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₁ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hφ w hw, hψ _ (e ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  have φψ : ∀ x ∈ Submodule.span L S₂, φ (ψ x) = x := by
    intro x hx
    have : Set.EqOn (φ ∘ₗ ψ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₂ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hψ w hw, hφ _ (e.symm ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  let φ' : Submodule.span L S₁ →ₗ[L] Submodule.span L S₂ := φ.restrict mφ
  let ψ' : Submodule.span L S₂ →ₗ[L] Submodule.span L S₁ := ψ.restrict mψ
  refine ⟨LinearEquiv.ofLinear φ' ψ'
    (LinearMap.ext fun x => Subtype.ext (φψ x x.2))
    (LinearMap.ext fun x => Subtype.ext (ψφ x x.2)), ?_⟩
  intro g v hv
  show φ (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec v)
      = ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec (φ v)
  have : Set.EqOn (φ ∘ₗ ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin)
      (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin ∘ₗ φ) S₁ := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have hgw : (ρ g : Matrix (Fin a) (Fin a) k).mulVec w ∈ W₁ := h₁ g w hw
    rw [key, hφ _ hgw, hφ w hw, key]
    congr 1
    exact he g ⟨w, hw⟩ hgw
  exact LinearMap.eqOn_span' this v.2

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoSub_span_extension_of_scalars : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  atlas_forward_decl GlobalTheory.isoSub_span_map
end

section
section
namespace GlobalTheory

theorem span_map_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L)
    {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ →
    Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓
      Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  intro k _ L _ f a W₁ W₂ h
  have hker : LinearMap.ker (W₂.mkQ ∘ₗ W₁.subtype) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw2 : (w : Fin a → k) ∈ W₂ := by
      simpa [Submodule.Quotient.mk_eq_zero] using hw
    have hw12 : (w : Fin a → k) ∈ W₁ ⊓ W₂ := ⟨w.2, hw2⟩
    rw [h] at hw12
    exact Subtype.ext (by simpa using hw12)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W₁.subtype ∘ₗ g ∘ₗ W₂.mkQ
  have hp1 : ∀ w ∈ W₁, p w = w := by
    intro w hw
    have := LinearMap.congr_fun hg (⟨w, hw⟩ : W₁)
    have h2 : g (W₂.mkQ w) = ⟨w, hw⟩ := by simpa using this
    simp only [p, LinearMap.comp_apply, h2]
    rfl
  have hp2 : ∀ w ∈ W₂, p w = 0 := by
    intro w hw
    have h2 : W₂.mkQ w = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using hw
    simp [p, h2]
  let P : (Fin a → L) →ₗ[L] (Fin a → L) := Matrix.mulVecLin ((LinearMap.toMatrix' p).map f)
  have hP : ∀ v : Fin a → k, P (f ∘ v) = f ∘ (p v) := by
    intro v
    funext i
    have := RingHom.map_mulVec f (LinearMap.toMatrix' p) v i
    simpa [P, LinearMap.toMatrix'_mulVec] using this.symm
  have hS1 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))), P x = x := by
    intro x hx
    have heq : Set.EqOn P (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.id_apply]
      rw [hP, hp1 v hv]
    exact LinearMap.eqOn_span heq hx
  have hS2 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))), P x = 0 := by
    intro x hx
    have heq : Set.EqOn P (0 : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.zero_apply]
      rw [hP, hp2 v hv]
      funext i
      simp
    exact LinearMap.eqOn_span heq hx
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hx1, hx2⟩
  rw [← hS1 x hx1, hS2 x hx2]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ → Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  atlas_forward_decl GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct :
    ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ}
      (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) →
      (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep f ρ) W₁ W₂) →
      AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ L _ f a ρ hss habs hdist
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible ρ hss
  have hs : ∀ j, Stable (matRep ((Units.coeHom _).comp ρ)) (Vs j) :=
    fun j g v hv => (hirr j).2.1 g v hv
  have hsp : ∀ j, Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hs j g)) = ⊤ :=
    fun j => GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt ρ (Vs j) (hs j) (habs _ (hirr j))
  refine ⟨Fin n, inferInstance, inferInstance, Vs, hs, hint, fun j => (hirr j).1, hsp, ?_⟩
  intro j j' hjj' e he
  have hiso : IsoSub ρ (Vs j) (Vs j') := by
    refine ⟨e, fun g v h => ?_⟩
    have := congrArg Subtype.val (he g v)
    exact this
  have hdisj : Vs j ⊓ Vs j' = ⊥ :=
    (hint.submodule_iSupIndep.pairwiseDisjoint hjj').eq_bot
  exact hdist _ _
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j) (hs j) (hirr j).1 (hsp j))
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j') (hs j') (hirr j').1 (hsp j'))
    (GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot f (Vs j) (Vs j') hdisj)
    (GlobalTheory.T.isoSub_span_extension_of_scalars f ρ (Vs j) (Vs j') (hirr j).2.1 (hirr j').2.1 hiso)

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) → (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep f ρ) W₁ W₂) → AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  atlas_forward_decl GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  intro D i r hO hr K' _ f hd x
  exact GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso f (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) (hr x).2.1 (hO x (r x) (hr x)) (hd x)

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrr_distinct_constituents_after_extension : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  atlas_forward_decl GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct
end

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem abs_irreducible_distinct_constituents : ∀ (D : D7), SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → AbsIrreducibleDistinct D i r := by
  intro D h32 hS i r hr
  obtain ⟨K', hK', hA, _, hK⟩ := (((h32 i).2.2 r hr).2.2.1).1
  exact GlobalTheory.T.absIrr_distinct_constituents_after_extension D i r (hS i) hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)

end GlobalTheory
end
