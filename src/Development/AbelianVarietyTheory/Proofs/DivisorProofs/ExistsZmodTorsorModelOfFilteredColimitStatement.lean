import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimitStatement

section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.FpDescent

theorem exists_finitePresentation_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩

end GlobalTheory.FpDescent
end

section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePresentation_descent_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit) | (exact GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit) | (intros; apply GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit  <;> assumption)
end

section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
end

section
open CategoryTheory Limits TensorProduct

noncomputable section
namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem eventually_map_eq_zero (hc : IsColimit c) {k : J} (x : F.obj k)
    (hx : (c.ι.app k).hom x = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'), (F.map (f₀ ≫ f)).hom x = 0 := by
  have hc' := isColimitOfPreserves (forget _) hc
  have h0 : (c.ι.app k).hom x = (c.ι.app k).hom 0 := by rw [hx, map_zero]
  obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x 0).1 (by exact h0)
  refine ⟨k₀, f₀, fun k' f => ?_⟩
  have e' : (F.map f₀).hom x = 0 := by simpa using e
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

theorem eventually_map_eq_zero_finite (hc : IsColimit c) {k : J} {κ : Type} [Fintype κ]
    (x : κ → F.obj k) (hx : ∀ i, (c.ι.app k).hom (x i) = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k') (i : κ), (F.map (f₀ ≫ f)).hom (x i) = 0 := by
  classical
  suffices H : ∀ S : Finset κ, ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (x i) = 0 by
    obtain ⟨k₀, f₀, h⟩ := H Finset.univ
    exact ⟨k₀, f₀, fun k' f i => h k' f i (Finset.mem_univ i)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S _ ih =>
    obtain ⟨k₀, f₀, h⟩ := GlobalTheory.TorsorColim.eventually_and
      (fun k' (g : k ⟶ k') => (F.map g).hom (x a) = 0)
      (fun k' (g : k ⟶ k') => ∀ i ∈ S, (F.map g).hom (x i) = 0)
      (eventually_map_eq_zero hc (x a) (hx a)) ih
    refine ⟨k₀, f₀, fun k' f i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (h k' f).1
    · exact (h k' f).2 i hi

theorem exists_stage_rep (hc : IsColimit c) (k₁ : J) {ι : Type} [Finite ι] (t : ι → c.pt) :
    ∃ (K : J) (h : k₁ ⟶ K) (u : ι → F.obj K), ∀ i, (c.ι.app K).hom (u i) = t i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose jx x hx using fun i : ι => Types.jointly_surjective_of_isColimit hc' (t i)
  haveI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert k₁ (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self k₁ _)
  have hm : ∀ i, Nonempty (jx i ⟶ K) := fun i =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ i)))
  refine ⟨K, h, fun i => (F.map (hm i).some).hom (x i), fun i => ?_⟩
  have h1 := hx i
  have h2 := congr(($(c.w (hm i).some)).hom (x i))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2]
  exact h1

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem exists_late_solution (hc : IsColimit c) (k₁ : J) {ι κ : Type} [Finite ι] [Fintype κ]
    (P : κ → MvPolynomial ι (F.obj k₁)) (t : ι → c.pt)
    (ht : ∀ i, MvPolynomial.eval₂ (c.ι.app k₁).hom t (P i) = 0) :
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ u : ι → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (P i) = 0 := by
  obtain ⟨K, h, u, hu⟩ := exists_stage_rep hc k₁ t
  have hx : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (P i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app k₁).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = t := funext hu
    rw [e1, e2]; exact ht i
  obtain ⟨k₀, f₀, h0⟩ := eventually_map_eq_zero_finite hc _ hx
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun a => (F.map (f₀ ≫ f)).hom (u a), fun i => ?_⟩⟩
  have := h0 k f i
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

theorem exists_late_linear (hc : IsColimit c) (k₁ : J) (M : Type) [AddCommGroup M]
    [Module (F.obj k₁) M] [Module.FinitePresentation (F.obj k₁) M] (m : M) :
    letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
    ∀ σ : M →ₗ[F.obj k₁] c.pt, σ m = 1 →
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
      ∃ σk : M →ₗ[F.obj k₁] F.obj k, σk m = 1 := by
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  intro σ hσ
  classical
  obtain ⟨s, hs, K, hK⟩ := Module.FinitePresentation.out (R := F.obj k₁) (M := M)
  set π := Finsupp.linearCombination (F.obj k₁) (Subtype.val : s → M) with hπdef
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, hπdef, Finsupp.range_linearCombination, Subtype.range_coe_subtype]
    simpa using hs
  obtain ⟨e, he⟩ := hπ m
  have hπapp : ∀ {T : Type} [AddCommGroup T] [Module (F.obj k₁) T] (g : M →ₗ[F.obj k₁] T)
      (v : s →₀ F.obj k₁), g (π v) = ∑ x, v x • g x := by
    intro T _ _ g v
    rw [hπdef, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp), map_sum]
    simp
  let lin : (s →₀ F.obj k₁) → MvPolynomial s (F.obj k₁) :=
    fun v => ∑ x, MvPolynomial.C (v x) * MvPolynomial.X x
  have evlin : ∀ {T : Type} [CommRing T] (φ : F.obj k₁ →+* T) (u : s → T) (v : s →₀ F.obj k₁),
      MvPolynomial.eval₂ φ u (lin v) = ∑ x, φ (v x) * u x := by
    intro T _ φ u v; simp [lin, MvPolynomial.eval₂_sum]
  let P : Option K → MvPolynomial s (F.obj k₁) := fun o => o.elim (lin e - 1) (fun v => lin v.1)
  have hKker : ∀ v ∈ K, π v = 0 := fun v hv => by
    have : v ∈ Submodule.span (F.obj k₁) (K : Set (s →₀ F.obj k₁)) := Submodule.subset_span hv
    rw [hK] at this
    exact this
  obtain ⟨k₀, f₀, hsol⟩ := exists_late_solution hc k₁ P (fun x => σ x) (by
    intro o
    cases o with
    | none =>
      change MvPolynomial.eval₂ _ _ (lin e - 1) = 0
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, evlin, sub_eq_zero, ← hσ, ← he, hπapp σ e]
      rfl
    | some v =>
      change MvPolynomial.eval₂ _ _ (lin v.1) = 0
      rw [evlin]
      have := hπapp σ v.1
      rw [hKker v.1 v.2, map_zero] at this
      rw [this]
      rfl)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨u, hu⟩ := hsol k f
  let φ := Finsupp.linearCombination (F.obj k₁) u
  have hφ : ∀ v : s →₀ F.obj k₁, φ v = MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (lin v) := by
    intro v
    rw [evlin, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; simp
  have hle : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hK, Submodule.span_le]
    intro v hv
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hφ]
    exact hu (some ⟨v, hv⟩)
  refine ⟨((LinearMap.ker π).liftQ φ hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, ?_⟩
  have hq : (π.quotKerEquivOfSurjective hπ).symm m = Submodule.Quotient.mk e := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, he]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.liftQ_apply, hφ]
  have := hu none
  change MvPolynomial.eval₂ _ _ (lin e - 1) = 0 at this
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, sub_eq_zero] at this
  exact this

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

theorem exists_late_split_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧
        ∃ τ : (c.pt ⊗[F.obj j] A) →ₗ[c.pt] c.pt, τ 1 = 1) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      ∃ τ : (F.obj k ⊗[F.obj j] A) →ₗ[F.obj k] F.obj k, τ 1 = 1 := by
  intro J _ _ F c hc j A _ _ _ h
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨hfin, τ, hτ⟩ := h
  obtain ⟨k₁, f₁, hk₁⟩ := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc j A hfin
  have hfin₁ := hk₁ k₁ (𝟙 k₁)
  rw [Category.comp_id] at hfin₁
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map f₁).hom.toAlgebra
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map f₁).hom x)
    rw [← c.w f₁]; rfl)
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hfin₁
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite _ _).2 inferInstance
  let g : A →ₗ[F.obj j] c.pt :=
    (τ.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) c.pt A 1)
  let σ : (F.obj k₁ ⊗[F.obj j] A) →ₗ[F.obj k₁] c.pt := LinearMap.liftBaseChange (F.obj k₁) g
  have hσ : σ 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
    change τ (1 ⊗ₜ 1) = 1
    rw [← Algebra.TensorProduct.one_def]; exact hτ
  obtain ⟨k₀, f₀, hk₀⟩ := exists_late_linear hc k₁ _ (1 : F.obj k₁ ⊗[F.obj j] A) σ hσ
  refine ⟨k₀, f₁ ≫ f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ f₀) ≫ f)).hom.toAlgebra
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map ((f₁ ≫ f₀) ≫ f)).hom x = (F.map (f₀ ≫ f)).hom ((F.map f₁).hom x)
    rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply])
  obtain ⟨σk, hσk⟩ := hk₀ k f
  refine ⟨LinearMap.liftBaseChange (F.obj k)
    ((σk.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) (F.obj k₁) A 1)), ?_⟩
  rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
  change σk (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def]; exact hσk

end GlobalTheory.SplitColim
end
end

section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_late_split_of_filteredColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧
        ∃ τ : (c.pt ⊗[F.obj j] A) →ₗ[c.pt] c.pt, τ 1 = 1) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      ∃ τ : (F.obj k ⊗[F.obj j] A) →ₗ[F.obj k] F.obj k, τ 1 = 1 := by
  first | (exact @GlobalTheory.SplitColim.exists_late_split_of_isColimit) | (exact GlobalTheory.SplitColim.exists_late_split_of_isColimit) | (intros; apply GlobalTheory.SplitColim.exists_late_split_of_isColimit <;> assumption)
end

section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.BijDescent

theorem exists_stage_isIso {K : Type} [SmallCategory K] [IsFiltered K]
    {R₀ A B : CommRingCat.{0}} (P EA EB : K ⥤ CommRingCat.{0}) (β : ∀ k, R₀ ⟶ P.obj k)
    (fA : R₀ ⟶ A) (fB : R₀ ⟶ B) (hA : fA.hom.FinitePresentation)
    (hB : fB.hom.FinitePresentation) (g : A ⟶ B) (hg : fA ≫ g = fB)
    (uA : P ⟶ EA) (vA : (Functor.const K).obj A ⟶ EA) (uB : P ⟶ EB)
    (vB : (Functor.const K).obj B ⟶ EB)
    (hpoA : ∀ k, IsPushout fA (β k) (vA.app k) (uA.app k))
    (hpoB : ∀ k, IsPushout fB (β k) (vB.app k) (uB.app k))
    (cA : Cocone EA) (hcA : IsColimit cA) (cB : Cocone EB) (hcB : IsColimit cB)
    (iA : A ⟶ cA.pt) (iB : B ⟶ cB.pt) (hiA : ∀ k, vA.app k ≫ cA.ι.app k = iA)
    (hiB : ∀ k, vB.app k ≫ cB.ι.app k = iB) (G : cA.pt ⟶ cB.pt) [IsIso G]
    (hG : ∀ k, (hpoA k).desc (g ≫ vB.app k) (uB.app k)
      (by rw [reassoc_of% hg, (hpoB k).w]) ≫ cB.ι.app k = cA.ι.app k ≫ G) :
    ∃ m : K, ∀ (l : K) (_ : m ⟶ l), IsIso ((hpoA l).desc (g ≫ vB.app l) (uB.app l)
      (by rw [reassoc_of% hg, (hpoB l).w])) := by
  let gs : ∀ k, EA.obj k ⟶ EB.obj k := fun k =>
    (hpoA k).desc (g ≫ vB.app k) (uB.app k) (by rw [reassoc_of% hg, (hpoB k).w])
  have gv : ∀ k, vA.app k ≫ gs k = g ≫ vB.app k := fun k => (hpoA k).inl_desc _ _ _
  have gu : ∀ k, uA.app k ≫ gs k = uB.app k := fun k => (hpoA k).inr_desc _ _ _
  have vAn : ∀ {k l} (f : k ⟶ l), vA.app k ≫ EA.map f = vA.app l := fun f =>
    (vA.naturality f).symm.trans (Category.id_comp _)
  have vBn : ∀ {k l} (f : k ⟶ l), vB.app k ≫ EB.map f = vB.app l := fun f =>
    (vB.naturality f).symm.trans (Category.id_comp _)
  have gnat : ∀ {k l} (f : k ⟶ l), EA.map f ≫ gs l = gs k ≫ EB.map f := by
    intro k l f
    apply (hpoA k).hom_ext
    · rw [reassoc_of% (vAn f), gv, reassoc_of% (gv k), vBn]
    · rw [← uA.naturality_assoc, gu, reassoc_of% (gu k), uB.naturality]
  obtain ⟨k₀⟩ := IsFiltered.nonempty (C := K)
  have hAG : iA ≫ G = g ≫ iB := by
    rw [← hiA k₀, Category.assoc, ← hG, reassoc_of% (gv k₀), hiB]
  let αA : (Functor.const K).obj R₀ ⟶ EA := (Functor.const K).map fA ≫ vA
  let αB : (Functor.const K).obj R₀ ⟶ EB := (Functor.const K).map fB ≫ vB
  obtain ⟨m, s, hs⟩ := GlobalTheory.TorsorColim.exists_stage_factor (I := Unit) EA αA fB cA hcA hB
    (fun _ => iB ≫ inv G) (fun _ k => by
      change fB ≫ iB ≫ inv G = (fA ≫ vA.app k) ≫ cA.ι.app k
      rw [Category.assoc, hiA, ← hg, Category.assoc, ← reassoc_of% hAG, IsIso.hom_inv_id,
        Category.comp_id])
  have hs1 : fB ≫ s () = fA ≫ vA.app m := (hs ()).1
  have hs2 : s () ≫ cA.ι.app m = iB ≫ inv G := (hs ()).2
  obtain ⟨m₁, p₁, hp₁⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EA αA fA cA hcA
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hA)) (k := m)
    (fun _ => g ≫ s ()) (fun _ => vA.app m) (fun _ => by rw [reassoc_of% hg, hs1]; rfl)
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hs2, hiA, ← reassoc_of% hAG, IsIso.hom_inv_id, Category.comp_id])
  obtain ⟨m₂, p₂, hp₂⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EB αB fB cB hcB
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hB)) (k := m)
    (fun _ => s () ≫ gs m) (fun _ => vB.app m)
    (fun _ => by
      change fB ≫ s () ≫ gs m = fB ≫ vB.app m
      rw [reassoc_of% hs1, gv, reassoc_of% hg])
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hG, reassoc_of% hs2, IsIso.inv_hom_id, Category.comp_id, hiB])
  let a := IsFiltered.leftToMax m₁ m₂
  let b := IsFiltered.rightToMax m₁ m₂
  let e := IsFiltered.coeqHom (p₁ ≫ a) (p₂ ≫ b)
  have he : (p₁ ≫ a) ≫ e = (p₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (p₁ ≫ a) (p₂ ≫ b), fun l f => ?_⟩
  obtain ⟨F', hF'⟩ : ∃ F' : m ⟶ l, F' = (p₁ ≫ a) ≫ e ≫ f := ⟨_, rfl⟩
  have h₁ : g ≫ s () ≫ EA.map F' = vA.app l := by
    subst hF'
    have := hp₁ ()
    simp only [Category.assoc] at this
    rw [← vAn ((p₁ ≫ a) ≫ e ≫ f)]
    simp only [EA.map_comp, Category.assoc]
    rw [reassoc_of% this]
  have h₂ : s () ≫ gs m ≫ EB.map F' = vB.app l := by
    subst hF'
    have := hp₂ ()
    simp only [Category.assoc] at this
    rw [← Category.assoc (p₁ ≫ a), he, ← vBn ((p₂ ≫ b) ≫ e ≫ f)]
    simp only [EB.map_comp, Category.assoc]
    rw [reassoc_of% this]
  let σ : EB.obj l ⟶ EA.obj l := (hpoB l).desc (s () ≫ EA.map F') (uA.app l)
    (by rw [reassoc_of% hs1, vAn, (hpoA l).w])
  have σv : vB.app l ≫ σ = s () ≫ EA.map F' := (hpoB l).inl_desc _ _ _
  have σu : uB.app l ≫ σ = uA.app l := (hpoB l).inr_desc _ _ _
  refine ⟨σ, ?_, ?_⟩
  · apply (hpoA l).hom_ext
    · change vA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gv l), σv, h₁, Category.comp_id]
    · change uA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gu l), σu, Category.comp_id]
  · apply (hpoB l).hom_ext
    · change vB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σv, gnat, h₂, Category.comp_id]
    · change uB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σu, gu, Category.comp_id]

end GlobalTheory.BijDescent

namespace GlobalTheory.BijDescent

theorem bijective_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  intro J _ _ F c hc j R S _ _ _ _ _ _ φ _ hbij
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let fR : F.obj j ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap (F.obj j) R)
  let fS : F.obj j ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap (F.obj j) S)
  have hfR : fR.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  have hfS : fS.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom φ.toRingHom
  have hg : fR ≫ g = fS := by ext x; exact φ.commutes x
  have sqR := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt R).flip
  have sqS := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt S).flip
  obtain ⟨ER, ιR, uR, vR, ⟨hER⟩, hkR⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fR _ _ sqR
  obtain ⟨ES, ιS, uS, vS, ⟨hES⟩, hkS⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fS _ _ sqS
  let G : CommRingCat.of (c.pt ⊗[F.obj j] R) ⟶ CommRingCat.of (c.pt ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ).toRingHom
  haveI : IsIso G := (ConcreteCategory.isIso_iff_bijective G).2 hbij
  have hGr : g ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := S)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := R)).toRingHom ≫ G := by
    ext x; simp [g, G]
  obtain ⟨m, hm⟩ := exists_stage_isIso (K := Under j) (Under.forget j ⋙ F) ER ES
    (fun k => F.map k.hom) fR fS hfR hfS g hg uR vR uS vS (fun k => (hkR k).1) (fun k => (hkS k).1)
    (Cocone.mk _ ιR) hER (Cocone.mk _ ιS) hES _ _ (fun k => (hkR k).2.1) (fun k => (hkS k).2.1) G
    (fun k => by
      have key : ∀ d : ER.obj k ⟶ ES.obj k, vR.app k ≫ d = g ≫ vS.app k →
          uR.app k ≫ d = uS.app k → d ≫ ιS.app k = ιR.app k ≫ G := by
        intro d hd1 hd2
        apply (hkR k).1.hom_ext
        · rw [reassoc_of% hd1, (hkS k).2.1, reassoc_of% (hkR k).2.1, hGr]
        · change uR.app k ≫ d ≫ ιS.app k = uR.app k ≫ ιR.app k ≫ G
          erw [reassoc_of% hd2, (hkS k).2.2, reassoc_of% (hkR k).2.2]
          ext x
          simp [G]
      exact key _ ((hkR k).1.inl_desc _ _ _) ((hkR k).1.inr_desc _ _ _))
  refine ⟨m.right, m.hom, fun k f => ?_⟩
  let l : Under j := Under.mk (m.hom ≫ f)
  obtain ⟨d, hd1, hd2, hdiso⟩ : ∃ d : ER.obj l ⟶ ES.obj l, vR.app l ≫ d = g ≫ vS.app l ∧
      uR.app l ≫ d = uS.app l ∧ IsIso d :=
    ⟨_, (hkR l).1.inl_desc _ _ _, (hkR l).1.inr_desc _ _ _, hm l (Under.homMk f rfl)⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (m.hom ≫ f)).hom.toAlgebra
  have tR := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) R).flip
  have tS := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) S).flip
  let M : CommRingCat.of (F.obj k ⊗[F.obj j] R) ⟶ CommRingCat.of (F.obj k ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ).toRingHom
  have hM : M = ((hkR l).1.isoIsPushout _ _ tR).inv ≫ d ≫ ((hkS l).1.isoIsPushout _ _ tS).hom := by
    apply tR.hom_ext
    · erw [IsPushout.inl_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd1,
        IsPushout.inl_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M, g]
    · erw [IsPushout.inr_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd2,
        IsPushout.inr_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M]
  haveI : IsIso M := by rw [hM]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective M).1 this

end GlobalTheory.BijDescent
end

section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_baseChange_descends_filteredColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  first | (exact @GlobalTheory.BijDescent.bijective_of_isColimit) | (exact GlobalTheory.BijDescent.bijective_of_isColimit) | (intros; apply GlobalTheory.BijDescent.bijective_of_isColimit  <;> assumption)
end

section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem bc_prodMapOf_bijective_iff (R T A : Type) [CommRing R] [CommRing T] [CommRing A] [Algebra R T]
    [Algebra R A] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) :
    Function.Bijective (prodMapOf T (T ⊗[R] A) q (bcAct T act)) ↔
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  let e1 : (T ⊗[R] A) ⊗[T] (T ⊗[R] A) ≃ₐ[T] T ⊗[R] (A ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R T T (T ⊗[R] A) A).trans
      (Algebra.TensorProduct.assoc R R T T A A)
  let e2 : T ⊗[R] (Multiplicative (ZMod q) → A) ≃ₐ[T] (Multiplicative (ZMod q) → T ⊗[R] A) :=
    Algebra.TensorProduct.piRight R T T (fun _ : Multiplicative (ZMod q) => A)
  have key : ∀ x, prodMapOf T (T ⊗[R] A) q (bcAct T act) x =
      e2 (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act) (e1 x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
    | tmul u v =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, hu, hu', map_add, map_add, map_add]
      | tmul t a =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, hv, hv', map_add, map_add, map_add]
        | tmul t' a' =>
          funext g
          simp [e1, e2, Algebra.TensorProduct.cancelBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
            Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight_tmul, mul_comm]
  have hf : ⇑(prodMapOf T (T ⊗[R] A) q (bcAct T act)) =
      e2 ∘ (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) ∘ e1 := funext key
  rw [hf]
  constructor
  · intro h
    have := (e2.symm.bijective.comp h).comp e1.symm.bijective
    convert this using 1
    funext y; simp
  · intro h
    exact e2.bijective.comp (h.comp e1.bijective)

theorem prodMapOf_finite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (q : ℕ) (hq : 0 < q)
    (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) : (prodMapOf R A q act).toRingHom.Finite := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hc : ((prodMapOf R A q act).toRingHom.comp
      (Algebra.TensorProduct.includeLeft (S := R) (A := A) (B := A)).toRingHom) =
      algebraMap A (Multiplicative (ZMod q) → A) := by
    ext x g
    simp [prodMapOf]
  have : (algebraMap A (Multiplicative (ZMod q) → A)).Finite := by
    exact RingHom.finite_algebraMap.2 inferInstance
  exact RingHom.Finite.of_comp_finite (hc ▸ this)

theorem eventually_prodMapOf_bijective : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  intro J _ _ F c hc q hq j A _ _ _ actA hT
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.FinitePresentation (F.obj j) (A ⊗[F.obj j] A) :=
    Algebra.FinitePresentation.trans (F.obj j) A (A ⊗[F.obj j] A)
  have hb : letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) (prodMapOf (F.obj j) A q actA)) := by
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    exact (bc_prodMapOf_bijective_iff (F.obj j) c.pt A q hq actA).1 hT.2.2.2
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.bijective_baseChange_descends_filteredColimit J F c hc j _ _ (prodMapOf (F.obj j) A q actA)
    (prodMapOf_finite _ _ q hq actA) hb
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  exact (bc_prodMapOf_bijective_iff (F.obj j) (F.obj k) A q hq actA).2 (hk k f)

end GlobalTheory.TorsorColim
end

section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  first | (exact @GlobalTheory.TorsorColim.eventually_prodMapOf_bijective) | (exact GlobalTheory.TorsorColim.eventually_prodMapOf_bijective) | (intros; apply GlobalTheory.TorsorColim.eventually_prodMapOf_bijective  <;> assumption)
end

section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem unit_splits_of_projective_faithfullyFlat :
    ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  intro R D _ _ _ _ hP hF
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
  let ev : (D →ₗ[R] R) →ₗ[R] R :=
    { toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hI : LinearMap.range ev = ⊤
  · obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)
    exact ⟨τ, hτ⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (LinearMap.range ev) hI
  exfalso
  have hcoord : ∀ x : D, s 1 x ∈ m := fun x =>
    hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by
    have : Finsupp.linearCombination R id (s 1) = (1 : D) := LinearMap.congr_fun hs 1
    rw [← this, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top
  have hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D) := by
    intro d y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x z hx hz
      rw [mul_add]; exact Submodule.add_mem _ hx hz
  apply Module.FaithfullyFlat.submodule_ne_top (M := D) hm
  rw [eq_top_iff]
  intro d _
  simpa using hmul d 1 h1

end GlobalTheory
end

section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  first | (exact @GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (exact GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (intros; apply GlobalTheory.unit_splits_of_projective_faithfullyFlat  <;> assumption)
end

section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem faithfullyFlat_of_split : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Projective R D →
    (∃ τ : D →ₗ[R] R, τ 1 = 1) → Module.FaithfullyFlat R D := by
  intro R D _ _ _ hP ⟨τ, hτ⟩
  haveI : Module.Flat R D := inferInstance
  refine ⟨fun m hm h => ?_⟩
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by rw [h]; exact Submodule.mem_top
  have h2 : ∀ x ∈ m • (⊤ : Submodule R D), τ x ∈ m := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr d _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ hr
    · rw [map_add]; exact m.add_mem hx hy
  have := h2 1 h1
  rw [hτ] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)

theorem isZModTorsor_of_algEquiv : ∀ (R D D' : Type) [CommRing R] [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D'] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[R] D)) (act' : Multiplicative (ZMod q) →* (D' ≃ₐ[R] D'))
    (e : D ≃ₐ[R] D'), (∀ (g : Multiplicative (ZMod q)) (x : D), e (act g x) = act' g (e x)) →
    GlobalTheory.LocAcyc.IsZModTorsor R D q act → GlobalTheory.LocAcyc.IsZModTorsor R D' q act' := by
  intro R D D' _ _ _ _ _ q act act' e he hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have el : D ≃ₗ[R] D' := e.toLinearEquiv
  refine ⟨Module.Finite.equiv el, Module.Projective.of_equiv el, ?_, ?_⟩
  · exact Module.FaithfullyFlat.of_linearEquiv R D el.symm
  · let eT : D ⊗[R] D ≃ₐ[R] D' ⊗[R] D' := Algebra.TensorProduct.congr e e
    let eP : (Multiplicative (ZMod q) → D) ≃ₐ[R] (Multiplicative (ZMod q) → D') :=
      AlgEquiv.piCongrRight (fun _ => e)
    have key : ∀ x, GlobalTheory.TorsorColim.prodMapOf R D' q act' (eT x) = eP (GlobalTheory.TorsorColim.prodMapOf R D q act x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        funext g
        simp [eT, eP, he]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have hb : Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D q act) := h4
    have : ⇑(GlobalTheory.TorsorColim.prodMapOf R D' q act') = eP ∘ (GlobalTheory.TorsorColim.prodMapOf R D q act) ∘ eT.symm := by
      funext y
      simp only [Function.comp_apply]
      rw [← key, AlgEquiv.apply_symm_apply]
    change Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D' q act')
    rw [this]
    exact eP.bijective.comp (hb.comp eT.symm.bijective)

theorem exists_torsor_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc q hq D _ _ act hD
  haveI : Module.Finite c.pt D := hD.1
  haveI : Module.Projective c.pt D := hD.2.1
  haveI : Module.FinitePresentation c.pt D := Module.finitePresentation_of_projective c.pt D
  obtain ⟨j, A, _, _, _, he0⟩ := GlobalTheory.T.exists_finitePresentation_descent_of_isColimit J F c hc D inferInstance
  obtain ⟨k, B, _, _, _, actB, e, he⟩ := GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered J F c hc q hq j A D act he0
  letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
  have hT : GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj k] B) q
      (GlobalTheory.TorsorColim.bcAct c.pt actB) := by
    refine GlobalTheory.TorsorColim.isZModTorsor_of_algEquiv c.pt D _ q act _ e.symm (fun g y => ?_) hD
    apply e.injective
    rw [he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have h1 := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc k B hT.1
  have h2 := GlobalTheory.T.projective_eventually_filteredColimit_algebra J F c hc k B ⟨hT.1, hT.2.1⟩
  have h3 := GlobalTheory.T.exists_late_split_of_filteredColimit J F c hc k B ⟨hT.1, GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat _ _ hT.1 hT.2.1 hT.2.2.1⟩
  have h4 := GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit J F c hc q hq k B actB hT
  have h34 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; ∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h3 h4
  have h234 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h2 h34
  obtain ⟨m, f₀, hm⟩ := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Finite (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B) ∧ (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h1 h234
  obtain ⟨i1, i2, ⟨τ, hτ⟩, i4⟩ := hm m (𝟙 m)
  refine ⟨m, ?_⟩
  letI : Algebra (F.obj k) (F.obj m) := (F.map (f₀ ≫ 𝟙 m)).hom.toAlgebra
  letI : Algebra (F.obj m) c.pt := (c.ι.app m).hom.toAlgebra
  haveI : IsScalarTower (F.obj k) (F.obj m) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app k).hom x = (c.ι.app m).hom ((F.map (f₀ ≫ 𝟙 m)).hom x)
    rw [← c.w (f₀ ≫ 𝟙 m)]
    rfl)
  exact ⟨F.obj m ⊗[F.obj k] B, inferInstance, inferInstance, GlobalTheory.TorsorColim.bcAct (F.obj m) actB,
    ⟨i1, i2, GlobalTheory.TorsorColim.faithfullyFlat_of_split _ _ i2 ⟨τ, hτ⟩, i4⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange (F.obj k) (F.obj m) c.pt c.pt B).trans e⟩⟩

end GlobalTheory.TorsorColim
end

section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit  <;> assumption)
end
