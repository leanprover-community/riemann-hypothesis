import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFrameLoc

theorem scaleD_scaleD {R : Type} [CommRing R] {G : Over (Sp R)} (a b : R)
    (y : Chart.sp (R₀ := R) (DualNumber R) ⟶ G) :
    Chart.spMap (Chart.scaleD a) ≫ Chart.spMap (Chart.scaleD b) ≫ y = Chart.spMap (Chart.scaleD (a * b)) ≫ y := by
  rw [← Category.assoc, Chart.spMap_comp]
  congr 2
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleD]
  · simp only [Chart.scaleD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    ring

theorem isLieBasis_scale {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {u : Fin n → (epsR R ⟶ G)}
    (hu : IsLieBasis u) (a : Fin n → Rˣ)
    (ht : ∀ i, IsTangent (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) :
    IsLieBasis (fun i => (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) := by
  have key : ∀ c : Fin n → R, Chart.prodPts c (fun i => Chart.spMap (Chart.scaleD (a i : R)) ≫ u i) =
      Chart.prodPts (fun i => c i * a i) u := fun c => by
    unfold Chart.prodPts
    exact congrArg List.prod (congrArg List.ofFn (funext fun i => scaleD_scaleD _ _ _))
  refine ⟨ht, fun w hw => ?_⟩
  obtain ⟨c, hc, huniq⟩ := hu.2 w hw
  refine ⟨fun i => c i * ↑(a i)⁻¹, ?_, fun c' hc' => ?_⟩
  · rw [Chart.isLieComb_iff] at hc ⊢
    rw [key, hc]
    congr 1
    funext i
    simp [mul_assoc]
  · replace hc' := (Chart.isLieComb_iff _ _ _).mp hc'
    rw [key] at hc'
    have := huniq _ ((Chart.isLieComb_iff _ _ _).mpr hc')
    funext i
    have hi := congrFun this i
    rw [← hi]
    simp [mul_assoc]

end GlobalTheory.LieFrameLoc

open GlobalTheory.LieFrameLoc in
open scoped CategoryTheory.Obj in

theorem GlobalTheory.exists_tangent_isLieBasis_atPrime : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  intro R _ G _ hsm p _
  haveI := hsm
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  have hGp : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  obtain ⟨n, u, hu⟩ := Chart.exists_isLieBasis (Chart.Gp (G := G) p) hGp
  have lift : ∀ i, ∃ q ∈ p.primeCompl, ∃ w : epsR R ⟶ G, IsTangent w ∧
      Chart.resP p w = Chart.spMap (Chart.scaleD (algebraMap R (Localization.AtPrime p) q)) ≫ u i := by
    intro i
    have hT : Chart.TanS (Chart.pushR G (u i)) := (Chart.isTan_iff_tanS p (u i)).mp ((Chart.isTan_iff _).mpr (hu.1 i))
    obtain ⟨q, hq, w, hw, he⟩ := Chart.tan_prime_lift p hT
    refine ⟨q, hq, w, (Chart.isTan_iff _).mp hw, Chart.pushR_inj G ?_⟩
    rw [Chart.pushR_resP, he, Chart.pushR_spMap]
    congr 2
  choose q hq w hw hres using lift
  refine ⟨n, w, hw, fun G' _ ψ hψ v hv => ?_⟩
  let a : Fin n → (Localization.AtPrime p)ˣ := fun i => (IsLocalization.map_units _ ⟨q i, hq i⟩).unit
  have hres' : ∀ i, Chart.resP p (w i) = Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i := hres
  have htan : ∀ i, IsTangent (Chart.resP p (w i)) := fun i =>
    (Chart.isTan_iff _).mp ((Chart.isTan_iff_tanS p _).mpr (by
      rw [Chart.pushR_resP]; exact Chart.tanS_restrict _ ((Chart.isTan_iff _).mpr (hw i))))
  have hbasis : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    have e : (fun i => Chart.resP p (w i)) = fun i => Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i :=
      funext hres'
    rw [e]
    exact isLieBasis_scale hu a fun i => hres' i ▸ htan i
  let φp : Localization.AtPrime p →+* Localization.AtPrime p := RingHom.id _
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = algebraMap R (Localization.AtPrime p) := RingHom.id_comp _
  have hsp : spMap (algebraMap R (Localization.AtPrime p)) = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ hψ
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have hv' : ∀ j, (v j).left ≫ ψ = spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (w j).left := hv
  refine Chart.isLieBasis_baseChange φp hG hbasis fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv' j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p)))) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p)))) ≫
        Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [φp, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_localization_lift : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  atlas_forward_decl GlobalTheory.exists_tangent_isLieBasis_atPrime
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSpanLoc

open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal

theorem exists_smul_mem_span : ∀ {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G],
    Smooth G.hom → ∀ (a : OAct O G) (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → GlobalTheory.Serre.Lie a),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i).hom (v i)) → IsLieBasis v) →
    ∀ l : GlobalTheory.Serre.Lie a, ∃ s ∉ p, s • l ∈ Submodule.span R (Set.range w) := by
  intro R O _ _ G _ _ hsm a p _ n w hw l
  haveI := hsm
  let Gp := (Over.pullback (spMap (algebraMap R (Localization.AtPrime p)))).obj G
  letI : GrpObj Gp := Functor.grpObjObj
  haveI : IsCommMonObj Gp := Functor.isCommMonObj_obj
  have hp := isGrpPullback_pullback G (spMap (algebraMap R (Localization.AtPrime p)))
  obtain ⟨ap, hap⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a hp
  obtain ⟨ρ, hρ, -⟩ := exists_res hp a ap hap
  have hb := hw Gp _ hp (fun i => (ρ (w i)).hom) (fun i => hρ (w i))
  have hbij := (Lie.isLieBasis_iff (a := ap) fun i => ρ (w i)).1 hb
  obtain ⟨c, hc⟩ := hbij.2 (ρ l)
  rw [Fintype.linearCombination_apply] at hc
  obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin n)) c
  choose b hb' using fun i => hqi i (Finset.mem_univ _)
  have hz : ρ (q • l - ∑ i, b i • w i) = 0 := by
    rw [map_sub, map_smulₛₗ, ← hc, map_sum, Finset.smul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hb', smul_smul, Algebra.smul_def]
  obtain ⟨r, hr, e⟩ := exists_smul_eq_zero a p (q • l - ∑ i, b i • w i) (by
    have e := hρ (q • l - ∑ i, b i • w i)
    have e₀ := hρ 0
    rw [map_zero, Lie.hom_zero, Lie.hom_zero] at e₀
    rw [hz, Lie.hom_zero] at e
    exact e.symm.trans e₀)
  refine ⟨r * q, p.primeCompl.mul_mem hr hq, ?_⟩
  rw [mul_smul, sub_eq_zero.1 ((smul_sub _ _ _).symm.trans e)]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end GlobalTheory.LieSpanLoc
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_localization_independent : ∀ {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G],
    Smooth G.hom → ∀ (a : OAct O G) (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → GlobalTheory.Serre.Lie a),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i).hom (v i)) → IsLieBasis v) →
    ∀ l : GlobalTheory.Serre.Lie a, ∃ s ∉ p, s • l ∈ Submodule.span R (Set.range w) := by
  atlas_forward_decl GlobalTheory.LieSpanLoc.exists_smul_mem_span
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isLieBasis_of_local_restrict : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G], Smooth G.hom →
    ∀ (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → (epsR R ⟶ G)),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) →
    ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T), (IsLocalRing.maximalIdeal T).comap g = p →
    ∀ (G' : Over (Sp T)) [GrpObj G'] (ψ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) ψ →
    ∀ v : Fin n → (epsR T ⟶ G'), (∀ i, GlobalTheory.IsVecOver g ψ (w i) (v i)) → IsLieBasis v := by
  intro R _ G _ hsm p _ n w hw T _ _ g hg G' _ ψ h v hv
  haveI : Smooth G.hom := hsm
  let φp : Localization.AtPrime p →+* T := IsLocalization.lift (M := p.primeCompl) (g := g)
    (fun x => not_not.1 fun h0 => x.2 (hg ▸ (show x.1 ∈ (IsLocalRing.maximalIdeal T).comap g from h0)))
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = g := IsLocalization.lift_comp _
  have hsp : spMap g = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ h
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  have hb : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    refine hw (Chart.Gp (G := G) p) (pullback.fst G.hom (Chart.fB R (Localization.AtPrime p)))
      (isGrpPullback_pullback G (Chart.fB R (Localization.AtPrime p))) _ fun i => ?_
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w i))
    simp only [Chart.pushR_left, Over.comp_left] at e
    exact e
  refine Chart.isLieBasis_baseChange φp hG hb fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR g)) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap T (DualNumber T))) ≫ Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_localization_spans : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G], Smooth G.hom →
    ∀ (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → (epsR R ⟶ G)),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) →
    ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T), (IsLocalRing.maximalIdeal T).comap g = p →
    ∀ (G' : Over (Sp T)) [GrpObj G'] (ψ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) ψ →
    ∀ v : Fin n → (epsR T ⟶ G'), (∀ i, GlobalTheory.IsVecOver g ψ (w i) (v i)) → IsLieBasis v := by
  atlas_forward_decl GlobalTheory.isLieBasis_of_local_restrict
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj
open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal

theorem lieBaseChange_equiv : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap (algebraMap R R')) φ →
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, ∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v) := by
  intro F _ _ 𝔠 R R' _ _ _ X X' φ h
  set f := algebraMap R R' with hf
  obtain ⟨ρ, hρ, -⟩ := exists_res h.grp X.rm X'.rm h.act
  letI : Module R X'.Lie := Module.compHom X'.Lie f
  haveI : IsScalarTower R R' X'.Lie := ⟨fun r s v => by
    show (r • s) • v = f r • (s • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let ρR : X.Lie →ₗ[R] X'.Lie :=
    { toFun := ρ, map_add' := ρ.map_add, map_smul' := fun r v => ρ.map_smulₛₗ r v }
  let e₀ : R' ⊗[R] X.Lie →ₗ[R'] X'.Lie := LinearMap.liftBaseChange R' ρR
  have he₀ : ∀ (c : R') v, e₀ (c ⊗ₜ v) = c • ρ v := fun c v => by
    simp [e₀, ρR, LinearMap.liftBaseChange_tmul]
  have corr : ∀ v v', LieCorr f φ v v' ↔ v' = ρ v := fun v v' =>
    ⟨fun e => Serre.Lie.ext ((existsUnique_isVecOver h.grp.1 v.hom).unique e (hρ v)), fun e => e ▸ hρ v⟩
  have hsm := X.dim.smooth
  have hsm' := X'.dim.smooth

  have loc : ∀ (q : Ideal R') [q.IsPrime], (∀ z, e₀ z = 0 → ∃ u ∉ q, u • z = 0) ∧
      ∀ y, ∃ u ∉ q, u • y ∈ LinearMap.range e₀ := by
    intro q _
    let T := Localization.AtPrime q
    let gT := algebraMap R' T
    letI : GrpObj ((Over.pullback (spMap gT)).obj X'.A) := Functor.grpObjObj
    haveI : IsCommMonObj ((Over.pullback (spMap gT)).obj X'.A) := Functor.isCommMonObj_obj
    have hq := isGrpPullback_pullback X'.A (spMap gT)
    obtain ⟨aq, haq⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X'.rm hq
    obtain ⟨ρq, hρq, -⟩ := exists_res hq X'.rm aq haq
    have hc : IsGrpPullback ((Over.pullback (spMap gT)).obj X'.A) X.A (spMap (gT.comp f))
        (pullback.fst X'.A.hom (spMap gT) ≫ φ) := by
      have := hq.comp h.grp
      rwa [spMap_comp_spMap] at this
    set p := q.comap f with hp
    obtain ⟨n, w₀, hw₀, hw⟩ := GlobalTheory.T.tangent_vectors_localization_lift X.A hsm p
    let w : Fin n → X.Lie := fun i => Serre.Lie.mk X.rm (w₀ i) (hw₀ i)
    have hmax : (IsLocalRing.maximalIdeal T).comap (gT.comp f) = p := by
      rw [← Ideal.comap_comap]
      exact congrArg (Ideal.comap f) (Localization.AtPrime.comap_maximalIdeal (I := q))
    have hB := GlobalTheory.T.tangent_frame_localization_spans hsm p w₀ hw T (gT.comp f) hmax _ _ hc
      (fun i => (ρq (ρ (w i))).hom) fun i => by
        have e1 := hρq (ρ (w i))
        have e2 := hρ (w i)
        unfold IsVecOver at e1 e2 ⊢
        rw [← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, spMap_comp_spMap,
          ← Chart.dualMapR_comp]
        rfl
    rw [Serre.Lie.isLieBasis_iff] at hB
    refine ⟨fun z hz => ?_, fun y => ?_⟩
    ·
      have span : ∀ z : R' ⊗[R] X.Lie, ∃ s ∉ p, ∃ c : Fin n → R', f s • z = ∑ i, c i ⊗ₜ w i := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => exact ⟨1, p.primeCompl.one_mem, 0, by simp⟩
        | tmul r l =>
          obtain ⟨s, hs, hl⟩ := GlobalTheory.T.tangent_frame_localization_independent hsm X.rm p w (fun G' _ ψ hψ v hv => hw G' ψ hψ v hv) l
          obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hl
          refine ⟨s, hs, fun i => f (b i) * r, ?_⟩
          calc f s • (r ⊗ₜ[R] l) = (s • r) ⊗ₜ[R] l := by
                rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
            _ = r ⊗ₜ[R] (s • l) := TensorProduct.smul_tmul _ _ _
            _ = _ := by
                rw [← hb, TensorProduct.tmul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
        | add z₁ z₂ h₁ h₂ =>
          obtain ⟨s₁, hs₁, c₁, e₁⟩ := h₁
          obtain ⟨s₂, hs₂, c₂, e₂⟩ := h₂
          refine ⟨s₁ * s₂, p.primeCompl.mul_mem hs₁ hs₂, fun i => f s₂ * c₁ i + f s₁ * c₂ i, ?_⟩
          have e₃ : f (s₁ * s₂) • (z₁ + z₂) = f s₂ • (f s₁ • z₁) + f s₁ • (f s₂ • z₂) := by
            rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm (f s₂)]
          rw [e₃, e₁, e₂]
          simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.add_tmul,
            Finset.sum_add_distrib]
      obtain ⟨s, hs, c, hc⟩ := span z
      have h0 : ∑ i, c i • ρ (w i) = 0 := by
        have := congrArg e₀ hc
        rw [map_smul, hz, smul_zero, map_sum] at this
        simpa [he₀] using this.symm
      have h1 : Fintype.linearCombination T (fun i => ρq (ρ (w i))) (fun i => gT (c i)) = 0 := by
        have := congrArg ρq h0
        rw [map_sum, map_zero] at this
        simpa [Fintype.linearCombination_apply] using this
      have h2 : ∀ i, gT (c i) = 0 := fun i => by
        have := hB.1 (h1.trans (map_zero _).symm)
        exact congrFun this i
      choose u hu using fun i => (IsLocalization.map_eq_zero_iff q.primeCompl T (c i)).1 (h2 i)
      refine ⟨(∏ i, (u i : R')) * f s, q.primeCompl.mul_mem (q.primeCompl.prod_mem fun i _ => (u i).2) hs, ?_⟩
      rw [mul_smul, hc, Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm, hu i, zero_mul, TensorProduct.zero_tmul]
    ·
      obtain ⟨c, hcy⟩ := hB.2 (ρq y)
      obtain ⟨⟨t, ht⟩, hta⟩ := IsLocalization.exist_integer_multiples q.primeCompl (Finset.univ : Finset (Fin n)) c
      choose a ha using fun i => hta i (Finset.mem_univ i)
      have hx0 : ρq (t • y - ∑ i, a i • ρ (w i)) = 0 := by
        rw [map_sub, map_smulₛₗ, map_sum, ← hcy, Fintype.linearCombination_apply, Finset.smul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_smulₛₗ, smul_smul, ha i, Algebra.smul_def, sub_self]
      haveI := hsm'
      obtain ⟨r, hr, hrx⟩ := exists_smul_eq_zero X'.rm q (t • y - ∑ i, a i • ρ (w i)) (by
        have e1 := hρq (t • y - ∑ i, a i • ρ (w i))
        have e0 := hρq 0
        rw [hx0] at e1
        rw [map_zero] at e0
        unfold IsVecOver at e1 e0
        exact e1.symm.trans e0)
      refine ⟨r * t, q.primeCompl.mul_mem hr ht, ∑ i, (r * a i) ⊗ₜ w i, ?_⟩
      rw [smul_sub, sub_eq_zero, Finset.smul_sum] at hrx
      rw [map_sum]
      simp only [he₀]
      rw [mul_smul, hrx]
      simp only [smul_smul]
  refine ⟨LinearEquiv.ofBijective e₀ ⟨?_, ?_⟩, fun v v' => (corr v v').trans ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact eq_zero_of_loc fun q _ => (loc q).1 z hz
  · intro y
    have : Submodule.Quotient.mk (p := LinearMap.range e₀) y = 0 := eq_zero_of_loc fun q _ => by
      obtain ⟨u, hu, hm⟩ := (loc q).2 y
      exact ⟨u, hu, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hm⟩
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · show v' = ρ v ↔ v' = e₀ (1 ⊗ₜ v)
    rw [he₀, one_smul]
end GlobalTheory.RealMult.Obj
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_base_change_iso : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap (algebraMap R R')) φ →
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, ∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v) := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.lieBaseChange_equiv
end
