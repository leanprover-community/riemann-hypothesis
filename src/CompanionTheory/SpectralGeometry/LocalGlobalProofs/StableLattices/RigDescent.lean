import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnits
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExists

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigCover

theorem exists_gen_of_chart {Y P : Scheme.{0}} {M : LB P} (hM : M.IsLB) (f : Y ⟶ P) (i : M.ι)
    (hf : ∀ y, f y ∈ M.U i) : ∃ t : LB.Gen (M.pull f), t.IsGen := by
  have le : ∀ J : PUnit → M.ι, LB.wchart M (K := PUnit) (fun _ => f) J ≤ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (M.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have hJ : f y ∈ M.U (J PUnit.unit) := mem_pull.1 hy.1
  have hJ' : f y ∈ M.U (J' PUnit.unit) := mem_pull.1 hy.2
  have key : ∀ (K : PUnit → M.ι) (h : f y ∈ M.U (K PUnit.unit)) (hk : y ∈ LB.wchart M (K := PUnit) (fun _ => f) K),
      gm (𝟙 Y) y _ (res (le K) (pullU f _ (M.g (K PUnit.unit) i))) =
        gm (𝟙 Y ≫ f) y _ (M.g (K PUnit.unit) i) := fun K h hk =>
    (gm_res _ y (le K) hk _).trans (gm_pull (𝟙 Y) f y (M.U (K PUnit.unit) ⊓ M.U i) (show f y ∈ _ from ⟨h, hf y⟩) _)
  have e : gm (𝟙 Y) y _ ((M.pull f).g J J') = gm (𝟙 Y ≫ f) y _ (M.g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (M.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ y _ hy _).trans (gm_pull (𝟙 Y) f y (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit)) (show f y ∈ _ from ⟨hJ, hJ'⟩) _)
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
  exact (key J hJ hy.1).trans ((gm_cocycle hM (𝟙 Y ≫ f) y hJ hJ' (hf y)).symm.trans
    (congrArg₂ (· * ·) e.symm (key J' hJ' hy.2).symm))

theorem exists_flat_cover_triv : ∀ {P : Scheme.{0}} (M : LB P), M.IsLB → ∃ (Z : Scheme.{0}) (g : Z ⟶ P),
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧ Triv (M.pull g) := by
  intro P M hM
  let D : M.ι → Scheme.{0} := fun i => (M.U i).toScheme
  let g : ∐ D ⟶ P := Sigma.desc fun i => (M.U i).ι
  have hι : ∀ i, Sigma.ι D i ≫ g = (M.U i).ι := fun i => Sigma.ι_desc _ i
  refine ⟨∐ D, g, ?_, ?_, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    have hf : ∀ i : M.ι, Flat (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover D) hf
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    have hf : ∀ i : M.ι, LocallyOfFinitePresentation (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover D) hf
  · refine ⟨fun x => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart hM x
    let x' : D i := ⟨x, hi⟩
    refine ⟨Sigma.ι D i x', ?_⟩
    have e : (Sigma.ι D i ≫ g) x' = x := by rw [hι]; rfl
    exact e
  · let W : M.ι → (∐ D).Opens := fun i => (Sigma.ι D i).opensRange
    have hW : ∀ y, ∃ s, y ∈ W s := fun y => by
      obtain ⟨i, x, rfl⟩ := (sigmaOpenCover D).exists_eq y
      exact ⟨i, x, rfl⟩
    have hg : ∀ s, ∃ t : LB.Gen (M.pull ((W s).ι ≫ g)), t.IsGen := fun s => by
      refine exists_gen_of_chart hM _ s fun y => ?_
      obtain ⟨x, hx⟩ : ((W s).ι y) ∈ Set.range (Sigma.ι D s) := y.2
      have : ((W s).ι ≫ g) y = (M.U s).ι x := by
        rw [← hι s, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
      rw [this]
      exact x.2
    choose t ht using hg
    obtain ⟨u, hu, -⟩ := glue_gen hM (K := PUnit) (fun _ => g) (fun _ => 1) W hW t ht
      (fun s s' Z r r' z J _ hr => by
        by_cases e : s = s'
        · subst e
          have : r = r' := (cancel_mono (W s).ι).1 hr
          rw [this]
        · exfalso
          have mem : ∀ (a : M.ι) (q : Z ⟶ (W a).toScheme), (q ≫ (W a).ι) z ∈ W a := fun a q => (q z).2
          have m₁ := mem s r
          have m₂ : (r ≫ (W s).ι) z ∈ W s' := hr ▸ mem s' r'
          have d : W s ⊓ W s' = ⊥ := disjoint_iff.1 (disjoint_opensRange_sigmaι D s s' e)
          have hx : (r ≫ (W s).ι) z ∈ W s ⊓ W s' := ⟨m₁, m₂⟩
          rw [d] at hx
          exact hx)
    exact ⟨u, hu⟩

end GlobalTheory.CompanionTheory.RigCover
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_trivial_after_flat_cover : ∀ {P : Scheme.{0}} (M : LB P), M.IsLB → ∃ (Z : Scheme.{0}) (g : Z ⟶ P),
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧ Triv (M.pull g) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RigCover.exists_flat_cover_triv
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem exists_unit_of_gen : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P), M.IsLB →
    ∀ (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])), c.IsGen →
    ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∃ (u : Γ(pullback (g ≫ f) (g ≫ f), ⊤)) (hu : IsUnit u),
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (w : W) (J : (W ⟶ P) → M.ι), Good M w J →
        gm (pullback.lift a b hab) w ⊤ hu.unit =
          val τ a w J * val c (pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab)) w J * (val τ b w J)⁻¹ := by
  intro Z P Q g f M hM c hc τ hτ
  have hm : (pullback.fst (g ≫ f) (g ≫ f) ≫ g) ≫ f = (pullback.snd (g ≫ f) (g ≫ f) ≫ g) ≫ f := by
    simpa using pullback.condition (f := g ≫ f) (g := g ≫ f)
  let m : pullback (g ≫ f) (g ≫ f) ⟶ pullback f f := pullback.lift _ _ hm
  have m₁ : m ≫ pullback.fst f f = pullback.fst (g ≫ f) (g ≫ f) ≫ g := pullback.lift_fst _ _ hm
  have m₂ : m ≫ pullback.snd f f = pullback.snd (g ≫ f) (g ≫ f) ≫ g := pullback.lift_snd _ _ hm
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, m₁, m₂]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ (LB.pullGen M _ _ τ (pullback.fst (g ≫ f) (g ≫ f))) (LB.pullGen M _ _ c m))
      (LB.invGen M _ _ (LB.pullGen M _ _ τ (pullback.snd (g ≫ f) (g ≫ f)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) (DVR.pullGen_isGen _ _ _ _ hc _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have le : (⊤ : (pullback (g ≫ f) (g ≫ f)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (pullback (g ≫ f) (g ≫ f) ⟶ P)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, Units.isUnit _, fun W a b hab w J hJ => ?_⟩
  have e₁ : pullback.lift a b hab ≫ pullback.fst (g ≫ f) (g ≫ f) = a := pullback.lift_fst _ _ _
  have e₂ : pullback.lift a b hab ≫ pullback.snd (g ≫ f) (g ≫ f) = b := pullback.lift_snd _ _ _
  have e₃ : pullback.lift a b hab ≫ m = pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab) := by
    apply pullback.hom_ext
    · rw [Category.assoc, m₁, ← Category.assoc, e₁, pullback.lift_fst]
    · rw [Category.assoc, m₂, ← Category.assoc, e₂, pullback.lift_snd]
  rw [IsUnit.unit_of_val_units]
  refine ((gm_res _ w le trivial _).trans (val_of t _ w J PEmpty.elim (fun k => k.elim)).symm).trans ?_
  rw [hv W _ w J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, e₁, e₂, e₃]

end GlobalTheory.CompanionTheory.RigDesc
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_descent_unit_exists : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P), M.IsLB →
    ∀ (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])), c.IsGen →
    ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∃ (u : Γ(pullback (g ≫ f) (g ≫ f), ⊤)) (hu : IsUnit u),
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (w : W) (J : (W ⟶ P) → M.ι), Good M w J →
        gm (pullback.lift a b hab) w ⊤ hu.unit =
          val τ a w J * val c (pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab)) w J * (val τ b w J)⁻¹ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RigDesc.exists_unit_of_gen
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.LbCocycle

theorem gm_comp_val {W' W X : Scheme.{0}} (p : W' ⟶ W) (y : W') (f : W ⟶ X) (V : X.Opens)
    (hy : f (p y) ∈ V) (x : Γ(X, V)ˣ) :
    (gm (p ≫ f) y V x).val = (p.stalkMap y).hom (gm f (p y) V x).val := by
  rw [gm_val (p ≫ f) y V hy, gm_val f (p y) V hy, Scheme.Hom.comp_app]
  exact (Scheme.Hom.germ_stalkMap_apply p (f ⁻¹ᵁ V) y hy _).symm

theorem gm_top_val {W' X : Scheme.{0}} (V : X.Opens) (g : W' ⟶ V.toScheme) (w : W') (τ : Γ(X, V)ˣ) :
    (gm (g ≫ V.ι) w V τ).val =
      (W'.presheaf.germ ⊤ w trivial).hom (g.appTop.hom ((GlobalTheory.FunDescent.res V).hom τ.val)) := by
  have hm : (g ≫ V.ι) w ∈ V := (g w).2
  have hl : ⊤ ≤ (g ≫ V.ι) ⁻¹ᵁ V := fun x _ => (g x).2
  have e := congrArg (fun ψ => ψ.hom τ.val) (GlobalTheory.FunDescent.res_comp_appTop V g (g ≫ V.ι) rfl hl)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [gm_val _ w V hm, e, Scheme.Hom.appLE]
  exact (TopCat.Presheaf.germ_res_apply W'.presheaf (homOfLE hl) w trivial _).symm

theorem gm_global_val {W' X : Scheme.{0}} (k : W' ⟶ X) (w : W') (u : Γ(X, ⊤)ˣ) :
    (gm k w ⊤ u).val = (W'.presheaf.germ ⊤ w trivial).hom (k.appTop.hom u.val) :=
  gm_val k w ⊤ trivial u

theorem exists_local_unit (H : H90) {Z Q : Scheme.{0}} (h : Z ⟶ Q) (hf : Flat h)
    (hl : LocallyOfFinitePresentation h) (hs : Surjective h) (u : Γ(pullback h h, ⊤)) (hu : IsUnit u)
    (hc : ∀ (W : Scheme.{0}) (a b c : W ⟶ Z) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) (y : Q) :
    ∃ U : Q.Opens, y ∈ U ∧ ∃ τ : Γ(Z, h ⁻¹ᵁ U)ˣ,
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ h = b ≫ h) (w : W), h (a w) ∈ U →
        gm a w (h ⁻¹ᵁ U) τ = gm (pullback.lift a b hab) w ⊤ hu.unit * gm b w (h ⁻¹ᵁ U) τ := by
  obtain ⟨U, hy, t, ht, F⟩ := H Z Q h hf hl hs u hu hc y
  refine ⟨U, hy, ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := (GlobalTheory.FunDescent.res_bijective (h ⁻¹ᵁ U)).2 t
  obtain ⟨σ₀, hσ₀⟩ := (GlobalTheory.FunDescent.res_bijective (h ⁻¹ᵁ U)).2 (ht.unit⁻¹).val
  have e₁ : τ₀ * σ₀ = 1 := (GlobalTheory.FunDescent.res_bijective (h ⁻¹ᵁ U)).1 (by
    rw [map_mul, map_one, hτ₀, hσ₀]
    exact ht.unit.mul_inv)
  let τ : Γ(Z, h ⁻¹ᵁ U)ˣ := ⟨τ₀, σ₀, e₁, (mul_comm _ _).trans e₁⟩
  refine ⟨τ, fun W a b hab w hw => ?_⟩
  let O : W.Opens := a ⁻¹ᵁ (h ⁻¹ᵁ U)
  have hO : ∀ x : O.toScheme, h (b (O.ι x)) ∈ U := fun x => by
    have : h (a (O.ι x)) ∈ U := x.2
    have e : h (a (O.ι x)) = h (b (O.ι x)) := congrArg (fun m : W ⟶ Q => m (O.ι x)) hab
    rwa [e] at this
  have lft : ∀ c : W ⟶ Z, (∀ x : O.toScheme, h (c (O.ι x)) ∈ U) →
      ∃ c' : O.toScheme ⟶ (h ⁻¹ᵁ U).toScheme, c' ≫ (h ⁻¹ᵁ U).ι = O.ι ≫ c := fun c hc' =>
    ⟨IsOpenImmersion.lift _ (O.ι ≫ c) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hc' q), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨a', ha'⟩ := lft a fun x => x.2
  obtain ⟨b', hb'⟩ := lft b hO
  have hab' : (a' ≫ (h ⁻¹ᵁ U).ι) ≫ h = (b' ≫ (h ⁻¹ᵁ U).ι) ≫ h := by
    rw [ha', hb', Category.assoc, Category.assoc, hab]
  have hk : pullback.lift (a' ≫ (h ⁻¹ᵁ U).ι) (b' ≫ (h ⁻¹ᵁ U).ι) hab' = O.ι ≫ pullback.lift a b hab := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ha']
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hb']
  have E := F O.toScheme a' b' hab'
  rw [hk] at E
  obtain ⟨w', rfl⟩ : ∃ w' : O.toScheme, O.ι w' = w := ⟨⟨w, hw⟩, rfl⟩
  have hτ : (GlobalTheory.FunDescent.res (h ⁻¹ᵁ U)).hom τ.val = t := hτ₀
  have inj : Function.Injective (O.ι.stalkMap w').hom :=
    (ConcreteCategory.bijective_of_isIso (O.ι.stalkMap w')).1
  have A : (O.ι.stalkMap w').hom (gm a (O.ι w') (h ⁻¹ᵁ U) τ).val =
      (O.toScheme.presheaf.germ ⊤ w' trivial).hom (a'.appTop.hom t) := by
    rw [← gm_comp_val O.ι w' a _ hw τ, ← ha', gm_top_val, hτ]
  have B : (O.ι.stalkMap w').hom (gm b (O.ι w') (h ⁻¹ᵁ U) τ).val =
      (O.toScheme.presheaf.germ ⊤ w' trivial).hom (b'.appTop.hom t) := by
    rw [← gm_comp_val O.ι w' b _ (hO w') τ, ← hb', gm_top_val, hτ]
  have C : (O.ι.stalkMap w').hom (gm (pullback.lift a b hab) (O.ι w') ⊤ hu.unit).val =
      (O.toScheme.presheaf.germ ⊤ w' trivial).hom ((O.ι ≫ pullback.lift a b hab).appTop.hom u) := by
    rw [← gm_comp_val O.ι w' (pullback.lift a b hab) ⊤ trivial hu.unit, gm_global_val]
    rfl
  apply Units.ext
  apply inj
  rw [Units.val_mul, map_mul, A, B, C, E, map_mul]

def lbOf {Q : Scheme.{0}} (U : Q → Q.Opens) (g : ∀ y y', Γ(Q, U y ⊓ U y')ˣ) : LB Q := ⟨Q, U, g⟩

theorem exists_lb : H90 → ∀ {Z Q : Scheme.{0}} (h : Z ⟶ Q), Flat h → LocallyOfFinitePresentation h → Surjective h →
    ∀ (u : Γ(pullback h h, ⊤)) (hu : IsUnit u),
    (∀ (W : Scheme.{0}) (a b c : W ⟶ Z) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) →
    ∃ N : LB Q, N.IsLB ∧ ∃ T : LB.Gen (N.pull h), T.IsGen ∧
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ h = b ≫ h) (w : W) (i : N.ι), h (a w) ∈ N.U i →
        gm a w ((N.pull h).U fun _ => i) (T.s fun _ => i) =
          gm (pullback.lift a b hab) w ⊤ hu.unit * gm b w ((N.pull h).U fun _ => i) (T.s fun _ => i) := by
  intro H Z Q h hf hl hs u hu hc
  choose U hU τ hτ using fun y => exists_local_unit H h hf hl hs u hu hc y
  have D := fun V => GlobalTheory.T.flat_descent_of_units h hf hl hs V
  have l₁ : ∀ y y' : Q, h ⁻¹ᵁ (U y ⊓ U y') ≤ h ⁻¹ᵁ U y := fun _ _ _ hx => hx.1
  have l₂ : ∀ y y' : Q, h ⁻¹ᵁ (U y ⊓ U y') ≤ h ⁻¹ᵁ U y' := fun _ _ _ hx => hx.2
  have ex : ∀ y y' : Q, ∃ s : Γ(Q, U y ⊓ U y')ˣ,
      pullU h _ s = res (l₁ y y') (τ y) * (res (l₂ y y') (τ y'))⁻¹ := fun y y' =>
    (D _).2 _ fun W b c e w hw => by
      have e' : h (b w) = h (c w) := congrArg (fun m : W ⟶ Q => m w) e
      have hc₁ : c w ∈ h ⁻¹ᵁ U y := show h (c w) ∈ U y from e' ▸ hw.1
      have hc₂ : c w ∈ h ⁻¹ᵁ U y' := show h (c w) ∈ U y' from e' ▸ hw.2
      have hw' : c w ∈ h ⁻¹ᵁ (U y ⊓ U y') := ⟨hc₁, hc₂⟩
      rw [map_mul, map_mul, map_inv, map_inv, gm_res b w _ hw, gm_res b w _ hw, gm_res c w _ hw',
        gm_res c w _ hw', hτ y W b c e w hw.1, hτ y' W b c e w hw.2, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul]
  choose g hg using ex
  have ext : ∀ (V : Q.Opens) (a b : Γ(Q, V)ˣ), (∀ z : Z, h z ∈ V → gm h z V a = gm h z V b) → a = b :=
    fun V a b e => (D V).1 (unit_ext fun z hz => by
      have k : ∀ c : Γ(Q, V)ˣ, gm (𝟙 Z) z (h ⁻¹ᵁ V) (pullU h V c) = gm h z V c := fun c =>
        (gm_pull (𝟙 Z) h z V hz c).trans (by rw [Category.id_comp])
      rw [k, k]
      exact e z hz)
  have K : ∀ (W : Scheme.{0}) (f : W ⟶ Z) (w : W) (y y' : Q) (_ : h (f w) ∈ U y ⊓ U y'),
      gm (f ≫ h) w _ (g y y') = gm f w _ (τ y) * (gm f w _ (τ y'))⁻¹ := fun W f w y y' hm => by
    have hm' : f w ∈ h ⁻¹ᵁ (U y ⊓ U y') := hm
    rw [← gm_pull f h w _ hm, hg, map_mul, map_inv, gm_res f w _ hm', gm_res f w _ hm']
  have K₁ : ∀ (z : Z) (y y' : Q) (_ : h z ∈ U y ⊓ U y'),
      gm h z _ (g y y') = gm (𝟙 Z) z _ (τ y) * (gm (𝟙 Z) z _ (τ y'))⁻¹ := fun z y y' hm => by
    have := K Z (𝟙 Z) z y y' hm
    rwa [Category.id_comp] at this
  have isLB : (lbOf U g).IsLB :=
    { cover := eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hU y⟩
      g_self := fun y => ext _ _ _ fun z hz => by
        have hm : h z ∈ U y ⊓ U y := ⟨hz, hz⟩
        refine (gm_res h z _ hz _).trans ?_
        refine (K₁ z y y hm).trans ?_
        rw [map_one, mul_inv_cancel]
      cocycle := fun i j k => ext _ _ _ fun z hz => by
        have h₁ : h z ∈ U i ⊓ U j := hz.1
        have h₂ : h z ∈ U j ⊓ U k := ⟨hz.1.2, hz.2⟩
        have h₃ : h z ∈ U i ⊓ U k := ⟨hz.1.1, hz.2⟩
        refine (map_mul _ _ _).trans ?_
        refine (congrArg₂ (· * ·) ((gm_res h z _ hz _).trans (K₁ z i j h₁))
          ((gm_res h z _ hz _).trans (K₁ z j k h₂))).trans ?_
        refine Eq.trans ?_ ((gm_res h z _ hz _).trans (K₁ z i k h₃)).symm
        rw [_root_.mul_assoc, inv_mul_cancel_left] }
  have hle : ∀ J : PUnit → Q, ((lbOf U g).pull h).U J ≤ h ⁻¹ᵁ U (J PUnit.unit) :=
    fun J x hx => mem_pull.1 hx
  let T : LB.Gen ((lbOf U g).pull h) := ⟨fun J => res (hle J) (τ (J PUnit.unit))⟩
  have hT : ∀ (W : Scheme.{0}) (f : W ⟶ Z) (w : W) (J : PUnit → Q), f w ∈ ((lbOf U g).pull h).U J →
      gm f w _ (T.s J) = gm f w _ (τ (J PUnit.unit)) := fun W f w J hm => gm_res f w (hle J) hm _
  refine ⟨lbOf U g, isLB, T, ?_, ?_⟩
  · intro J J'
    apply unit_ext
    intro z hz
    have hm : h z ∈ U (J PUnit.unit) ⊓ U (J' PUnit.unit) := ⟨hle J hz.1, hle J' hz.2⟩
    refine (gm_res _ z _ hz _).trans ((hT Z (𝟙 Z) z J hz.1).trans ?_)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl (gm_res _ z _ hz _).symm)
    rw [hT Z (𝟙 Z) z J' hz.2]
    have := gm_pull_g (lbOf U g) h (𝟙 Z) z J J' hz.1 hz.2
    refine Eq.trans ?_ (congrArg₂ (· * ·) (this.trans (K Z (𝟙 Z) z _ _ hm)).symm rfl)
    rw [inv_mul_cancel_right]
  · intro W a b hab w i hi
    have e' : h (a w) = h (b w) := congrArg (fun m : W ⟶ Q => m w) hab
    have hb : h (b w) ∈ (lbOf U g).U i := e' ▸ hi
    rw [hT W a w _ (mem_pull.2 hi), hT W b w _ (mem_pull.2 hb)]
    exact hτ i W a b hab w hi

end GlobalTheory.CompanionTheory.LbCocycle
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_defines_descended_line_bundle : H90 → ∀ {Z Q : Scheme.{0}} (h : Z ⟶ Q), Flat h → LocallyOfFinitePresentation h → Surjective h →
    ∀ (u : Γ(pullback h h, ⊤)) (hu : IsUnit u),
    (∀ (W : Scheme.{0}) (a b c : W ⟶ Z) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) →
    ∃ N : LB Q, N.IsLB ∧ ∃ T : LB.Gen (N.pull h), T.IsGen ∧
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ h = b ≫ h) (w : W) (i : N.ι), h (a w) ∈ N.U i →
        gm a w ((N.pull h).U fun _ => i) (T.s fun _ => i) =
          gm (pullback.lift a b hab) w ⊤ hu.unit * gm b w ((N.pull h).U fun _ => i) (T.s fun _ => i) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LbCocycle.exists_lb
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigGlue

theorem gm_gen_pull {Y X : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {t : LB.Gen (L.pull F)} (ht : t.IsGen) (x : Y)
    (i i' : L.ι) (hi : F x ∈ L.U i) (hi' : F x ∈ L.U i') :
    gm (𝟙 Y) x ((L.pull F).U fun _ => i) (t.s fun _ => i) =
      gm (𝟙 Y ≫ F) x _ (L.g i i') * gm (𝟙 Y) x ((L.pull F).U fun _ => i') (t.s fun _ => i') := by
  have m₁ : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i) := mem_pull.2 hi
  have m₂ : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i') := mem_pull.2 hi'
  have hm : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨m₁, m₂⟩
  have e := congrArg (gm (𝟙 Y) x _) (ht (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res (𝟙 Y) x _ hm, gm_res (𝟙 Y) x _ hm, gm_pull_g L F (𝟙 Y) x _ _ m₁ m₂] at e
  exact e

theorem gm_pull_div_g {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P) (N : LB Q) (x : Z) (i i' : N.ι) (k k' : M.ι)
    (hi : f (g x) ∈ N.U i) (hi' : f (g x) ∈ N.U i') (hk : g x ∈ M.U k) (hk' : g x ∈ M.U k') :
    gm (𝟙 Z) x (((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i, k)) ⊓
        ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i', k')))
      (((LB.div (N.pull f) M).pull g).g (fun _ => (fun _ => i, k)) (fun _ => (fun _ => i', k'))) =
      gm (𝟙 Z ≫ g ≫ f) x _ (N.g i i') * (gm (𝟙 Z ≫ g) x _ (M.g k k'))⁻¹ := by
  have m₁ : (𝟙 Z : Z ⟶ Z) x ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i, k)) :=
    mem_pull.2 ⟨mem_pull.2 hi, hk⟩
  have m₂ : (𝟙 Z : Z ⟶ Z) x ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i', k')) :=
    mem_pull.2 ⟨mem_pull.2 hi', hk'⟩
  refine (gm_pull_g (LB.div (N.pull f) M) g (𝟙 Z) x _ _ m₁ m₂).trans ?_
  refine (gm_div_g (L := N) (F := f) (L' := M) (𝟙 Z ≫ g) x i i' k k' hi hi' hk hk').trans ?_
  rw [Category.assoc]

theorem lbIso_of_same_descent : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q), Flat g → LocallyOfFinitePresentation g → Surjective g →
    ∀ (M : LB P), M.IsLB → ∀ (N : LB Q), N.IsLB → ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∀ (T : LB.Gen (N.pull (g ≫ f))), T.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ Z), a ≫ g = b ≫ g → ∀ (w : W) (i : N.ι) (k : M.ι), f (g (a w)) ∈ N.U i → g (a w) ∈ M.U k →
        gm a w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹ =
          gm b w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹) →
      LBIso M (N.pull f) := by
  intro Z P Q g f hfl hlf hsu M hM N hN τ hτ T hT hinv
  have hD : (LB.div (N.pull f) M).IsLB := LB.isLB_div (pull_isLB hN f) hM
  have mem₁ : ∀ (J : PUnit → (LB.div (N.pull f) M).ι) (x : Z), x ∈ ((LB.div (N.pull f) M).pull g).U J →
      f (g x) ∈ N.U ((J PUnit.unit).1 PUnit.unit) := fun J x hx => mem_pull.1 (mem_pull.1 hx).1
  have mem₂ : ∀ (J : PUnit → (LB.div (N.pull f) M).ι) (x : Z), x ∈ ((LB.div (N.pull f) M).pull g).U J →
      g x ∈ M.U (J PUnit.unit).2 := fun J x hx => (mem_pull.1 hx).2
  have le₁ : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ((LB.div (N.pull f) M).pull g).U J ≤
      (N.pull (g ≫ f)).U (fun _ => (J PUnit.unit).1 PUnit.unit) := fun J x hx => mem_pull.2 (mem₁ J x hx)
  have le₂ : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ((LB.div (N.pull f) M).pull g).U J ≤
      (M.pull g).U (fun _ => (J PUnit.unit).2) := fun J x hx => mem_pull.2 (mem₂ J x hx)
  let ω : LB.Gen ((LB.div (N.pull f) M).pull g) :=
    ⟨fun J => res (le₁ J) (T.s _) * (res (le₂ J) (τ.s _))⁻¹⟩
  have germ : ∀ (W : Scheme.{0}) (a : W ⟶ Z) (w : W) (J : PUnit → (LB.div (N.pull f) M).ι)
      (h : a w ∈ ((LB.div (N.pull f) M).pull g).U J),
      gm a w _ (ω.s J) = gm a w ((N.pull (g ≫ f)).U fun _ => (J PUnit.unit).1 PUnit.unit) (T.s _) *
        (gm a w ((M.pull g).U fun _ => (J PUnit.unit).2) (τ.s _))⁻¹ := by
    intro W a w J h
    show gm a w _ (res (le₁ J) (T.s _) * (res (le₂ J) (τ.s _))⁻¹) = _
    rw [map_mul, map_inv, gm_res a w _ h, gm_res a w _ h]
  have hω : ω.IsGen := by
    have split : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ∃ (i : N.ι) (k : M.ι), J = fun _ => (fun _ => i, k) :=
      fun J => ⟨(J PUnit.unit).1 PUnit.unit, (J PUnit.unit).2, rfl⟩
    intro J J'
    obtain ⟨i, k, rfl⟩ := split J
    obtain ⟨i', k', rfl⟩ := split J'
    apply unit_ext
    intro x hx
    have h₁ := hx.1
    have h₂ := hx.2
    have i₁ : f (g x) ∈ N.U i := mem₁ _ x h₁
    have i₂ : f (g x) ∈ N.U i' := mem₁ _ x h₂
    have k₁ : g x ∈ M.U k := mem₂ _ x h₁
    have k₂ : g x ∈ M.U k' := mem₂ _ x h₂
    have eT := gm_gen_pull hT x i i' i₁ i₂
    have eτ := gm_gen_pull hτ x k k' k₁ k₂
    refine (gm_res (𝟙 Z) x _ hx _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) (gm_pull_div_g g f M N x i i' k k' i₁ i₂ k₁ k₂).symm
      (gm_res (𝟙 Z) x _ hx _).symm)
    refine (germ _ (𝟙 Z) x _ h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (germ _ (𝟙 Z) x _ h₂).symm))
    show gm (𝟙 Z) x _ (T.s fun _ => i) * (gm (𝟙 Z) x _ (τ.s fun _ => k))⁻¹ =
      _ * (gm (𝟙 Z) x _ (T.s fun _ => i') * (gm (𝟙 Z) x _ (τ.s fun _ => k'))⁻¹)
    rw [eT, eτ, mul_inv, _root_.mul_mul_mul_comm]
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator g hfl hlf hsu _ hD ω hω ?_
  intro W a b hab w i hi
  have hpt : g (a w) = g (b w) := by
    have := congrArg (fun q : W ⟶ P => q w) hab
    simpa using this
  have ha : a w ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => i) := mem_pull.2 hi
  have hb : b w ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => i) := mem_pull.2 (hpt ▸ hi)
  rw [germ W a w _ ha, germ W b w _ hb]
  exact hinv W a b hab w _ _ (mem₁ _ _ ha) (mem₂ _ _ ha)

end GlobalTheory.CompanionTheory.RigGlue
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_pull_of_generator_ratio_eq : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q), Flat g → LocallyOfFinitePresentation g → Surjective g →
    ∀ (M : LB P), M.IsLB → ∀ (N : LB Q), N.IsLB → ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∀ (T : LB.Gen (N.pull (g ≫ f))), T.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ Z), a ≫ g = b ≫ g → ∀ (w : W) (i : N.ι) (k : M.ι), f (g (a w)) ∈ N.U i → g (a w) ∈ M.U k →
        gm a w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹ =
          gm b w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹) →
      LBIso M (N.pull f) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RigGlue.lbIso_of_same_descent
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem isPullback_snd_lift_fst_snd_comp {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (snd A X).left (lift (fst A X) (snd A X ≫ q)).left q.left (snd A Y).left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact (IsPullback.of_right hout e₂ hY).flip

theorem lift_fst_snd_comp_flat_lfp_surjective :
    ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  intro S A X Y _ _ q hf hl hs
  have h := isPullback_snd_lift_fst_snd_comp A X Y q
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hl,
    MorphismProperty.of_isPullback (P := @Surjective) h hs⟩

end GlobalTheory.CompanionTheory.RigDesc
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_cover_base_change_product : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RigDesc.lift_fst_snd_comp_flat_lfp_surjective
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

variable {S : Scheme.{0}} {A X Y : Over S} [GrpObj A]

theorem val_lift_eq_of_comp_eq (hA : IsAbelianScheme A) (q : X ⟶ Y) {N : LB (A ⊗ Y).left} (hN : N.IsLB)
    (r : LB.Gen (ev N (1 : Y ⟶ A) (𝟙 Y)))
    (t : LB.Gen (ev N (fst A X) (snd A X ≫ q))) (ht : t.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (s : Z ⟶ X.left) (z : Z) (J : (Z ⟶ (A ⊗ Y).left) → N.ι), Good N z J →
      val t (s ≫ (lift (1 : X ⟶ A) (𝟙 X)).left) z J = val r (s ≫ q.left) z J)
    {T : Over S} (α : T ⟶ A) (x x' : T ⟶ X) (h : x ≫ q = x' ≫ q)
    (z : T.left) (J : (T.left ⟶ (A ⊗ Y).left) → N.ι) (hJ : Good N z J) :
    val t (lift α x).left z J = val t (lift α x').left z J := by
  have hc : ∀ x₁ : T ⟶ X, lift (fst A T) (snd A T ≫ x₁) ≫ lift (fst A X) (snd A X ≫ q) =
      lift (fst A T) (snd A T ≫ x₁ ≫ q) := fun x₁ => by
    ext <;> simp
  have hc' : (lift (fst A T) (snd A T ≫ x)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      (lift (fst A T) (snd A T ≫ x')).left ≫ (lift (fst A X) (snd A X ≫ q)).left := by
    rw [← Over.comp_left, ← Over.comp_left, hc, hc, h]
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hs : ∀ x₁ : T ⟶ X, (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left =
      x₁.left ≫ (lift (1 : X ⟶ A) (𝟙 X)).left := fun x₁ => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hv : ∀ x₁ : T ⟶ X, ∀ (y : T.left) (I : (T.left ⟶ (A ⊗ Y).left) → N.ι), Good N y I →
      val (LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x₁)).left) (lift (1 : T ⟶ A) (𝟙 T)).left y I =
        val r (x₁ ≫ q).left y I := fun x₁ y I hI => by
    rw [val_pull hI, hs, hn _ _ _ _ hI, Over.comp_left]
  have key := gen_unique' hN (u := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x)).left)
    (u' := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x')).left)
    (fun U _ k => by simp only [hc']) (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (surj_snd GlobalTheory.globalFns_holds hA T)
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _)
    (fun y I hI => by rw [hv x y I hI, hv x' y I hI, h]) T.left (lift α (𝟙 T)).left z J hJ
  have hl : ∀ x₁ : T ⟶ X, (lift α (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left = (lift α x₁).left := fun x₁ => by
    rw [← Over.comp_left]
    congr 1
    ext <;> simp
  rw [val_pull hJ, val_pull hJ, hl, hl] at key
  exact key

end GlobalTheory.CompanionTheory.RigDesc

namespace GlobalTheory.CompanionTheory.RigDesc

theorem triv_of_triv_of_flat_cover : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N := by
  rintro S A X Y _ hA q hfl hlfp hsj N hN ⟨r, hr⟩ ⟨t₀, ht₀⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hfl hlfp hsj
  have he : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (snd A X).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hef : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  obtain ⟨t, ht, hn⟩ := GlobalTheory.T.linear_combination_generator_section_exists hN (fun _ => (lift (fst A X) (snd A X ≫ q)).left) (fun _ => 1)
    (fun _ => q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left) (fun _ => 1) (snd A X).left (lift (1 : X ⟶ A) (𝟙 X)).left he
    (fun U _ k => by simp only [hef]) t₀ ht₀ (LB.pullGen N _ _ r q.left) (DVR.pullGen_isGen _ _ _ _ hr _)
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator _ f₁ f₂ f₃ N hN t ht fun W a b hab w i hi => ?_
  have hw : a ≫ (A ⊗ X).hom = b ≫ (A ⊗ X).hom := by
    have e := congrArg (· ≫ (A ⊗ Y).hom) hab
    simpa only [Category.assoc, Over.w] using e
  let T : Over S := Over.mk (a ≫ (A ⊗ X).hom)
  let a' : T ⟶ A ⊗ X := Over.homMk a rfl
  let b' : T ⟶ A ⊗ X := Over.homMk b hw.symm
  have hab' : a' ≫ lift (fst A X) (snd A X ≫ q) = b' ≫ lift (fst A X) (snd A X ≫ q) := by
    exact Over.OverMorphism.ext hab
  have h₁ : a' ≫ fst A X = b' ≫ fst A X := by
    have e := congrArg (· ≫ fst A Y) hab'
    simpa using e
  have h₂ : (a' ≫ snd A X) ≫ q = (b' ≫ snd A X) ≫ q := by
    have e := congrArg (· ≫ snd A Y) hab'
    simpa using e
  obtain ⟨J, hJ, hJi⟩ := exists_good N hN w (K := PUnit.{1}) (fun _ => a ≫ (lift (fst A X) (snd A X ≫ q)).left)
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have hJi' : J (a ≫ (lift (fst A X) (snd A X ≫ q)).left) = i := hJi PUnit.unit
  have key := val_lift_eq_of_comp_eq hA q hN r t ht (fun Z s z I hI => (hn Z s z I hI).trans (val_pull hI _ _ _))
    (a' ≫ fst A X) (a' ≫ snd A X) (b' ≫ snd A X) h₂ w J hJ
  have ea : (lift (a' ≫ fst A X) (a' ≫ snd A X)).left = a := by
    rw [← comp_lift, lift_fst_snd]; simp [a']
  have eb : (lift (a' ≫ fst A X) (b' ≫ snd A X)).left = b := by
    rw [h₁, ← comp_lift, lift_fst_snd]; simp [b']
  rw [ea, eb, val_of t a w J (fun _ => i) (fun _ => hJi'), val_of t b w J (fun _ => i) (fun _ => by rw [← hab]; exact hJi')] at key
  exact key

end GlobalTheory.CompanionTheory.RigDesc
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_triviality_abelian_scheme : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RigDesc.triv_of_triv_of_flat_cover
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.RigDescLink

variable {S : Scheme.{0}} {A X : Over S}

abbrev aH (A : Over S) {T X : Over S} (x : T ⟶ X) : A ⊗ T ⟶ A ⊗ X := lift (fst A T) (snd A T ≫ x)

abbrev zS (A : Over S) [GrpObj A] (T : Over S) : T ⟶ A ⊗ T := lift (1 : T ⟶ A) (𝟙 T)

theorem aH_comp {T T' : Over S} (v : T' ⟶ T) (x : T ⟶ X) : aH A v ≫ aH A x = aH A (v ≫ x) := by
  simp [aH, comp_lift]

theorem zS_aH [GrpObj A] {T : Over S} (x : T ⟶ X) : zS A T ≫ aH A x = x ≫ zS A X := by
  simp [aH, zS, comp_lift]

theorem zS_left_snd [GrpObj A] (T : Over S) : (zS A T).left ≫ (snd A T).left = 𝟙 T.left := by
  rw [← Over.comp_left]; simp [zS]

def Normed [GrpObj A] (M : LB (A ⊗ X).left) (R : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (zS A X).left) (fun _ => 1)))
    {T : Over S} (x x' : T ⟶ X) (l : LB.Gen (LB.LinComb M (K := Fin 2) ![(aH A x).left, (aH A x').left] ![-1, 1])) : Prop :=
  l.IsGen ∧ ∀ (Z : Scheme.{0}) (s : Z ⟶ T.left) (z : Z) (J : (Z ⟶ (A ⊗ X).left) → M.ι), Good M z J →
    val l (s ≫ (zS A T).left) z J = (val R (s ≫ x.left) z J)⁻¹ * val R (s ≫ x'.left) z J

variable [GrpObj A] {M : LB (A ⊗ X).left} {R : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => (zS A X).left) (fun _ => 1))}

theorem exists_normed (hM : M.IsLB) (hR : R.IsGen) {T : Over S} (x x' : T ⟶ X)
    (h : LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) : ∃ l, Normed M R x x' l := by
  have hc := (cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).2 h
  rw [cls_pull hM, cls_pull hM] at hc
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (LB.isLB_linComb hM ![(aH A x).left, (aH A x').left] ![-1, 1])).1 (by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul]
    rw [← hc]; simp)
  have e₁ : ∀ y : T ⟶ X, (zS A T).left ≫ (aH A y).left = y.left ≫ (zS A X).left := fun y => by
    rw [← Over.comp_left, ← Over.comp_left, zS_aH]
  obtain ⟨t', ht', hv⟩ := GlobalTheory.T.linear_combination_generator_section_exists hM ![(aH A x).left, (aH A x').left] ![-1, 1]
    (Sum.elim (fun _ : PUnit => x.left ≫ (zS A X).left) (fun _ : PUnit => x'.left ≫ (zS A X).left))
    (Sum.elim (fun _ => -1) (fun _ => 1)) (snd A T).left (zS A T).left (zS_left_snd T)
    (fun U _ k => by
      rw [Fin.prod_univ_two, Fintype.prod_sum_type]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.prod_singleton, zpow_neg, zpow_one]) t ht
    (LB.mulGen M _ _ _ _ (LB.invGen M _ _ (LB.pullGen M _ _ R x.left)) (LB.pullGen M _ _ R x'.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hR _)) (DVR.pullGen_isGen _ _ _ _ hR _))
  refine ⟨t', ht', fun Z s z J hJ => ?_⟩
  rw [hv Z s z J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ]

theorem normed_mul (hG : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB) {T : Over S} {x x' x'' : T ⟶ X}
    {l₁ l₂ l₃} (h₁ : Normed M R x x' l₁) (h₂ : Normed M R x' x'' l₂) (h₃ : Normed M R x x'' l₃)
    (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ T).left) (z : Z) (J) (hJ : Good M z J) :
    val l₁ r z J * val l₂ r z J = val l₃ r z J := by
  rw [← val_mul hJ]
  refine gen_unique' hM (fun U _ k => ?_) (snd A T).left (zS A T).left (zS_left_snd T) (surj_snd hG hA T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁.1 h₂.1) h₃.1 (fun y I hI => ?_) Z r z J hJ
  · rw [Fin.prod_univ_two, Fintype.prod_sum_type]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl, Sum.elim_inr, zpow_neg, zpow_one]
    group
  · have a₁ := h₁.2 _ (𝟙 _) y I hI
    have a₂ := h₂.2 _ (𝟙 _) y I hI
    have a₃ := h₃.2 _ (𝟙 _) y I hI
    simp only [Category.id_comp] at a₁ a₂ a₃
    rw [val_mul hI, a₁, a₂, a₃]
    group

theorem normed_pull (hG : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB) {T T' : Over S} {x x' : T ⟶ X} {y y' : T' ⟶ X}
    (v : T' ⟶ T) (e : v ≫ x = y) (e' : v ≫ x' = y') {l l'} (h : Normed M R x x' l) (h' : Normed M R y y' l')
    (Z : Scheme.{0}) (r : Z ⟶ (A ⊗ T').left) (z : Z) (J) (hJ : Good M z J) :
    val l' r z J = val l (r ≫ (aH A v).left) z J := by
  subst e e'
  rw [← val_pull hJ]
  refine gen_unique' hM (fun U _ k => ?_) (snd A T').left (zS A T').left (zS_left_snd T') (surj_snd hG hA T')
    h'.1 (DVR.pullGen_isGen _ _ _ _ h.1 _) (fun w I hI => ?_) Z r z J hJ
  · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Over.comp_left, ← Over.comp_left, aH_comp, aH_comp]
  · have a₁ := h'.2 _ (𝟙 _) w I hI
    have a₂ := h.2 _ v.left w I hI
    simp only [Category.id_comp] at a₁
    have e₀ : (zS A T').left ≫ (aH A v).left = v.left ≫ (zS A T).left := by
      rw [← Over.comp_left, ← Over.comp_left, zS_aH]
    rw [val_pull hI, e₀, a₁, a₂]; rfl

section Descent

variable {Y : Over S} (q : X ⟶ Y)

omit [GrpObj A] in
theorem fst_eq {W : Over S} {a b : W ⟶ A ⊗ X} (h : a ≫ aH A q = b ≫ aH A q) : a ≫ fst A X = b ≫ fst A X := by
  have := congrArg (· ≫ fst A Y) h
  simpa [aH] using this

omit [GrpObj A] in
theorem snd_eq {W : Over S} {a b : W ⟶ A ⊗ X} (h : a ≫ aH A q = b ≫ aH A q) :
    (a ≫ snd A X) ≫ q = (b ≫ snd A X) ≫ q := by
  have := congrArg (· ≫ snd A Y) h
  simpa [aH] using this

omit [GrpObj A] in
theorem hom_eq {W : Scheme.{0}} {a b : W ⟶ (A ⊗ X).left} (h : a ≫ (aH A q).left = b ≫ (aH A q).left) :
    b ≫ (A ⊗ X).hom = a ≫ (A ⊗ X).hom := by
  rw [← Over.w (aH A q), ← Category.assoc, ← Category.assoc, h]

abbrev T₂ (A : Over S) {X Y : Over S} (q : X ⟶ Y) : Over S :=
  Over.mk (pullback.fst (aH A q).left (aH A q).left ≫ (A ⊗ X).hom)

abbrev P₁ (A : Over S) {X Y : Over S} (q : X ⟶ Y) : T₂ A q ⟶ A ⊗ X := Over.homMk (pullback.fst _ _) rfl

abbrev P₂ (A : Over S) {X Y : Over S} (q : X ⟶ Y) : T₂ A q ⟶ A ⊗ X :=
  Over.homMk (pullback.snd _ _) (hom_eq q pullback.condition)

omit [GrpObj A] in
theorem charpoly_eq_of_isIso : P₁ A q ≫ aH A q = P₂ A q ≫ aH A q := Over.OverMorphism.ext pullback.condition

abbrev sg (A : Over S) {X Y : Over S} (q : X ⟶ Y) : T₂ A q ⟶ A ⊗ T₂ A q := lift (P₁ A q ≫ fst A X) (𝟙 _)

omit [GrpObj A] in
theorem sg_one : sg A q ≫ aH A (P₁ A q ≫ snd A X) = P₁ A q := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [aH, sg]

omit [GrpObj A] in
theorem sg_two : sg A q ≫ aH A (P₂ A q ≫ snd A X) = P₂ A q := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa [aH, sg] using fst_eq q (charpoly_eq_of_isIso q)
  · simp [aH, sg]

abbrev pr {W : Over S} (a b : W ⟶ A ⊗ X) (h : a.left ≫ (aH A q).left = b.left ≫ (aH A q).left) : W ⟶ T₂ A q :=
  Over.homMk (pullback.lift a.left b.left h) (by
    show pullback.lift a.left b.left h ≫ pullback.fst _ _ ≫ (A ⊗ X).hom = W.hom
    rw [pullback.lift_fst_assoc]; exact Over.w a)

omit [GrpObj A] in
theorem pr_one {W : Over S} (a b : W ⟶ A ⊗ X) (h) : pr q a b h ≫ P₁ A q = a :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

omit [GrpObj A] in
theorem pr_two {W : Over S} (a b : W ⟶ A ⊗ X) (h) : pr q a b h ≫ P₂ A q = b :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

omit [GrpObj A] in
theorem pr_sg {W : Over S} (a b : W ⟶ A ⊗ X) (h) :
    lift (a ≫ fst A X) (𝟙 W) ≫ aH A (pr q a b h) = pr q a b h ≫ sg A q := by
  apply CartesianMonoidalCategory.hom_ext
  · have := pr_one q a b h
    simp only [aH, sg, comp_lift, lift_fst, Category.assoc, lift_snd_assoc, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, this]
  · simp [aH, sg]

theorem exists_c (hM : M.IsLB) {l : LB.Gen (LB.LinComb M (K := Fin 2)
      ![(aH A (P₁ A q ≫ snd A X)).left, (aH A (P₂ A q ≫ snd A X)).left] ![-1, 1])} (hl : l.IsGen) :
    ∃ c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst (aH A q).left (aH A q).left,
        pullback.snd (aH A q).left (aH A q).left] ![-1, 1]), c.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback (aH A q).left (aH A q).left) (z : Z) (J), Good M z J →
        val c r z J = val l (r ≫ (sg A q).left) z J := by
  obtain ⟨c, hc, hv⟩ := exists_gen hM (φ' := ![pullback.fst (aH A q).left (aH A q).left,
      pullback.snd (aH A q).left (aH A q).left]) (ε' := ![-1, 1]) (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← Over.comp_left, ← Over.comp_left, sg_one, sg_two]; rfl)
    (LB.pullGen M _ _ l (sg A q).left) (DVR.pullGen_isGen _ _ _ _ hl _)
  exact ⟨c, hc, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem val_pr (hG : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hM : M.IsLB)
    {l : LB.Gen (LB.LinComb M (K := Fin 2)
      ![(aH A (P₁ A q ≫ snd A X)).left, (aH A (P₂ A q ≫ snd A X)).left] ![-1, 1])}
    (hl : Normed M R (P₁ A q ≫ snd A X) (P₂ A q ≫ snd A X) l) {W : Over S} (a b : W ⟶ A ⊗ X) (h)
    {l₀} (h₀ : Normed M R (a ≫ snd A X) (b ≫ snd A X) l₀) (w : W.left) (J) (hJ : Good M w J) :
    val l ((pr q a b h).left ≫ (sg A q).left) w J = val l₀ (lift (a ≫ fst A X) (𝟙 W)).left w J := by
  rw [normed_pull hG hA hM (pr q a b h) (by rw [← Category.assoc, pr_one]) (by rw [← Category.assoc, pr_two]) hl h₀ _ _ w J hJ,
    ← Over.comp_left, ← Over.comp_left, pr_sg]

end Descent

theorem descent_datum : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ (q : X ⟶ Y) (M : LB (A ⊗ X).left), M.IsLB →
    Triv (ev M (1 : X ⟶ A) (𝟙 X)) →
    (∀ (T : Over S) (x x' : T ⟶ X), x ≫ q = x' ≫ q →
        LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) →
    ∃ c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left,
        pullback.snd (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left] ![-1, 1]), c.IsGen ∧
      ∀ (W : Scheme.{0}) (a b d : W ⟶ (A ⊗ X).left) (hab : a ≫ (lift (fst A X) (snd A X ≫ q)).left = b ≫ (lift (fst A X) (snd A X ≫ q)).left)
        (hbd : b ≫ (lift (fst A X) (snd A X ≫ q)).left = d ≫ (lift (fst A X) (snd A X ≫ q)).left) (w : W) (J : (W ⟶ (A ⊗ X).left) → M.ι), Good M w J →
        val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J := by
  intro S A X Y _ hA q M hM hT hyp
  obtain ⟨R, hR⟩ := hT
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨l, hl⟩ := exists_normed (A := A) hM hR (P₁ A q ≫ snd A X) (P₂ A q ≫ snd A X)
    (hyp _ _ _ (snd_eq q (charpoly_eq_of_isIso q)))
  obtain ⟨c, hc, hv⟩ := exists_c q hM hl.1
  refine ⟨c, hc, fun W a b d hab hbd w J hJ => ?_⟩
  let W₀ : Over S := Over.mk (a ≫ (A ⊗ X).hom)
  let a' : W₀ ⟶ A ⊗ X := Over.homMk a rfl
  let b' : W₀ ⟶ A ⊗ X := Over.homMk b (hom_eq q hab)
  let d' : W₀ ⟶ A ⊗ X := Over.homMk d ((hom_eq q hbd).trans (hom_eq q hab))
  have eab : a' ≫ aH A q = b' ≫ aH A q := Over.OverMorphism.ext hab
  have ebd : b' ≫ aH A q = d' ≫ aH A q := Over.OverMorphism.ext hbd
  obtain ⟨l₁, h₁⟩ := exists_normed (A := A) hM hR (a' ≫ snd A X) (b' ≫ snd A X) (hyp _ _ _ (snd_eq q eab))
  obtain ⟨l₂, h₂⟩ := exists_normed (A := A) hM hR (b' ≫ snd A X) (d' ≫ snd A X) (hyp _ _ _ (snd_eq q ebd))
  obtain ⟨l₃, h₃⟩ := exists_normed (A := A) hM hR (a' ≫ snd A X) (d' ≫ snd A X) (hyp _ _ _ (snd_eq q (eab.trans ebd)))
  have v₁ := (hv W _ w J hJ).trans (val_pr q hG hA hM hl a' b' hab h₁ w J hJ)
  have v₂ := (hv W _ w J hJ).trans (val_pr q hG hA hM hl b' d' hbd h₂ w J hJ)
  have v₃ := (hv W _ w J hJ).trans (val_pr q hG hA hM hl a' d' (hab.trans hbd) h₃ w J hJ)
  rw [← fst_eq q eab] at v₂
  exact (congrArg₂ (· * ·) v₁ v₂).trans ((normed_mul hG hA hM h₁ h₂ h₃ _ _ w J hJ).trans v₃.symm)

end GlobalTheory.CompanionTheory.RigDescLink
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_generator_exists : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ (q : X ⟶ Y) (M : LB (A ⊗ X).left), M.IsLB →
    Triv (ev M (1 : X ⟶ A) (𝟙 X)) →
    (∀ (T : Over S) (x x' : T ⟶ X), x ≫ q = x' ≫ q →
        LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) →
    ∃ c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left,
        pullback.snd (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left] ![-1, 1]), c.IsGen ∧
      ∀ (W : Scheme.{0}) (a b d : W ⟶ (A ⊗ X).left) (hab : a ≫ (lift (fst A X) (snd A X ≫ q)).left = b ≫ (lift (fst A X) (snd A X ≫ q)).left)
        (hbd : b ≫ (lift (fst A X) (snd A X ≫ q)).left = d ≫ (lift (fst A X) (snd A X ≫ q)).left) (w : W) (J : (W ⟶ (A ⊗ X).left) → M.ι), Good M w J →
        val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RigDescLink.descent_datum
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem mul_mid {G : Type*} [CommGroup G] (x y z p q : G) : x * (p * q) * z⁻¹ = (x * p * y⁻¹) * (y * q * z⁻¹) := by
  simp only [_root_.mul_assoc, inv_mul_cancel_left]

theorem mul_fix {G : Type*} [CommGroup G] (x y t : G) : (x * y⁻¹ * t) * x⁻¹ = t * y⁻¹ := by
  rw [_root_.mul_comm x, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_comm x, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one, _root_.mul_comm]

theorem gs_appTop {W Y : Scheme.{0}} (φ : W ⟶ Y) (u : Γ(Y, ⊤)ˣ) (x : W) :
    gs (𝟙 W) x ⊤ (φ.appTop.hom u.val) = (gm φ x ⊤ u).val := by
  have e := gs_pull (𝟙 W) φ x ⊤ trivial u.val
  rw [Category.id_comp] at e
  exact e.trans (gs_unit φ x ⊤ trivial u)

theorem lbDescent (hH : H90) {P Q : Scheme.{0}} (f : P ⟶ Q) (hf : Flat f) (hl : LocallyOfFinitePresentation f)
    (hs : Surjective f) (M : LB P) (hM : M.IsLB)
    (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])) (hc : c.IsGen)
    (coc : ∀ (W : Scheme.{0}) (a b d : W ⟶ P) (hab : a ≫ f = b ≫ f) (hbd : b ≫ f = d ≫ f) (w : W)
      (J : (W ⟶ P) → M.ι), Good M w J →
      val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J) :
    ∃ N : LB Q, N.IsLB ∧ LBIso M (N.pull f) := by
  obtain ⟨Z, g, hg, hgl, hgs, τ, hτ⟩ := GlobalTheory.T.line_bundle_trivial_after_flat_cover M hM
  have h₁ : Flat (g ≫ f) := inferInstance
  have h₂ : LocallyOfFinitePresentation (g ≫ f) := inferInstance
  have h₃ : Surjective (g ≫ f) := inferInstance
  obtain ⟨u, hu, hv⟩ := GlobalTheory.T.generator_descent_unit_exists g f M hM c hc τ hτ
  have good : ∀ {W : Scheme.{0}} (w : W), ∃ J : (W ⟶ P) → M.ι, Good M w J := fun w =>
    ⟨fun χ => (exists_chart hM (χ w)).choose, fun χ => (exists_chart hM (χ w)).choose_spec⟩
  have cocu : ∀ (W : Scheme.{0}) (a b d : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (hbd : b ≫ g ≫ f = d ≫ g ≫ f),
      (pullback.lift a d (hab.trans hbd)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b d hbd).appTop u := by
    intro W a b d hab hbd
    have e₀ : ∀ φ : W ⟶ pullback (g ≫ f) (g ≫ f), φ.appTop u = φ.appTop.hom hu.unit.val := fun _ => rfl
    refine fn_ext fun x _ => ?_
    obtain ⟨J, hJ⟩ := good x
    have hab' : (a ≫ g) ≫ f = (b ≫ g) ≫ f := by simpa using hab
    have hbd' : (b ≫ g) ≫ f = (d ≫ g) ≫ f := by simpa using hbd
    have key : gm (pullback.lift a d (hab.trans hbd)) x ⊤ hu.unit =
        gm (pullback.lift a b hab) x ⊤ hu.unit * gm (pullback.lift b d hbd) x ⊤ hu.unit := by
      rw [hv _ _ _ _ _ _ hJ, hv _ _ _ _ _ _ hJ, hv _ _ _ _ _ _ hJ]
      rw [← coc W (a ≫ g) (b ≫ g) (d ≫ g) hab' hbd' x J hJ]
      exact mul_mid _ _ _ _ _
    rw [gs_mul (𝟙 W) x ⊤ trivial, e₀, e₀, e₀, gs_appTop, gs_appTop, gs_appTop, key, Units.val_mul]
  obtain ⟨N, hN, T, hT, hTv⟩ := GlobalTheory.T.cocycle_defines_descended_line_bundle hH (g ≫ f) h₁ h₂ h₃ u hu cocu
  refine ⟨N, hN, GlobalTheory.T.lbIso_pull_of_generator_ratio_eq g f hg hgl hgs M hM N hN τ hτ T hT fun W a b hab w i k hi hk => ?_⟩
  have hab' : a ≫ g ≫ f = b ≫ g ≫ f := by rw [← Category.assoc, hab, Category.assoc]
  obtain ⟨J, hJ, hJk⟩ := exists_good M hM w (K := PUnit) (fun _ => a ≫ g) (fun _ => k) (fun _ _ _ => rfl) (fun _ => hk)
  have hJk' : J (a ≫ g) = k := hJk PUnit.unit
  have one : ∀ (x y : W ⟶ P) (h : x ≫ f = y ≫ f), x = y → val c (pullback.lift x y h) w J = 1 := by
    rintro x _ h rfl
    exact mul_eq_left.1 (coc W x x x h h w J hJ)
  have va : val τ a w J = gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k) := val_of τ a w J _ fun _ => hJk'
  have vb : val τ b w J = gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k) := val_of τ b w J _ fun _ => by rw [← hab]; exact hJk'
  have e := hTv W a b hab' w i hi
  rw [hv _ _ _ _ _ _ hJ, one _ _ _ hab, va, vb, _root_.mul_one] at e
  rw [e]
  exact mul_fix _ _ _

theorem rigDescent : H90 → RigDescent := by
  intro hH S A X Y _ hA q hq hl hs
  refine ⟨GlobalTheory.T.seesaw_triviality_abelian_scheme S A X Y hA q hq hl hs, fun M hM hr hinv => ?_⟩
  obtain ⟨hf, hfl, hfs⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hq hl hs
  obtain ⟨c, hc, coc⟩ := GlobalTheory.T.theorem_of_cube_generator_exists S A X Y hA q M hM hr hinv
  obtain ⟨N₀, hN₀, iso⟩ := lbDescent hH _ hf hfl hfs M hM c hc coc
  let eY := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  let eX := (lift (1 : X ⟶ A) (𝟙 X)).left
  let pY := (snd A Y).left
  let pX := (snd A X).left
  let f := (lift (fst A X) (snd A X ≫ q)).left
  have e₁ : eY ≫ pY = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : f ≫ pY ≫ eY = pX ≫ eX ≫ f := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1 <;> simp
  obtain ⟨N, hN, hc'⟩ := cls_surj (cls N₀ hN₀ - CechPic.pull pY (CechPic.pull eY (cls N₀ hN₀)))
  have hm : cls M hM = CechPic.pull f (cls N₀ hN₀) := (cls_eq_iff hM (pull_isLB hN₀ _)).2 iso
  have z : CechPic.pull eX (cls M hM) = 0 := (triv_ev_iff hM _ _).1 hr
  refine ⟨N, hN, (triv_ev_iff hN _ _).2 ?_, (cls_eq_iff hM (pull_isLB hN _)).1 ?_⟩
  · show CechPic.pull eY (cls N hN) = 0
    rw [hc', map_sub, ← pull_comp, e₁, pull_id, sub_self]
  · show cls M hM = CechPic.pull f (cls N hN)
    rw [hc', map_sub, ← pull_comp f pY, ← pull_comp (f ≫ pY) eY, Category.assoc, e₂, pull_comp pX, pull_comp eX, ← hm, z, map_zero,
      sub_zero, hm]

end GlobalTheory.CompanionTheory.RigDesc
end
