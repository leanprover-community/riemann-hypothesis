import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRing
import Development.WeilBound.CoreStatements.SesquilinearFractions.NBasic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCptStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FixedByAutomorphismsMemField
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebraStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LocallyQuasiFiniteSpMap
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingValuationSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHolds
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFinite
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem abelianTriple_spreads_out : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (tL : SAB H (Sp L)), IsProper tL.G.hom → ∃ (n : 𝓞 L) (_ : n ≠ 0) (T : SAB H (Sp (Localization.Away n))) (f : Localization.Away n →+* L), (∀ x : 𝓞 L, f (algebraMap _ _ x) = (x : L)) ∧ Nonempty (SABMap tL T (spMap f)) :=
  PositivityTheory.Xgn.abelian_scheme_spreads_over_localization

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePointFrame

theorem alg_descend {O K T : Type} [CommRing O] [Field K] [AddCommGroup T] [Module K T] (ρ : O →+* Module.End K T)
    (σ : O →+* K) {N n : ℕ} (t : Fin N → T) (ht : Submodule.span K (Set.range t) = ⊤) (u : Fin n → T)
    (h1 : ∀ i, u i ∈ eigSp ρ σ) (h2 : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → K, e = ∑ i, cf i • u i) :
    ∃ Z : Set K, Z.Finite ∧ ∀ (V : Type) [CommRing V] (g : V →+* K) (M : Type) [AddCommGroup M] [Module V M]
      (b : M →+ T) (s : Fin N → M) (ρV : O →+* Module.End V M) (σV : O →+* V), Function.Injective g →
      Z ⊆ Set.range g → Function.Injective b → (∀ c x, b (c • x) = g c • b x) → (∀ i, b (s i) = t i) →
      Submodule.span V (Set.range s) = ⊤ → (∀ a x, b (ρV a x) = ρ a (b x)) → g.comp σV = σ →
      ∃ u' : Fin n → M, (∀ i, b (u' i) = u i) ∧ (∀ i, u' i ∈ eigSp ρV σV) ∧
        ∀ e ∈ eigSp ρV σV, ∃! cf : Fin n → V, e = ∑ i, cf i • u' i := by
  classical
  have hli : LinearIndependent K u := Fintype.linearIndependent_iff.2 fun g hg i => by
    have := (h2 0 (Submodule.zero_mem _)).unique hg.symm (y₂ := 0) (by simp)
    exact congrFun this i
  obtain ⟨L, hL⟩ := (Fintype.linearCombination K u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli.fintypeLinearCombination_injective)
  have hL' : ∀ cf : Fin n → K, L (∑ i, cf i • u i) = cf := fun cf => by
    have := LinearMap.congr_fun hL cf
    simpa [Fintype.linearCombination_apply] using this
  have ha : ∀ k, ∃ a : Fin N → K, ∑ i, a i • t i = u k := fun k =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (ht ▸ Submodule.mem_top)
  choose a ha using ha
  refine ⟨Set.range (fun x : Fin n × Fin N => a x.1 x.2) ∪ Set.range (fun x : Fin n × Fin N => L (t x.2) x.1),
    (Set.finite_range _).union (Set.finite_range _), ?_⟩
  intro V _ g M _ _ b s ρV σV hg hZ hb hsm hs hsp hρ hσ
  choose a' ha' using fun k i => hZ (Or.inl ⟨(k, i), rfl⟩)
  choose l' hl' using fun k i => hZ (Or.inr ⟨(k, i), rfl⟩)
  have hbu : ∀ k, b (∑ i, a' k i • s i) = u k := fun k => by
    rw [map_sum, ← ha k]
    exact Finset.sum_congr rfl fun i _ => by rw [hsm, hs, ha']
  have heig : ∀ x, x ∈ eigSp ρV σV ↔ b x ∈ eigSp ρ σ := fun x => by
    rw [EigBase.mem_eigSp, EigBase.mem_eigSp]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hσ, RingHom.comp_apply, ← hsm, hb.eq_iff]
  have hsum : ∀ cf : Fin n → V, b (∑ k, cf k • ∑ i, a' k i • s i) = ∑ k, g (cf k) • u k := fun cf => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hsm, hbu]
  refine ⟨fun k => ∑ i, a' k i • s i, hbu, fun k => (heig _).2 (by rw [hbu]; exact h1 k), fun e he => ?_⟩
  obtain ⟨cf, hcf, -⟩ := h2 _ ((heig e).1 he)
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 (hsp ▸ Submodule.mem_top : e ∈ _)
  have hc : ∀ k, cf k = g (∑ i, x i * l' k i) := fun k => by
    rw [← hL' cf, ← hcf, ← hx, map_sum, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, hs, map_smul, map_mul, hl']
    rfl
  have he' : e = ∑ k, (∑ i, x i * l' k i) • ∑ i, a' k i • s i := hb (by
    rw [hsum, hcf]
    exact Finset.sum_congr rfl fun k _ => by rw [hc])
  refine ⟨fun k => ∑ i, x i * l' k i, he', fun y hy => funext fun k => hg ?_⟩
  have e1 := congrArg b (hy.symm.trans he')
  rw [hsum, hsum] at e1
  exact congrFun ((hL' _).symm.trans ((congrArg L e1).trans (hL' _))) k

theorem lie_lift {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {R R' : Type} [CommRing R]
    [CommRing R'] (g : R →+* R') {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (hx : x' = spMap g ≫ x) {V V' : Type}
    [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R' V'] (M : LieModel G x V) (M' : LieModel G x' V') :
    ∃ b : V →+ V', (∀ e, (M'.pt (b e)).left = spMap (dualMap g) ≫ (M.pt e).left) ∧
      (∀ c e, b (c • e) = g c • b e) ∧ Submodule.span R' (Set.range b) = ⊤ ∧
      (Function.Injective g → Function.Injective b) := by
  letI := g.toAlgebra
  subst hx
  obtain ⟨T, _, _, _, _, M'', j, hl, hj⟩ := GlobalTheory.T.exists_lie_model_base_change S G R R' x V M
  obtain ⟨f, hf, -⟩ := lieModel_existsUnique_equiv S G R' _ T V' M'' M'
  refine ⟨f.toLinearMap.toAddMonoidHom.comp j.toAddMonoidHom, fun e => ?_, fun c e => ?_, ?_, fun hg => ?_⟩
  · have := hl e
    show (M'.pt (f (j e))).left = _
    rw [hf]
    simpa [LieModel.Lifts] using this
  · show f (j (c • e)) = g c • f (j e)
    rw [j.map_smul, ← algebraMap_smul R' c (j e), f.map_smul]
    rfl
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨z, rfl⟩ := f.surjective y
    induction z using hj.inductionOn with
    | zero => simp
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n h => rw [map_smul]; exact Submodule.smul_mem _ _ (h trivial)
    | add m n h h' => rw [map_add]; exact Submodule.add_mem _ (h trivial) (h' trivial)
  · haveI : Module.Projective R V := (LieProj.lie_finite_projective_baseChange S G R x V M).2.1
    haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hg
    intro a c hac
    have h1 : j a = j c := f.injective hac
    refine Module.Flat.tensorProduct_mk_injective R V R' (hj.equiv.injective ?_)
    simpa [hj.equiv_tmul] using h1

theorem span_map {R R' V V' : Type} [CommRing R] [CommRing R'] [AddCommGroup V] [Module R V] [AddCommGroup V']
    [Module R' V'] (g : R →+* R') (b : V →+ V') (hb : ∀ c e, b (c • e) = g c • b e)
    (h : Submodule.span R' (Set.range b) = ⊤) {N : ℕ} {s : Fin N → V} (hs : Submodule.span R (Set.range s) = ⊤) :
    Submodule.span R' (Set.range fun i => b (s i)) = ⊤ := by
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hs ▸ Submodule.mem_top : e ∈ _)
  rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [hb]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem frame_descend {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {R K : Type}
    [CommRing R] [Field K] (f : R →+* K) (x : Sp R ⟶ S) (xK : Sp K ⟶ S) (hx : xK = spMap f ≫ x) {O : Type}
    [CommRing O] (act : OAct O G) (σ : O →+* K) {n : ℕ} (v : Fin n → (epsAt xK ⟶ G)) (hv : IsEigFrame act xK σ v) :
    ∃ Z : Set K, Z.Finite ∧ ∀ (V : Type) [CommRing V] (g : V →+* K) (r : R →+* V) (σV : O →+* V) (xV : Sp V ⟶ S),
      Function.Injective g → Z ⊆ Set.range g → g.comp r = f → g.comp σV = σ → xV = spMap r ≫ x →
      ∃ v' : Fin n → (epsAt xV ⟶ G), IsEigFrame act xV σV v' ∧
        ∀ i, (v i).left = spMap (dualMap g) ≫ (v' i).left := by
  obtain ⟨MR, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨T, _, _, ⟨MK⟩⟩ := lieModel_exists S G K xK
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G K xK T MK O act.act act.hom act.one act.mul act.add
  haveI : Module.Finite R MR := (LieProj.lie_finite_projective_baseChange S G R x MR M).1
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := MR)
  obtain ⟨jK, hjK, hsK, hspK, -⟩ := lie_lift f hx M MK
  choose u hu using fun i => MK.onto (v i) (hv.1 i).1
  obtain rfl : (fun k => MK.pt (u k)) = v := funext hu
  obtain ⟨h1, h2⟩ := (LieEigFrame.isEigFrame_pt_iff S K G xK T MK O act ρ σ n u hρ).1 hv
  obtain ⟨Z, hZ, H⟩ := alg_descend ρ σ _ (span_map f jK hsK hspK hs) u h1 h2
  refine ⟨Z, hZ, fun V _ g r σV xV hg hZg hr hσ hxV => ?_⟩
  obtain ⟨W, _, _, ⟨MV⟩⟩ := lieModel_exists S G V xV
  obtain ⟨ρV, hρV, -⟩ := lieModel_exists_unique_act S G V xV W MV O act.act act.hom act.one act.mul act.add
  obtain ⟨jV, hjV, hsV, hspV, -⟩ := lie_lift r hxV M MV
  have hxK : xK = spMap g ≫ xV := by
    rw [hx, hxV, ← hr, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨b, hb, hsb, -, hinj⟩ := lie_lift g hxK MV MK
  have hd : spMap (dualMap f) = spMap (dualMap g) ≫ spMap (dualMap r) := by
    rw [← Spec.map_comp, ← hr]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    show dualMap (g.comp r) a = dualMap g (dualMap r a)
    ext <;> simp [dualMap]
  obtain ⟨u', e1, e2, e3⟩ := H V g W b (fun i => jV (s i)) ρV σV hg hZg (hinj hg) hsb
    (fun i => MK.inj (Over.OverMorphism.ext (by rw [hb, hjV, hjK, hd, Category.assoc])))
    (span_map r jV hsV hspV hs)
    (fun a e => MK.inj (Over.OverMorphism.ext (by
      rw [hρ a (b e), Over.comp_left, hb, hb, hρV a e, Over.comp_left, Category.assoc]))) hσ
  refine ⟨fun i => MV.pt (u' i), (LieEigFrame.isEigFrame_pt_iff S V G xV W MV O act ρV σV n u' hρV).2 ⟨e2, e3⟩,
    fun i => ?_⟩
  rw [← hb, e1]

theorem frame_transfer {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (x : Sp R ⟶ S) (hx : x = x' ≫ f) (σ : 𝓞 E →+* R) (n : ℕ) :
    (∀ v' : Fin n → (epsAt x' ⟶ t'.G), IsEigFrame t'.act x' σ v' → ∃ v : Fin n → (epsAt x ⟶ t.G),
      IsEigFrame t.act x σ v ∧ ∀ i, (v' i).left ≫ m.φ = (v i).left) ∧
    ∀ v : Fin n → (epsAt x ⟶ t.G), IsEigFrame t.act x σ v → ∃ v' : Fin n → (epsAt x' ⟶ t'.G),
      IsEigFrame t'.act x' σ v' ∧ ∀ i, (v' i).left ≫ m.φ = (v i).left := by
  subst hx
  obtain ⟨V, _, _, ⟨M'⟩⟩ := lieModel_exists S' t'.G R x'
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap E H S S' t' t f m R x' V M'
  obtain ⟨ρ, hρ', -⟩ := lieModel_exists_unique_act S' t'.G R x' V M' _ t'.act.act t'.act.hom t'.act.one t'.act.mul
    t'.act.add
  have hρ : M.IsActOf t.act.act ρ := fun a e => Over.OverMorphism.ext (by
    rw [Over.comp_left, hM, hM, hρ' a e, Over.comp_left, Category.assoc, Category.assoc, m.act])
  have key : ∀ u : Fin n → V, IsEigFrame t'.act x' σ (fun i => M'.pt (u i)) ↔
      IsEigFrame t.act (x' ≫ f) σ (fun i => M.pt (u i)) := fun u =>
    (LieEigFrame.isEigFrame_pt_iff _ _ _ _ _ M' _ t'.act ρ σ n u hρ').trans
      (LieEigFrame.isEigFrame_pt_iff _ _ _ _ _ M _ t.act ρ σ n u hρ).symm
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · choose u hu using fun i => M'.onto (v i) (h.1 i).1
    obtain rfl : (fun k => M'.pt (u k)) = v := funext hu
    exact ⟨_, (key u).1 h, fun i => (hM _).symm⟩
  · choose u hu using fun i => M.onto (v i) (h.1 i).1
    obtain rfl : (fun k => M.pt (u k)) = v := funext hu
    exact ⟨_, (key u).2 h, fun i => (hM _).symm⟩

theorem exists_sab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (f : S' ⟶ S)
    (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m₁⟩⟩

theorem exists_point {X : Scheme.{0}} {F : Type} [Field F] (s : X ⟶ Sp F) [LocallyOfFiniteType s] (U : Set X)
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ (L : Type) (_ : Field L) (β : F →+* L) (y : Sp L ⟶ X),
      β.Finite ∧ y ≫ s = spMap β ∧ Set.range y ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx hU
  replace hW : IsAffineOpen W := hW
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hW.fromSpec ≫ s)
  have hft : ψ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map ψ) := by
      rw [hψ]
      exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance ‹_›
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hr : Set.range hW.fromSpec = (W : Set X) := hW.range_fromSpec
  obtain ⟨q, -⟩ : x ∈ Set.range hW.fromSpec := hr ▸ hxW
  haveI : Nontrivial Γ(X, W) := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, W)
  letI := Ideal.Quotient.field m
  refine ⟨Γ(X, W) ⧸ m, inferInstance, (Ideal.Quotient.mk m).comp ψ.hom,
    spMap (Ideal.Quotient.mk m) ≫ hW.fromSpec, ?_, ?_, ?_⟩
  · exact RingHom.finite_iff_finiteType_of_isJacobsonRing.2
      ((RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft)
  · rw [Category.assoc, ← hψ]
    exact (Spec.map_comp _ _).symm
  · rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hWU (hr ▸ ⟨_, rfl⟩)

theorem exists_framed {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c)
      (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w := by
  haveI := c.fin
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  haveI := Xo.univ.t.semi.smooth
  obtain ⟨L, _, β, y, hfin, hy, hyU⟩ :=
    exists_point (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) U hU hne
  let k := AlgebraicClosure L
  let βk : c.F →+* k := (algebraMap L k).comp β
  have hxs : (spMap (algebraMap L k) ≫ under y) ≫ Xo.s =
      spMap (βk.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y, hy, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hdet := (Xo.univ.geom k _ _ hxs).1
  have h0 : tauIn c τ H.rt = (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ := Subtype.ext hτ
  have h1 : tauIn c (ComplexEmbedding.conjugate τ) H.rt ≠ (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ := by
    intro h
    have h' : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := congrArg Subtype.val h
    rw [hτ] at h'
    obtain ⟨a, ha⟩ := Complex.conj_eq_iff_real.1 h'
    have h2 := H.sqrt_neg_disc_sq
    rw [ha] at h2
    have h3 : a ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg a]
  obtain ⟨v, hv⟩ : ∃ v : Fin D.p → (epsAt (spMap (algebraMap L k) ≫ under y) ⟶ Xo.univ.t.G),
      IsEigFrame Xo.univ.t.act _ (βk.comp (tauIn c τ)) v :=
    (hdet (βk.comp (tauIn c τ))).1 (congrArg βk h0)
  obtain ⟨w, hw⟩ : ∃ w : Fin D.q → (epsAt (spMap (algebraMap L k) ≫ under y) ⟶ Xo.univ.t.G),
      IsEigFrame Xo.univ.t.act _ (βk.comp (tauIn c (ComplexEmbedding.conjugate τ))) w :=
    (hdet (βk.comp (tauIn c (ComplexEmbedding.conjugate τ)))).2 fun h => h1 (βk.injective h)
  obtain ⟨Z₁, hZ₁, H₁⟩ := frame_descend (algebraMap L k) (under y) _ rfl _ _ v hv
  obtain ⟨Z₂, hZ₂, H₂⟩ := frame_descend (algebraMap L k) (under y) _ rfl _ _ w hw
  let K := IntermediateField.adjoin L (Z₁ ∪ Z₂)
  haveI : Finite (Z₁ ∪ Z₂ : Set k) := (hZ₁.union hZ₂).to_subtype
  haveI : FiniteDimensional L K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let βK : c.F →+* K := (algebraMap L K).comp β
  have hβK : βK.Finite := (RingHom.finite_algebraMap.2 inferInstance).comp hfin
  haveI : CharZero K := βK.charZero_iff βK.injective |>.1 inferInstance
  haveI : NumberField c.F := { }
  haveI : NumberField K := by
    letI := βK.toAlgebra
    haveI : Module.Finite c.F K := hβK
    exact NumberField.of_module_finite c.F K
  have hZ : Z₁ ∪ Z₂ ⊆ Set.range (algebraMap K k) := fun z hz => ⟨⟨z, IntermediateField.subset_adjoin _ _ hz⟩, rfl⟩
  obtain ⟨v', hv', -⟩ := H₁ K (algebraMap K k) (algebraMap L K) (βK.comp (tauIn c τ))
    (under (spMap (algebraMap L K) ≫ y)) (algebraMap K k).injective (Set.subset_union_left.trans hZ) rfl rfl
    (Category.assoc _ _ _)
  obtain ⟨w', hw', -⟩ := H₂ K (algebraMap K k) (algebraMap L K) (βK.comp (tauIn c (ComplexEmbedding.conjugate τ)))
    (under (spMap (algebraMap L K) ≫ y)) (algebraMap K k).injective (Set.subset_union_right.trans hZ) rfl rfl
    (Category.assoc _ _ _)
  refine ⟨K, inferInstance, inferInstance, βK, spMap (algebraMap L K) ≫ y, v', w', ?_, ?_, hv', hw'⟩
  · rw [Category.assoc, hy, ← Spec.map_comp]
    rfl
  · rintro _ ⟨p, rfl⟩
    exact hyU ⟨spMap (algebraMap L K) p, (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem exists_denom {K : Type} [Field K] [NumberField K] (Z : Set K) (hZ : Z.Finite) :
    ∃ n : ℕ, 0 < n ∧ ∀ z ∈ Z, ∃ a : 𝓞 K, (a : K) = n * z := by
  obtain ⟨y, hy, H⟩ := exists_integral_multiples ℤ ℚ hZ.toFinset
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun z hz => ?_⟩
  have h := H z (hZ.mem_toFinset.2 hz)
  rcases Int.natAbs_eq y with e | e
  · refine ⟨⟨y • z, h⟩, ?_⟩
    show y • z = _
    rw [zsmul_eq_mul]
    nth_rewrite 1 [e]
    simp
  · refine ⟨⟨-(y • z), h.neg⟩, ?_⟩
    show -(y • z) = _
    rw [zsmul_eq_mul]
    nth_rewrite 1 [e]
    simp

theorem intFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {K R : Type} [Field K] [CommRing R] {y : Sp K ⟶ Xo.XF c} {tK : SAB H (Sp K)}
    (m : SABMap tK Xo.univ.t (under y)) {T : SAB H (Sp R)} (f : R →+* K) (m₀ : SABMap tK T (spMap f))
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) (hv : IsEigFrame Xo.univ.t.act (under y) σ v) :
    ∃ Z : Set K, Z.Finite ∧ ∀ (V : Type) [CommRing V] [Algebra V K] (r : R →+* V) (σV : 𝓞 E →+* V)
      (TV : SAB H (Sp V)) (mV : SABMap TV T (spMap r)) (m' : SABMap tK TV (spMap (algebraMap V K))),
      Function.Injective (algebraMap V K) → Z ⊆ Set.range (algebraMap V K) → (algebraMap V K).comp r = f →
      (algebraMap V K).comp σV = σ → m₀.φ = m'.φ ≫ mV.φ → IsIntFrame m m' σ v := by
  haveI := T.semi.smooth
  obtain ⟨vK, hvK, eK⟩ := (frame_transfer m (𝟙 _) (under y) (Category.id_comp _).symm σ n).2 v hv
  obtain ⟨vT, hvT, eT⟩ := (frame_transfer m₀ (𝟙 _) (spMap f) (Category.id_comp _).symm σ n).1 vK hvK
  obtain ⟨Z, hZ, HZ⟩ := frame_descend f (𝟙 _) (spMap f) (Category.comp_id _).symm T.act σ vT hvT
  refine ⟨Z, hZ, fun V _ _ r σV TV mV m' hg hZg hr hσ hm => ?_⟩
  obtain ⟨v', hv', e'⟩ := HZ V (algebraMap V K) r σV (spMap r) hg hZg hr hσ (Category.comp_id _).symm
  obtain ⟨vV, hvV, eV⟩ := (frame_transfer mV (𝟙 _) (spMap r) (Category.id_comp _).symm σV n).2 v' hv'
  refine ⟨σV, vV, hσ, hvV, fun a => ⟨(vK a).left, eK a, ?_⟩⟩
  have hp : IsPullback mV.φ TV.G.hom T.G.hom (spMap r) := mV.cart.1
  have hq : IsPullback m'.φ tK.G.hom TV.G.hom (spMap (algebraMap V K)) := m'.cart.1
  apply hp.hom_ext
  · rw [Category.assoc, ← hm, eT, e', Category.assoc, eV]
  · have a₁ : (vK a).left ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) ≫ 𝟙 _ := Over.w (vK a)
    have a₂ : (vV a).left ≫ TV.G.hom = spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _ := Over.w (vV a)
    rw [Category.assoc, hq.w, ← Category.assoc, a₁, Category.assoc, Category.assoc, a₂, Category.comp_id,
      Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    show algebraMap K (DualNumber K) (algebraMap V K z) = dualMap (algebraMap V K) (algebraMap V (DualNumber V) z)
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' S'' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} (g : S'' ⟶ S') {h : S'' ⟶ S} (e : h = g ≫ f)
    (m : SABMap t' t f) (n : SABMap t'' t h) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n

end GlobalTheory.CompanionTheory.Ar.Flat.LinePointFrame

namespace GlobalTheory.CompanionTheory.Ar.Flat

open LinePointFrame in

theorem line_function_norm_zero_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsOpen U → U.Nonempty → IsLineFn U τ φ → ∃ n : ℕ, 0 < n ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ), ¬ (p : ℕ) ∣ n → HasFinNorm U τ φ p κ t → t = 0 := by
  intro E _ _ _ H D l Xo c U τ φ hτ hU hne hφ
  haveI := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨K, _, _, β, y, v, w, hfr⟩ := exists_framed Xo c U τ hτ hU hne
  obtain ⟨tK, ⟨m⟩⟩ := LinePointFrame.exists_sab (under y) Xo.univ.t
  have hprop : IsProper tK.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  obtain ⟨n₀, hn₀, T, f, hf, ⟨m₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.Flat.abelianTriple_spreads_out E H K tK hprop
  obtain ⟨Z₁, hZ₁, H₁⟩ := intFrame m f m₀ _ v hfr.2.2.1
  obtain ⟨Z₂, hZ₂, H₂⟩ := intFrame m f m₀ _ w hfr.2.2.2
  have hφ0 : φ K y v w ≠ 0 := hφ.ne K β y v w hfr
  obtain ⟨n, hn, Hn⟩ := exists_denom (Z₁ ∪ Z₂ ∪ {φ K y v w, (φ K y v w)⁻¹, (n₀ : K)⁻¹})
    ((hZ₁.union hZ₂).union (Set.toFinite _))
  refine ⟨n, hn, fun p κ t hp ht => ?_⟩
  obtain ⟨j, hj⟩ := PositivityTheory.Xgf.exists_extension_embedding_alg_closed c.F K ℂ_[p] β κ
  obtain ⟨V, hV, hjV, hOV, hnV⟩ := GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding K p j
  have hle : ∀ z ∈ Z₁ ∪ Z₂ ∪ {φ K y v w, (φ K y v w)⁻¹, (n₀ : K)⁻¹}, ‖j z‖ ≤ 1 := fun z hz => by
    obtain ⟨a, ha⟩ := Hn z hz
    have := (hjV _).2 (hOV a)
    rwa [ha, map_mul, norm_mul, hnV n hp, _root_.one_mul] at this
  have hrange : ∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range := fun a =>
    (hjV a).trans ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  have hn₀K : (n₀ : K) ≠ 0 := fun h => hn₀ (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hfV : ∀ x, f x ∈ V.toSubring := fun x => by
    obtain ⟨k, a, hx⟩ := IsLocalization.Away.surj n₀ x
    have h1 := congrArg f hx
    rw [map_mul, map_pow, hf, hf] at h1
    have h2 : f x = (a : K) * ((n₀ : K)⁻¹) ^ k := by
      rw [← h1, inv_pow, mul_inv_cancel_right₀ (pow_ne_zero k hn₀K)]
    rw [h2]
    exact mul_mem (hOV a) (pow_mem ((hjV _).1 (hle _ (by simp))) k)
  have hσV : ∀ (σ : 𝓞 E →+* K) (x : 𝓞 E), σ x ∈ V.toSubring := fun σ x =>
    hOV ⟨σ x, (RingOfIntegers.isIntegral x).map σ.toIntAlgHom⟩
  let r : Localization.Away n₀ →+* V := f.codRestrict V.toSubring hfV
  obtain ⟨TV, ⟨mV⟩⟩ := LinePointFrame.exists_sab (spMap r) T
  obtain ⟨m', hm'⟩ := exists_cancel (spMap (algebraMap V K)) (h := spMap f) (by rw [← Spec.map_comp]; rfl) mV m₀
  have key := ht V K j β y v w TV tK m m' hrange hj hfr
    (H₁ V r (RingHom.codRestrict (β.comp (tauIn c τ)) V.toSubring (hσV _)) TV mV m' Subtype.val_injective
      (fun z hz => (hrange z).1 (hle z (Or.inl (Or.inl hz)))) rfl rfl hm')
    (H₂ V r (RingHom.codRestrict (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) V.toSubring (hσV _)) TV mV m' Subtype.val_injective
      (fun z hz => (hrange z).1 (hle z (Or.inl (Or.inr hz)))) rfl rfl hm')
  have a₁ := hle (φ K y v w) (by simp)
  have a₂ := hle (φ K y v w)⁻¹ (by simp)
  have a₃ : 0 < ‖j (φ K y v w)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hφ0)
  rw [map_inv₀, norm_inv, inv_le_one₀ a₃] at a₂
  rw [← key, le_antisymm a₁ a₂, Real.log_one]

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_zero_outside_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsOpen U → U.Nonempty → IsLineFn U τ φ → ∃ n : ℕ, 0 < n ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ), ¬ (p : ℕ) ∣ n → HasFinNorm U τ φ p κ t → t = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.line_function_norm_zero_away
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left :=
  PositivityTheory.Xgn.framed_point_specialization
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framed_point_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat.Ratio

open Matrix

local notation "HF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm

theorem hf_sum_left {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    HF Hm (∑ i, c i • V i) w = ∑ i, c i * HF Hm (V i) w := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, sum_dotProduct, smul_dotProduct]

theorem hf_sum_right {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    HF Hm z (∑ i, c i • V i) = ∑ i, star (c i) * HF Hm z (V i) := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum,
    Matrix.mulVec_smul, dotProduct_smul]

theorem exists_row {R M I : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype I]
    (e : I → M) (he : LinearIndependent R e) (hc : Fintype.card I = Module.finrank R M) (x : M) :
    ∃ (n : R) (c : I → R), n ≠ 0 ∧ n • x = ∑ m, c m • e m := by
  classical
  have hnot : ¬ LinearIndependent R (fun o : Option I => o.elim x e) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, hc] at this
    omega
  obtain ⟨c, hsum, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hnot
  rw [Fintype.sum_option] at hsum
  simp only [Option.elim] at hsum
  have hn : c none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hsum
    have := Fintype.linearIndependent_iff.1 he (fun m => c (some m)) hsum
    cases o with
    | none => exact ho h0
    | some m => exact ho (this m)
  refine ⟨c none, fun m => - c (some m), hn, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hsum

theorem lifts_change {p q g : ℕ} (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (π π₀ : Fin p ⊕ Fin q → Fin g → ℂ) (S S₀ Tm : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hT : IsLinearMap ℂ T) (hH : Hm.IsHermitian)
    (hHp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (hS : S.det ≠ 0) (hS₀ : S₀.det ≠ 0)
    (hV : LinearIndependent ℂ V) (hW : LinearIndependent ℂ W)
    (hVs : ∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) (hWs : ∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W))
    (hVs₀ : ∀ n, T (π₀ n) ∈ Submodule.span ℂ (Set.range V)) (hWs₀ : ∀ n, T' (π₀ n) ∈ Submodule.span ℂ (Set.range W))
    (hF : ∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n)
    (hF₀ : ∀ m n, hermForm Hm (T (π₀ m)) (T (π₀ n)) - star (hermForm Hm (T' (π₀ m)) (T' (π₀ n))) = 2 * Complex.I * S₀ m n)
    (hc : ∀ m, T (π m) = ∑ k, Tm m k • T (π₀ k)) (hc' : ∀ m, T' (π m) = ∑ k, star (Tm m k) • T' (π₀ k)) :
    Tm.det ≠ 0 ∧ ∃ (C C₀ : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B Fm₀ B₀ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a, T (∑ m, C a m • π m) = V a) ∧ (∀ n, T' (π n) = ∑ j, B j n • W j) ∧ (∀ j n, ∑ m, Fm j m * S m n = B j n) ∧
      (∀ a, T (∑ m, C₀ a m • π₀ m) = V a) ∧ (∀ n, T' (π₀ n) = ∑ j, B₀ j n • W j) ∧
      (∀ j n, ∑ m, Fm₀ j m * S₀ m n = B₀ j n) ∧ (Matrix.fromRows C Fm).det ≠ 0 ∧
      (Matrix.fromRows C₀ Fm₀).det = (Matrix.fromRows C Fm).det * Tm.det := by
  obtain ⟨⟨Fm, B, d⟩, ⟨h1, h2, h3, ⟨C, hC⟩, h5⟩, -⟩ :=
    GlobalTheory.T.hermitian_period_linear_algebra p q g T T' V W π S Hm hT hH hHp hS hV hW hVs hWs hF
  obtain ⟨⟨Fm₀, B₀, d₀⟩, ⟨k1, k2, k3, -, k5⟩, -⟩ :=
    GlobalTheory.T.hermitian_period_linear_algebra p q g T T' V W π₀ S₀ Hm hT hH hHp hS₀ hV hW hVs₀ hWs₀ hF₀
  simp only at h1 h2 h3 hC h5 k1 k2 k3 k5
  have lin : ∀ (c : Fin p ⊕ Fin q → ℂ) (x : Fin p ⊕ Fin q → Fin g → ℂ), T (∑ m, c m • x m) = ∑ m, c m • T (x m) := by
    intro c x
    have := map_sum (hT.mk' T) (fun m => c m • x m) Finset.univ
    simpa using this

  have hmat : S = Tm * S₀ * Tmᴴ := by
    ext m n
    have e0 := hF m n
    rw [hc m, hc n, hc' m, hc' n] at e0
    simp only [hf_sum_left, hf_sum_right, star_sum, star_mul', star_star, Finset.mul_sum] at e0
    have e1 : (2 * Complex.I) * (Tm * S₀ * Tmᴴ) m n = 2 * Complex.I * S m n := by
      rw [← e0, ← Finset.sum_sub_distrib]
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hF₀ j i
      linear_combination (- (Tm m j * star (Tm n i))) * this
    have h2I : (2 * Complex.I) ≠ 0 := by simp
    exact (mul_left_cancel₀ h2I e1).symm
  have hdetH : Tmᴴ.det = star Tm.det := Matrix.det_conjTranspose Tm
  have hTdet : Tm.det ≠ 0 := by
    intro h0
    apply hS
    rw [hmat, Matrix.det_mul, Matrix.det_mul, h0]
    simp
  have hTH : Tmᴴ.det ≠ 0 := by
    rw [hdetH]; simpa using hTdet
  have hBm : B = B₀ * Tmᴴ := by
    ext j n
    have e0 : ∑ j, (B j n - (B₀ * Tmᴴ) j n) • W j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1 n, hc' n, sub_eq_zero]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [k1 k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hW _ e0 j)
  have hFS : Fm * S = B := by
    ext j n
    simpa [Matrix.mul_apply] using h2 j n
  have hFS₀ : Fm₀ * S₀ = B₀ := by
    ext j n
    simpa [Matrix.mul_apply] using k2 j n
  have hFm : Fm * Tm = Fm₀ := by
    have a1 : (Fm * Tm * S₀) * Tmᴴ = (Fm₀ * S₀) * Tmᴴ := by
      rw [hFS₀, ← hBm, ← hFS, hmat]
      simp only [Matrix.mul_assoc]
    have iTH : IsUnit Tmᴴ.det := isUnit_iff_ne_zero.2 hTH
    have iS : IsUnit S₀.det := isUnit_iff_ne_zero.2 hS₀
    have a2 : Fm * Tm * S₀ = Fm₀ * S₀ := by
      have := congrArg (· * Tmᴴ⁻¹) a1
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ iTH] using this
    have := congrArg (· * S₀⁻¹) a2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ iS] using this
  have hC₀ : ∀ a, T (∑ m, (C * Tm) a m • π₀ m) = V a := by
    intro a
    rw [← hC a, lin, lin]
    simp only [hc, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  have hd : d ≠ 0 := h3
  have hd' : (Matrix.fromRows C Fm).det = d := h5 C hC
  refine ⟨hTdet, C, C * Tm, Fm, B, Fm₀, B₀, hC, h1, h2, hC₀, k1, k2, by rw [hd']; exact hd, ?_⟩
  rw [← hFm, ← Matrix.fromRows_mul, Matrix.det_mul]

end GlobalTheory.CompanionTheory.Ar.Flat.Ratio

namespace GlobalTheory.CompanionTheory.Ar.Flat.Ratio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tyPart_add {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty σ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem tyPart_row {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (σ : E →+* ℂ) {I : Type} [Fintype I] (e : I → D.La) (x : D.La) (n : 𝓞 E) (c : I → 𝓞 E) (hn : n ≠ 0)
    (h : n • x = ∑ m, c m • e m) :
    tyPart ty σ (P x) = ∑ m, (σ (c m : E) / σ (n : E)) • tyPart ty σ (P (e m)) := by
  have hσ : σ (n : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hn
  funext k
  simp only [tyPart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hk
  · have e1 := congrFun (congrArg P h) k
    rw [hP.1, map_sum, Finset.sum_apply] at e1
    simp only [hP.1, hk] at e1
    rw [eq_comm, ← mul_right_inj' hσ, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  · simp

end GlobalTheory.CompanionTheory.Ar.Flat.Ratio

open GlobalTheory.CompanionTheory.Ar.Flat.Ratio in

theorem GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : ℂ, ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i _ h1 h2 hU
  obtain ⟨e, ρ, he, hc⟩ := h1.flat
  obtain ⟨e₀, ρ₀, he₀, hc₀⟩ := h2.flat
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hcard' : Fintype.card (Fin D.p ⊕ Fin D.q) = Module.finrank (𝓞 E) (FU.Di i).La := by
    rw [hcard, (FU.Di i).rank]
  haveI := (FU.Di i).fin
  choose n cf hn hrow using fun m => exists_row e₀ he₀ hcard' (e m)
  set Tm : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m k => τ (cf m k : E) / τ (n m : E) with hTm
  refine ⟨ρ * Tm.det / ρ₀, fun y v w hfr => ?_⟩
  obtain ⟨P, hP, hy⟩ := hU y hfr.1 hfr.2.1
  have hfv := hfr.2.2.1
  have hfw := hfr.2.2.2
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ τ D.p v hP hy (fun a => rfl) hfv
  obtain ⟨W, hWd, hWl, hWs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ) D.q w hP hy
    (fun a => rfl) hfw
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty P Hm hP hHh hHi
  have hSdet : ∀ e' : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e' →
      (Matrix.of fun m n => τ (sesq (FU.Di i) (e' m) (e' n))).det ≠ 0 := by
    intro e' he'
    have := hd 0 _ e' hcard he'
    have h2 : (Matrix.of fun m n => τ (sesq (FU.Di i) (e' m) (e' n))) =
        (Matrix.of fun m n => sesq (FU.Di i) (e' m) (e' n)).map τ := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 this
  obtain ⟨hTdet, C, C₀, Fm, B, Fm₀, B₀, a1, a2, a3, b1, b2, b3, hdet, hrel⟩ :=
    lifts_change (tyPart ty τ) (tyPart ty (ComplexEmbedding.conjugate τ)) V W (fun m => P (e m)) (fun m => P (e₀ m)) _ _ Tm Hm
      (tyPart_add ty τ) hHh hHp (hSdet e he) (hSdet e₀ he₀) hVl hWl (fun _ => hVs _) (fun _ => hWs _) (fun _ => hVs _)
      (fun _ => hWs _) (fun m n => hs τ _ _) (fun m n => hs τ _ _)
      (fun m => tyPart_row hP τ e₀ (e m) (n m) (cf m) (hn m) (hrow m))
      (fun m => by
        rw [tyPart_row hP (ComplexEmbedding.conjugate τ) e₀ (e m) (n m) (cf m) (hn m) (hrow m)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hTm, ComplexEmbedding.conjugate_coe_eq])
  have c1 := hc P y v w V W C Fm B hP hy hfr (fun a => (hVd a _).2 rfl) (fun j => (hWd j _).2 rfl) a1 a2 a3
  have c2 := hc₀ P y v w V W C₀ Fm₀ B₀ hP hy hfr (fun a => (hVd a _).2 rfl) (fun j => (hWd j _).2 rfl) b1 b2 b3
  have hφ₀ : φ₀ ℂ y v w ≠ 0 := h2.line.ne ℂ _ y v w hfr
  have hρ₀ : ρ₀ ≠ 0 := by
    rw [← c2, hrel]
    exact mul_ne_zero hφ₀ (mul_ne_zero hdet hTdet)
  rw [← c1, ← c2, hrel]
  field_simp
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_gen_frame_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : ℂ, ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

section Comb

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem epsMul_zero_eq : GlobalTheory.CompanionTheory.Ar.epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsMul_one_eq : GlobalTheory.CompanionTheory.Ar.epsMul (1 : R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem comp_one_over {Y Z M : Over S} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  exact MonObj.comp_one f

theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {n : ℕ} (u : Fin n → M) (j : Fin n),
    (∀ i, i ≠ j → u i = 1) → (List.ofFn u).prod = u j := by
  intro n
  induction n with
  | zero => intro u j; exact j.elim0
  | succ n ih =>
    intro u j hu
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1 := List.prod_eq_one fun x hx => by
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hu _ (Fin.succ_ne_zero i)
      rw [h1, _root_.mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      rw [hu 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => u i.succ) j' fun i hi => hu _ fun h => hi (Fin.succ_injective _ h)

theorem isComb_single {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (w : Fin n → (epsAt x ⟶ G))
    (hw : ∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (w i)) (j : Fin n) : GlobalTheory.CompanionTheory.Ar.Fl.IsComb (Pi.single j 1) w (w j) := by
  classical
  refine ⟨fun i => if i = j then w i else 1, fun i => ?_, ?_⟩
  · show Over.Hom.left (if i = j then w i else 1) = _
    by_cases hij : i = j
    · subst hij
      simp [epsMul_one_eq, spMap]
    · rw [if_neg hij, Pi.single_eq_of_ne hij, epsMul_zero_eq]
      have h1 := comp_one_over (M := G)
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))) rfl :
          GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ Over.mk x)
      rw [← h1, Over.comp_left, ← hw i]
      simp [spMap]
  · rw [prod_ofFn_single _ j fun i hi => if_neg hi, if_pos rfl]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem eq_mul_of_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (h : IsFramed U τ β y v w) (h' : IsFramed U τ β y v' w') {b : F}
    (hb : φ F y v' w' = b * φ₀ F y v' w') : φ F y v w = b * φ₀ F y v w := by
  have hv := h.2.2.1
  have hw := h.2.2.2
  have hv' := h'.2.2.1
  have hw' := h'.2.2.2
  have hvw' : IsFramed U τ β y v w' := ⟨h.1, h.2.1, hv, hw'⟩
  let A : Matrix (Fin D.p) (Fin D.p) F := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose
  have hA : ∀ a, IsComb (A a) v (v' a) := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose_spec
  let B : Matrix (Fin D.q) (Fin D.q) F := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose
  have hB : ∀ b, IsComb (B b) w (w' b) := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose_spec
  have hIv : ∀ a, IsComb ((1 : Matrix (Fin D.p) (Fin D.p) F) a) v (v a) := fun a => by
    have h1 : (1 : Matrix (Fin D.p) (Fin D.p) F) a = Pi.single a 1 :=
      funext fun b => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single v (fun i => (hv.1 i).1) a
  have hIw : ∀ b, IsComb ((1 : Matrix (Fin D.q) (Fin D.q) F) b) w' (w' b) := fun b => by
    have h1 : (1 : Matrix (Fin D.q) (Fin D.q) F) b = Pi.single b 1 :=
      funext fun b' => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single w' (fun i => (hw'.1 i).1) b
  have e1 := hφ.chg F β y v w v w' 1 B h hvw' hIv hB
  have e1₀ := hφ₀.chg F β y v w v w' 1 B h hvw' hIv hB
  have e2 := hφ.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  have e2₀ := hφ₀.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  rw [Matrix.det_one, _root_.mul_one] at e1 e1₀ e2 e2₀
  have hBne : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hφ.ne F β y v w' hvw' e1
  apply mul_right_cancel₀ hBne
  calc φ F y v w * B.det = φ F y v w' := e1.symm
    _ = φ F y v' w' * A.det := e2.symm
    _ = b * (φ₀ F y v' w' * A.det) := by rw [hb, _root_.mul_assoc]
    _ = b * φ₀ F y v w * B.det := by rw [e2₀, e1₀, _root_.mul_assoc]

theorem ratio_at {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {a : ℂ}
    (ha : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w)
    {k : Type} [Field k] {β₀ : c.F →+* k} {y₀ : Sp k ⟶ Xo.XF c} {v₀ : Vecs y₀ D.p} {w₀ : Vecs y₀ D.q}
    (h₀ : IsFramed U τ β₀ y₀ v₀ w₀)
    (hb : ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p)
      (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧
        (∀ a, (v' a).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (v₀ a).left) ∧
        ∀ b, (w' b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (w₀ b).left)
    (j : k →+* ℂ) (hj : j.comp β₀ = algebraMap c.F ℂ) : j (φ k y₀ v₀ w₀) = a * j (φ₀ k y₀ v₀ w₀) := by
  obtain ⟨v', w', hfr, hv', hw'⟩ := hb ℂ j
  have hfr' : IsFramed U τ (algebraMap c.F ℂ) (spMap j ≫ y₀) v' w' := by
    rw [← hj]
    exact hfr
  have e := ha _ v' w' hfr'
  rw [hφ.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw',
    hφ₀.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw'] at e
  exact e

theorem flatGen_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  obtain ⟨a, ha⟩ := GlobalTheory.T.flat_gen_frame_independent E H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  have hL := hφ.line
  have hL₀ := hφ₀.line
  by_cases hex : ∃ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ (algebraMap c.F ℂ) y v w
  · obtain ⟨y1, v1, w1, h1⟩ := hex
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ ℂ (algebraMap c.F ℂ) y1 v1 w1 h1
    have hr := ratio_at hL hL₀ ha h₀ hb j hj
    have hne₀ : j (φ₀ k y₀ v₀ w₀) ≠ 0 := (map_ne_zero j).2 (hL₀.ne k β₀ y₀ v₀ w₀ h₀)
    have hfix : ∀ σ' : ℂ ≃+* ℂ, (∀ x ∈ c.F, σ' x = x) → σ' a = a := by
      intro σ' hσ'
      have hj' : (σ'.toRingHom.comp j).comp β₀ = algebraMap c.F ℂ := by
        refine RingHom.ext fun x => ?_
        have hx := RingHom.congr_fun hj x
        simp only [RingHom.comp_apply] at hx ⊢
        rw [hx]
        exact hσ' _ x.2
      have hr' := ratio_at hL hL₀ ha h₀ hb _ hj'
      simp only [RingHom.comp_apply] at hr'
      rw [hr, map_mul] at hr'
      exact mul_right_cancel₀ ((map_ne_zero _).2 hne₀) hr'
    have haF : a ∈ c.F := GlobalTheory.T.fixed_by_automorphisms_mem_field c.F a c.fin hfix
    refine ⟨⟨a, haF⟩, ?_, ?_⟩
    · intro h0
      have ha0 : a = 0 := congrArg Subtype.val h0
      apply hL.ne k β₀ y₀ v₀ w₀ h₀
      apply j.injective
      rw [hr, map_zero, ha0, zero_mul]
    · intro F _ β y v w hfr
      obtain ⟨k', _, β₀', y₀', v₀', w₀', f', j', h₀', hfβ', hj'', hy', hb'⟩ :=
        GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
      subst hy'
      subst hfβ'
      have hr2 := ratio_at hL hL₀ ha h₀' hb' j' hj''
      have hk : φ k' y₀' v₀' w₀' = β₀' ⟨a, haF⟩ * φ₀ k' y₀' v₀' w₀' := by
        apply j'.injective
        rw [map_mul, hr2]
        congr 1
        have hx := RingHom.congr_fun hj'' ⟨a, haF⟩
        simp only [RingHom.comp_apply] at hx
        rw [hx]
        rfl
      obtain ⟨v', w', hfr', hv', hw'⟩ := hb' F f'
      have n1 := hL.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      have n2 := hL₀.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      refine eq_mul_of_frames hL hL₀ hfr hfr' (b := f' (β₀' ⟨a, haF⟩)) ?_
      rw [n1, n2, hk, map_mul]
  · refine ⟨1, one_ne_zero, fun F _ β y v w hfr => ?_⟩
    exfalso
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
    obtain ⟨v', w', hfr', -, -⟩ := hb ℂ j
    rw [hj] at hfr'
    exact hex ⟨_, v', w', hfr'⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_gen_frame_complex_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isGeom_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → Z.IsGeom := by
  exact @PositivityTheory.Xgn.geometric_of_periods

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_uniformised_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → Z.IsGeom := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.isGeom_of_period
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.TopA

theorem exists_padic_emb (F : IntermediateField ℚ ℂ) [NumberField F] (p : Nat.Primes) :
    Nonempty (F →+* ℂ_[p]) :=
  ⟨(IsAlgClosed.lift (M := ℂ_[p]) (R := ℚ) (S := F)).toRingHom⟩

theorem eq_of_clopen_irred {X : Type*} [TopologicalSpace X] {U U' : Set X} (hU : IsClopen U)
    (hUi : IsIrreducible U) (hU' : IsClopen U') (hUi' : IsIrreducible U') {u : X} (hu : u ∈ U) (hu' : u ∈ U') :
    U = U' :=
  (hUi.isConnected.isPreconnected.subset_isClopen hU' ⟨u, hu, hu'⟩).antisymm
    (hUi'.isConnected.isPreconnected.subset_isClopen hU ⟨u, hu', hu⟩)

theorem finite_primes_dvd {n : ℕ} (hn : n ≠ 0) : {p : Nat.Primes | (p : ℕ) ∣ n}.Finite :=
  ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun p hp =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp

theorem model_hyp {K : Type} [Field K] (V : ValuationSubring K) [IsDiscreteValuationRing V] :
    Function.Injective V.subtype ∧ IsNoetherianRing V ∧
      ∀ x : K, ∃ a b : V, V.subtype b ≠ 0 ∧ x * V.subtype b = V.subtype a := by
  refine ⟨Subtype.val_injective, inferInstance, fun x => ?_⟩
  rcases V.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, by simp, by simp [hx]⟩
    · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simp [hx]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_place {l : Level H} (c : Coeff l) [NumberField c.F] (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) :
    ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧ IsDiscreteValuationRing (c.V W) ∧
      ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W := by
  obtain ⟨W, hp, hW⟩ := GlobalTheory.T.padic_embedding_valuation_subring c.F p κ
  obtain ⟨V, hV, hκ, -, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p κ
  have hmem : ∀ x : c.F, x ∈ c.V W ↔ ‖κ x‖ ≤ 1 := fun x => (hW x).symm
  have heq : c.V W = V := by ext x; rw [hmem, hκ]
  refine ⟨W, hp, ?_, fun x => (hmem x).symm⟩
  rw [heq]; exact hV

theorem exists_cpt {D : Datum H} {l : Level H} (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    {U : Set (Xo.XF c)} (hU : IsClopen U) (hUi : IsIrreducible U) : Nonempty (CptOver Y U) := by
  obtain ⟨u, hu⟩ := hUi.nonempty
  obtain ⟨U', Z, hu', hc, hi⟩ := GlobalTheory.T.exists_clopen_irreducible_cpt E H D l Xo c O β Y u hβ
  rw [eq_of_clopen_irred hU hUi hc hi hu hu']
  exact ⟨Z⟩

theorem local_gen (hA0 : FlatLineGenerator) (hA1 : FlatLineGeneratorComponent) (hC : FinConstAll) {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (U : Set (Xo.XF c)) (τ : E →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (hpq : 1 ≤ D.p + D.q)
    (hτ : τ (H.rt : E) = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hU : IsClopen U) (hUi : IsIrreducible U)
    (hP : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P))
    (W : ValuationSubring ℂ) [IsDiscreteValuationRing (c.V W)] (Y : Model Xo c (c.V W).subtype)
    (hSF : Y.SplitFibres) (hN3 : Y.N3) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (hκ : ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W) :
    ∃ φ : FrameFn Xo c, IsFlatGen U τ φ FU i ∧ (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧
      ∃ t, HasFinNorm U τ φ p κ t := by
  obtain ⟨Z⟩ := exists_cpt Xo c Y (model_hyp (c.V W)) hU hUi
  have hG : Z.IsGeom := GlobalTheory.T.generic_fibre_uniformised_frame E H D l Xo c _ _ Y U Z g ty FU i hty (fun y hy hr => (hP y hy).1 hr)
  obtain ⟨φ, hl, hf, -⟩ := hA0 E H D l Xo c _ _ Y U Z τ (model_hyp (c.V W)) hpq hτ hG
  obtain ⟨hinf, hfg⟩ := hA1 E H D l Xo c _ _ Y U Z τ φ (model_hyp (c.V W)) hpq hτ hG hl hf
  refine ⟨φ, hfg g ty FU i hty (fun P y hPer hu hy => (hP y hy).2 ⟨P, hPer, hu⟩), fun s => ?_, ?_⟩
  · obtain ⟨t, ht, -⟩ := hinf s
    exact ⟨t, ht⟩
  · refine hC E H D l Xo c _ _ Y U Z τ p κ φ hτ Subtype.val_injective (fun x => (hκ x).trans ?_) hSF hN3 hG hf hl
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem hasFinNorm_of_eq {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {U : Set (Xo.XF c)}
    {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (hl : IsLineFn U τ φ) {a : c.F} (ha : a ≠ 0)
    (he : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ' F y v w = β a * φ F y v w)
    {p : Nat.Primes} {κ : c.F →+* ℂ_[p]} {t : ℝ} (ht : HasFinNorm U τ φ' p κ t) :
    HasFinNorm U τ φ p κ (t - Real.log ‖κ a‖) := by
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht V K j β y v w T tK m m' hj hjβ hfr hv hw
  have hja : j (β a) = κ a := by rw [← hjβ]; rfl
  have h2 : ‖κ a‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero κ).mpr ha)
  have h3 : ‖j (φ K y v w)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero j).mpr (hl.ne K β y v w hfr))
  rw [he K β y v w hfr, map_mul, hja, norm_mul, Real.log_mul h2 h3] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat.TopA

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.TopA in

theorem thmFlatA_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  intro hI hA0 hA1 _ E _ _ _ H D Xo l c _ U τ g ty FU i hpq hτ hg hty hU hUi hP
  have hC : FinConstAll := GlobalTheory.T.finite_constant_all_holds
  obtain ⟨-, hI'⟩ := hI
  obtain ⟨Ys, hYs, -⟩ := hI' E H D hpq Xo
  have key : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ φ : FrameFn (Xo l) c, IsFlatGen U τ φ FU i ∧
      (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧ ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨W, hpW, hdvr, hκ⟩ := exists_place c p κ
    haveI := hdvr
    obtain ⟨-, hYi⟩ := hYs p W p.2 hpW
    obtain ⟨hSF, hN3, -⟩ := hYi ⟨l, c, hg p p.2⟩
    exact local_gen hA0 hA1 hC U τ FU i hpq hτ hty hU hUi hP W (Ys p W p.2 hpW ⟨l, c, hg p p.2⟩) hSF hN3 p κ hκ
  obtain ⟨κ₀⟩ := exists_padic_emb c.F ⟨2, Nat.prime_two⟩
  obtain ⟨φ, hφ, hinf, -⟩ := key _ κ₀
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨φ', hφ', -, t, ht⟩ := key p κ
    obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ φ' φ g ty FU i hty hφ' hφ
      (fun y hy hr => (hP y hy).1 hr)
    exact ⟨_, hasFinNorm_of_eq hφ.line ha he ht⟩
  let N : LogNorms c.F := ⟨fun s => (hinf s).choose, fun p κ => (hfin p κ).choose -
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  have hN : HasNorms U τ φ N := ⟨fun s => (hinf s).choose_spec, fun p κ => by
    simp only [N, sub_add_cancel]
    exact (hfin p κ).choose_spec⟩
  refine ⟨φ, N, hφ, hN, ?_⟩
  obtain ⟨n, hn, hn0⟩ := GlobalTheory.T.finite_norm_zero_outside_denom E H D l (Xo l) c U τ φ hτ hU.isOpen hUi.nonempty hφ.line
  have hS := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  refine (((finite_primes_dvd hn.ne').union (finite_primes_dvd H.d_prime.ne_zero)).union hS).subset ?_
  rintro p ⟨ι₀, hι⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  obtain ⟨-, -, -, -, hd⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p ι₀
  have hd' : ‖((H.d : ℕ) : ℂ_[p])‖ = 1 := by simpa using hd H.d h2
  have h0 := hn0 p ι₀ _ h1 (hN.2 p ι₀)
  rw [h3 (ι₀.comp (tauIn c τ)), hd', Real.log_one] at h0
  simp only [sub_zero, mul_zero, add_zero] at h0
  exact hι h0

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
