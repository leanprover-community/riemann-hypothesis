import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.FamilyPeriod
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem exists_embedding (K k : Type) [Field K] [Field k] [Countable K] [Countable k] (β : K →+* k) (s : K →+* ℂ) :
    ∃ j : k →+* ℂ, j.comp β = s := by
  letI := β.toAlgebra
  letI := s.toAlgebra
  obtain ⟨I₁, x, hx⟩ := exists_isTranscendenceBasis' K k
  obtain ⟨κ, z, hz⟩ := exists_isTranscendenceBasis' K ℂ
  have hI₁ : Countable I₁ := hx.1.injective.countable
  have hκ : Cardinal.mk ℂ = Cardinal.mk κ := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz
      (Cardinal.mk_le_aleph0_iff.2 inferInstance) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    exact this
  have hle : Cardinal.mk I₁ ≤ Cardinal.mk κ := by
    rw [← hκ, Cardinal.mk_complex]
    exact (Cardinal.mk_le_aleph0_iff.2 hI₁).trans Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := hle
  have hz' : AlgebraicIndependent K (z ∘ e) := hz.1.comp e e.injective
  letI : Algebra (MvPolynomial I₁ K) k := (MvPolynomial.aeval x : MvPolynomial I₁ K →ₐ[K] k).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial I₁ K) ℂ := (MvPolynomial.aeval (z ∘ e) : MvPolynomial I₁ K →ₐ[K] ℂ).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial I₁ K) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hx.1
  haveI : FaithfulSMul (MvPolynomial I₁ K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hz'
  haveI : Algebra.IsAlgebraic (MvPolynomial I₁ K) k := by
    haveI := hx.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range x)) (B := k) hx.1.aevalEquiv
      (RingHom.id k) hx.1.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hx.1.algebraMap_aevalEquiv p)
  let j : k →ₐ[MvPolynomial I₁ K] ℂ := IsAlgClosed.lift
  refine ⟨j.toRingHom, RingHom.ext fun a => ?_⟩
  have h := j.commutes (MvPolynomial.C a)
  have h1 : algebraMap (MvPolynomial I₁ K) k (MvPolynomial.C a) = β a := MvPolynomial.aeval_C x a
  have h2 : algebraMap (MvPolynomial I₁ K) ℂ (MvPolynomial.C a) = s a := MvPolynomial.aeval_C (z ∘ e) a
  rw [h1, h2] at h
  exact h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_bij (hξ : IsCptGen ξ) (q : X) (hq : q = genPt ξ) (h : genPt ξ ⤳ q) :
    Function.Bijective (genMap ξ ⟨q, h⟩) := by
  subst hq
  have : X.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  refine ⟨hξ.inj _, ?_⟩
  unfold genMap
  simp only [this]
  exact hξ.bij.2

theorem countable_of_tie {κ : Type} [Finite κ] {x : κ → Ω} (h : CoordTie ℤ ξ x) : Countable Ω := by
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Countable (MvPolynomial κ ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  refine Function.Surjective.countable (f := fun a : MvPolynomial κ ℤ × MvPolynomial κ ℤ =>
    MvPolynomial.aeval (fun j => x j / x c) a.1 / MvPolynomial.aeval (fun j => x j / x c) a.2) fun a => ?_
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c _ hc a).1 ((genMap_bij h.gen _ rfl _).2 a)
  rw [Algebra.adjoin_range_eq_range_aeval] at hs hsa
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := hsa
  refine ⟨(g, f), ?_⟩
  have hf' : MvPolynomial.aeval (fun j => x j / x c) f = s := hf
  have hg' : MvPolynomial.aeval (fun j => x j / x c) g = s * a := hg
  simp only [hf', hg']
  exact mul_div_cancel_left₀ _ hu.1

theorem cancel_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] {a b : Ω →+* R} (h : spMap a ≫ ξ = spMap b ≫ ξ) :
    a = b := by
  have e := LieTangent.spec_genMap ξ ⟨genPt ξ, specializes_rfl⟩
  have h' : (spMap a ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ =
      (spMap b ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ := by
    rw [Category.assoc, Category.assoc, e, h]
  rw [cancel_mono, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp] at h'
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  refine RingHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := (genMap_bij hξ _ rfl specializes_rfl).2 t
  exact DFunLike.congr_fun h2 s

theorem factor_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (V : Sp R ⟶ X)
    (hV : centre V = genPt ξ) : ∃ δ : Ω →+* R, spMap δ ≫ ξ = V := by
  have h : genPt ξ ⤳ centre V := hV ▸ specializes_rfl
  let e := RingEquiv.ofBijective _ (genMap_bij hξ _ hV h)
  refine ⟨(Scheme.stalkClosedPointTo V).hom.comp e.symm.toRingHom, ?_⟩
  have e1 := LieTangent.spec_genMap ξ ⟨centre V, h⟩
  have e2 := LieTangent.spec_centre V
  refine (congrArg (spMap _ ≫ ·) e1.symm).trans (Eq.trans ?_ e2)
  rw [← Category.assoc, spMap, ← Spec.map_comp]
  congr 2
  ext s
  exact congrArg (Scheme.stalkClosedPointTo V).hom (e.symm_apply_apply s)

theorem hom_dual_ext {F₀ F : Type} [Field F₀] [Field F] [CharZero F] (i : F₀ →+* F)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank F₀ F)) {δ δ' : F →+* DualNumber ℂ} (h : δ.comp i = δ'.comp i)
    (h' : ∀ x, (δ x).fst = (δ' x).fst) : δ = δ' := by
  letI := i.toAlgebra
  letI := (δ.comp i).toAlgebra
  haveI : CharZero F₀ := i.charZero
  haveI : Module.Finite F₀ F := Module.finite_of_finrank_pos hfin
  have hu : Algebra.FormallyUnramified F₀ F := Algebra.FormallyUnramified.of_isSeparable F₀ F
  have h := Algebra.FormallyUnramified.ext' (R := F₀) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    { δ with commutes' := fun _ => rfl } { δ' with commutes' := fun r => (DFunLike.congr_fun h r).symm } h'
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem const_of_finite {Y : Scheme.{0}} {Ω₀ : Type} [Field Ω₀] [CharZero Ω] {ξ₀ : Sp Ω₀ ⟶ Y} (hξ : IsCptGen ξ)
    (hξ₀ : IsCptGen ξ₀) {f : X ⟶ Y} {i : Ω₀ →+* Ω} (hf : ξ ≫ f = spMap i ≫ ξ₀)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank Ω₀ Ω)) {φ : Ω →+* ℂ} {V : Sp (DualNumber ℂ) ⟶ X}
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V = spMap φ ≫ ξ)
    (h2 : V ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (spMap φ ≫ ξ) ≫ f) :
    V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ ≫ ξ := by
  have hc : centre V = genPt ξ := by
    have a1 : centre (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V) = centre V := by
      exact congrArg V (Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    rw [← a1, h1]
    exact SheetDecomposition.CovSch.centre_spMap φ ξ
  obtain ⟨δ, rfl⟩ := factor_gen hξ V hc
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have e1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ = φ := cancel_gen hξ (by rw [sc, Category.assoc, h1])
  have e2 : δ.comp i = ((algebraMap ℂ (DualNumber ℂ)).comp φ).comp i := cancel_gen hξ₀ (by
    rw [sc, sc _ ((algebraMap ℂ (DualNumber ℂ)).comp φ), sc φ, Category.assoc, Category.assoc, Category.assoc, ← hf]
    simpa only [Category.assoc] using h2)
  rw [hom_dual_ext i hfin e2 fun x => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using DFunLike.congr_fun e1 x, sc, Category.assoc]

theorem fderiv_value_zero (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {n : ℕ} {B : Set (Fin n → ℂ)}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hp : IsHolTo B p) (h0 : 0 ∈ B) (hc : centre (p 0) = centre ξ) {v : Fin n → ℂ}
    (hv : IsDerivAt0 p v (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0)) {a : Ω} {r : (Fin n → ℂ) → ℂ}
    (hr : ∀ᶠ u in nhds 0, ValAt ξ (p u) a (r u)) : fderiv ℂ r 0 v = 0 := by
  obtain ⟨g, rfl⟩ := hξ.bij.2 a
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have hU0 : ⊤ ≤ p 0 ⁻¹ᵁ U := (SheetDecomposition.CovSch.top_le_iff _ _).2 (hc ▸ hU)
  have he : r =ᶠ[nhds 0] fun u => valAt' (p u) U s := by
    filter_upwards [hr, GlobalTheory.LocalLift.hol_eventually_mem hp h0 hU0] with u h1 h2
    have h3 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h2.2
    rw [SheetDecomposition.CovSch.valAt'_eq _ _ h3]
    exact SheetDecomposition.CovSch.v_unique hξ h1 (SheetDecomposition.CovSch.valAt_sec (hall _) U h3 hU s)
  have h1 : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0) ⁻¹ᵁ U := fun q _ => hU0 (Set.mem_univ _)
  rw [he.fderiv_eq, ← hv.2 U h1 s]
  have := GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (p 0) U hU0 h1 s
  refine (congrArg TrivSqZeroExt.snd this).trans ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end PositivityTheory.Xgp.c_bm_exists_period
end
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

open PositivityTheory.Xgp.c_bm_exists_period FramePeriods in
theorem PositivityTheory.Xgp.t_c_bm_exists_immersion : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  intro hG E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie hp1 _ d hd Rb s hInt hcl q O F hO hcov hF hgood
  have hpq : 1 ≤ D.p + D.q := by omega
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  haveI : Countable M.Ω := countable_of_tie 𝔐.tie
  haveI : Countable c.F := 𝔐.cst.injective.countable
  obtain ⟨φ, hφ⟩ := exists_embedding c.F M.Ω 𝔐.cst c.F.val.toRingHom
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  obtain ⟨w, hw⟩ := tp.2.1 (spMap φ ≫ 𝔐.ξ) (𝔐.all _)
  have htop : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun z h => by simpa using h.2 1 trivial
  obtain ⟨x, a, ha, hxa⟩ := Rb.surj w ((GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).2 ⟨_, 𝔐.all _, hw⟩) (htop w)
  have hz : CoordsAt 𝔐.ξ M.x (spMap φ ≫ 𝔐.ξ) (Rb.lift x x) :=
    ((tp.2.2 _ _ (𝔐.all _) hw).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), hxa⟩
  have hcz : centre (spMap φ ≫ 𝔐.ξ) = centre 𝔐.ξ := SheetDecomposition.CovSch.centre_spMap φ 𝔐.ξ
  have hx : x ∉ bdry s := (hInt x _ hz).2 (by
    change centre _ ∈ _
    rw [hcz]
    exact (GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y S M.Ω _ _ M.x 𝔐 (FaithfulSMul.algebraMap_injective _ _)).1)
  obtain ⟨l₀, hl₀⟩ := hcov x
  obtain ⟨j, r, p, hr, hj, hwd, hp⟩ := exists_family (𝔐 := 𝔐) Rb hcl hx
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all _ _ _ p
    Metric.isOpen_ball hwd fun u hu => (hp u hu).2.1
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) _ p hhol
  have hint : ∀ u ∈ Metric.ball 0 1, 𝔐.Interior (p u) := fun u hu => (hInt _ _ (hp u hu).2.2).1 (hp u hu).1
  have hb0 : 0 ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) 1 := Metric.mem_ball_self one_pos
  have hc0 : CoordsAt 𝔐.ξ M.x (p 0) (Rb.lift x x) := by
    have := (hp 0 hb0).2.1
    rwa [smul_zero, add_zero, (Rb.A.chart j).left_inv hj] at this
  have hp0 : p 0 = spMap φ ≫ 𝔐.ξ :=
    (tp.1 _ hz.1 (tp.2.2 _ _ (𝔐.all _) hz).1).unique ⟨𝔐.all _, hc0⟩ ⟨𝔐.all _, hz⟩
  have hτ₀ : τ₀ = c.F.val.toRingHom := by
    have h1 := hτ 0 hb0
    rw [hp0, Category.assoc, 𝔐.cst_over, spMap, spMap, spMap, ← Spec.map_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    rw [← hφ]
    exact IsFractionRing.ringHom_ext (A := 𝓞 c.F) fun t => (DFunLike.congr_fun h2 t).symm
  obtain ⟨ρ, B, Pi, Γ, hρ, hρ', hB, h0, hsub, hPi, hgr, hder⟩ := family_period hG.1.2.2.1 tie hpq (hF l₀) p τ₀
    (by rw [hτ₀]; rfl) hhol hτ hint (by rw [ptIdeal_centre hc0]; exact hgood l₀ x hl₀)
  obtain ⟨h1, h2, h3⟩ := to_manifold Rb.A j hj (r := (r : ℂ) * ρ) hB h0
  have hne : (r : ℂ) * ρ ≠ 0 := by exact_mod_cast (mul_pos hr hρ).ne'
  have hback : ∀ x' ∈ (Rb.A.chart j).source, (Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • (ρ : ℂ) •
      (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x))) = x' := fun x' hx' => by
    rw [smul_smul (r : ℂ), smul_inv_smul₀ hne, add_sub_cancel, (Rb.A.chart j).left_inv hx']
  refine ⟨l₀, x, ⟨hl₀, hx⟩, _, fun τ x' => Pi τ (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x)), h2,
    ⟨h1, fun τ a b => h3 _ (hPi τ a b), fun τ x' hx' => ?_⟩, fun k hk v hv => ?_⟩
  · have hm := smul_mem_ball' hρ hρ' (hsub hx'.2)
    have hc := (hp _ hm).2.2
    rw [hback x' hx'.1] at hc
    simp only
    rw [baseGram, gramFn_eq hc (hint _ hm) (hgr τ _ hx'.2).1]
    exact (hgr τ _ hx'.2).2
  let ψ : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) :=
    fun t => ((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j ((Rb.A.chart k).symm t) - Rb.A.chart j x)
  have hkx : (Rb.A.chart k).symm (Rb.A.chart k x) = x := (Rb.A.chart k).left_inv hk
  have hψ0 : ψ (Rb.A.chart k x) = 0 := by simp only [ψ, hkx, sub_self, smul_zero]
  have hψ : DifferentiableAt ℂ ψ (Rb.A.chart k x) :=
    by
    have := ((Rb.A.holo k j _ ⟨(Rb.A.chart k).map_source hk, by rw [Set.mem_preimage, hkx]; exact hj⟩).differentiableAt.sub_const
      (Rb.A.chart j x)).const_smul (((r : ℂ) * ρ)⁻¹)
    exact this
  have chain : ∀ f : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → ℂ, DifferentiableAt ℂ f 0 →
      HasFDerivAt (fun t => f (ψ t)) ((fderiv ℂ f 0).comp (fderiv ℂ ψ (Rb.A.chart k x))) (Rb.A.chart k x) :=
    fun f hf => HasFDerivAt.comp _ (by rw [hψ0]; exact hf.hasFDerivAt) hψ.hasFDerivAt
  obtain ⟨V, hV1, hV2⟩ := hder (fderiv ℂ ψ (Rb.A.chart k x) v) fun τ a b h₁ h₂ => by
    have := hv τ a b h₁ h₂
    simp only [sub_self, smul_zero] at this
    convert this using 3
    ext a' b'
    exact (congrArg (· v) (chain _ ((hPi τ a' b').differentiableAt (hB.mem_nhds h0))).fderiv).symm
  have hV3 : V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 := by
    have e1 := hV1.1
    simp only [smul_zero] at e1
    rw [hp0] at e1 hV2 ⊢
    exact const_of_finite 𝔐.tie.gen 𝔐.gen₀ 𝔐.fn_over (hd.2 ▸ hd.1) e1 hV2
  choose pc hpc using hz.1
  have hball : ∀ᶠ u in nhds (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ), u ∈ Metric.ball 0 1 :=
    Metric.isOpen_ball.mem_nhds hb0
  let wv : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ := fun u =>
    Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • (ρ : ℂ) • u))
  have hwv0 : wv 0 = Rb.lift x x := by simp only [wv, smul_zero, add_zero, (Rb.A.chart j).left_inv hj]
  have hwv : ∀ q', DifferentiableAt ℂ (fun u => wv u q') 0 := fun q' => by
    have a1 := (differentiableOn_pi.1 hwd q').differentiableAt hball
    have a2 : DifferentiableAt ℂ (fun u : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ => (ρ : ℂ) • u) 0 := by
      fun_prop
    exact DifferentiableAt.comp (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) (by rw [smul_zero]; exact a1) a2
  have hne0 : ∀ k', wv 0 ⟨k', pc k'⟩ ≠ 0 := fun k' => by rw [hwv0]; exact (hpc k').ne_zero
  have hhol' : IsHolTo (Metric.ball 0 1) fun u => p ((ρ : ℂ) • u) :=
    GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all _ _ wv _ Metric.isOpen_ball
      (hwd.comp (by fun_prop) fun u hu => smul_mem_ball' hρ hρ' hu) fun u hu => (hp _ (smul_mem_ball' hρ hρ' hu)).2.1
  have hA : ∀ q', DifferentiableAt ℂ (fun u => affCoord pc (wv u) q') 0 ∧
      fderiv ℂ (fun u => affCoord pc (wv u) q') 0 (fderiv ℂ ψ (Rb.A.chart k x) v) = 0 := fun q' => by
    refine ⟨by
      simp only [affCoord, div_eq_mul_inv]
      exact (hwv q').mul ((hwv ⟨q'.1, pc q'.1⟩).inv (hne0 q'.1)), fderiv_value_zero 𝔐.tie.gen 𝔐.all hhol' hb0
      (by simp only [smul_zero]; rw [hp0, hcz]) (by simp only [smul_zero]; rw [← hV3]; exact hV1)
      (a := M.x q' / M.x ⟨q'.1, pc q'.1⟩) ?_⟩
    filter_upwards [hball, (hwv _).continuousAt.eventually_ne (hne0 q'.1)] with u hu hu'
    obtain ⟨t, ht, e⟩ := ((hp _ (smul_mem_ball' hρ hρ' hu)).2.1.2 q'.1 (pc q'.1) (IsUnit.mk0 _ hu')).2 q'.2
    have e' : wv u q' = t * wv u ⟨q'.1, pc q'.1⟩ := e
    rw [affCoord, e', mul_div_cancel_right₀ _ hu']
    exact ht
  have hker := Rb.immersion x (htop _) pc (fun k' => (hpc k').ne_zero) k hk
  have hev : (fun t => affCoord pc (Rb.lift x ((Rb.A.chart k).symm t))) =ᶠ[nhds (Rb.A.chart k x)]
      fun t q' => affCoord pc (wv (ψ t)) q' := by
    have hs : (Rb.A.chart j).source ∈ nhds ((Rb.A.chart k).symm (Rb.A.chart k x)) := by
      rw [hkx]; exact (Rb.A.chart j).open_source.mem_nhds hj
    filter_upwards [((Rb.A.chart k).continuousAt_symm ((Rb.A.chart k).map_source hk)).eventually hs] with t ht
    simp only [wv, ψ, hback _ ht]
  rw [hev.fderiv_eq, (hasFDerivAt_pi.2 fun q' => chain _ (hA q').1).fderiv] at hker
  rw [← Submodule.mem_bot ℂ, ← hker]
  exact funext fun q' => (hA q').2
end
