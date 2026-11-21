import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem coordTie_reindex {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite




end GlobalTheory.CompanionTheory.Ar.HodgeExists
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgField

theorem exists_compositum (κ Ω₁ Ω' : Type) [Field κ] [Field Ω₁] [Field Ω'] (i₁ : κ →+* Ω₁) (i₂ : κ →+* Ω')
    (h : i₂.Finite) :
    ∃ (Ω : Type) (_ : Field Ω) (a : Ω₁ →+* Ω) (b : Ω' →+* Ω), a.Finite ∧ a.comp i₁ = b.comp i₂ := by
  letI := i₁.toAlgebra
  letI := i₂.toAlgebra
  haveI : Module.Finite κ Ω' := h
  haveI : Module.Finite Ω₁ (TensorProduct κ Ω₁ Ω') := inferInstance
  haveI : Nontrivial (TensorProduct κ Ω₁ Ω') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct κ Ω₁ Ω')
  let q := Ideal.Quotient.mk m
  refine ⟨TensorProduct κ Ω₁ Ω' ⧸ m, Ideal.Quotient.field m,
    q.comp (algebraMap Ω₁ (TensorProduct κ Ω₁ Ω')),
    q.comp (Algebra.TensorProduct.includeRight : Ω' →ₐ[κ] TensorProduct κ Ω₁ Ω').toRingHom, ?_, ?_⟩
  · exact RingHom.Finite.comp (RingHom.Finite.of_surjective q Ideal.Quotient.mk_surjective)
      (RingHom.finite_algebraMap.2 inferInstance)
  · ext x
    have e : algebraMap Ω₁ (TensorProduct κ Ω₁ Ω') (i₁ x) = (1 : Ω₁) ⊗ₜ[κ] (i₂ x) := by
      have h1 : i₁ x = x • (1 : Ω₁) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
      have h2 : i₂ x = x • (1 : Ω') := by rw [Algebra.smul_def, _root_.mul_one]; rfl
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h1, h2,
        TensorProduct.smul_tmul]
    simp only [RingHom.comp_apply]
    rw [e]
    rfl

theorem exists_root (K : Type) [Field K] [CharZero K] (N : ℕ) (hN : N ≠ 0) :
    ∃ (L : Type) (_ : Field L) (j : K →+* L), j.Finite ∧ ∃ ζ : L, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN⟩
  haveI : NeZero ((N : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hN⟩
  haveI : Module.Finite K (CyclotomicField N K) := by
    first
      | exact IsCyclotomicExtension.finiteDimensional {N} K _
      | exact IsCyclotomicExtension.finite {N} K _
      | exact Polynomial.IsSplittingField.finiteDimensional _ (Polynomial.cyclotomic N K)
  exact ⟨CyclotomicField N K, inferInstance, algebraMap _ _, RingHom.finite_algebraMap.2 inferInstance,
    IsCyclotomicExtension.zeta N K _, IsCyclotomicExtension.zeta_spec N K _⟩

theorem fullTorsion_ext {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (j : Ω →+* Ω') {n : ℕ} (hf : FullTorsion G ξ n) :
    FullTorsion G (spMap j ≫ ξ) n := by
  intro k _ i g hg
  have hs : spMap (i.comp j) = spMap i ≫ spMap j := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : spMap i ≫ spMap j ≫ ξ = spMap (i.comp j) ≫ ξ := by
    rw [hs, Category.assoc]
  revert g
  rw [e]
  intro g hg
  obtain ⟨x, hx⟩ := hf k (i.comp j) g hg
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  refine ⟨Over.homMk (spMap j ≫ x.left) ?_, ?_⟩
  · simp only [Over.mk_hom, Category.assoc, hxw]
  · show g.left = spMap i ≫ spMap j ≫ x.left
    rw [hx, hs]
    exact Category.assoc _ _ _

theorem exists_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : X)
    (h : genPt ξ = e) : ∃ i : X.residueField e →+* Ω, ξ = spMap i ≫ X.fromSpecResidueField e := by
  subst h
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ξ)).hom,
    ((Scheme.SpecToEquivOfField Ω X).left_inv ξ).symm⟩

theorem exists_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₁ : Type) [Field Ω₁] [CharZero Ω₁] (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ Y.X) (S : Finset ℕ), GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (i : Ω₁ →+* Ω), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) ∧ (∀ p ∈ S, FullTorsion Y.t.G (spMap i ≫ ξ₁) (p ^ 4)) ∧ ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4) := by
  intro E _ _ _ H D l Xo c Y Ω₁ _ _ ξ₁ S he hS
  have hN0 : (∏ p ∈ S, p ^ 4) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  obtain ⟨Ω', _, _, n, x, M, f, y, t, m, z, ev, -, hfin, hfe, -, -, htor, -⟩ :=
    GlobalTheory.T.LevelCoverSt_holds E H D l Xo c Y _ he (∏ p ∈ S, p ^ 4) (Nat.one_le_iff_ne_zero.2 hN0)
  haveI := hfin
  obtain ⟨i₁, h₁⟩ := exists_factor ξ₁ _ rfl
  obtain ⟨i₂, h₂⟩ := exists_factor (M.ξ ≫ f) (genPt ξ₁) (by
    rw [← hfe]
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Ar.genPt])
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates M.ξ (Y.X.fromSpecResidueField (genPt ξ₁)) f i₂ := h₂
  have hi₂ : i₂.Finite := HodgeExists.finite_of_dominates M.tie.gen f hdom
  obtain ⟨Ω₂, _, a, b, ha, hab⟩ := exists_compositum _ Ω₁ Ω' i₁ i₂ hi₂
  haveI : CharZero Ω₂ := charZero_of_injective_ringHom a.injective
  obtain ⟨Ω, _, j, hj, ζ, hζ⟩ := exists_root Ω₂ _ hN0
  haveI : CharZero Ω := charZero_of_injective_ringHom j.injective
  have hsp : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (u : R →+* R') (v : R' →+* R''),
      spMap (v.comp u) = spMap v ≫ spMap u := by
    intro R R' R'' _ _ _ u v
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hpt : spMap (j.comp a) ≫ ξ₁ = spMap (j.comp b) ≫ M.ξ ≫ f := by
    rw [h₂]
    conv_lhs => rw [h₁]
    rw [← Category.assoc, ← Category.assoc, ← hsp, ← hsp, RingHom.comp_assoc, RingHom.comp_assoc, hab]
  have hdvd : ∀ p ∈ S, p ^ 4 ∣ ∏ p ∈ S, p ^ 4 := fun p hp => Finset.dvd_prod_of_mem (fun p => p ^ 4) hp
  refine ⟨Ω, inferInstance, inferInstance, j.comp a, RingHom.Finite.comp hj ha, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hpt]
    exact fullTorsion_ext (j.comp b) (HodgeExists.fullTorsion_push m.cart (hdvd p hp) htor)
  · obtain ⟨d, hd⟩ := hdvd p hp
    exact ⟨ζ ^ d, hζ.pow (Nat.pos_of_ne_zero hN0) (by rw [hd, mul_comm])⟩

end GlobalTheory.CompanionTheory.Ar.ChgField
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₁ : Type) [Field Ω₁] [CharZero Ω₁] (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ Y.X) (S : Finset ℕ), GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (i : Ω₁ →+* Ω), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) ∧ (∀ p ∈ S, FullTorsion Y.t.G (spMap i ≫ ξ₁) (p ^ 4)) ∧ ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgField.exists_field | exact GlobalTheory.CompanionTheory.Ar.ChgField.exists_field | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgField.exists_field <;> assumption)
end
