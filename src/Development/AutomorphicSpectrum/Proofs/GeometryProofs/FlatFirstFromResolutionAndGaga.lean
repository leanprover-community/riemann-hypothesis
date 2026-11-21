import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeGramComplexConjugate
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunctionStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZero

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_analytic_norm : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (φ : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → Z.IsGeom → IsUnitAn τ σ Φ → IsLineFn U τ φ → FlatOnModel Z τ φ → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ y v w, IsFramed U τ σ y v w → φ ℂ y v w = κ * Φ y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn | exact GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  exact @PositivityTheory.Xgn.hodge_gram_complex_conjugate_alt

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_conjugate : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_spMap_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B)
    {T : Scheme.{0}} (g : Sp A ⟶ T) : spMap a ≫ spMap b ≫ g = spMap (a.comp b) ≫ g := by
  rw [← Category.assoc, spMap_spMap]

theorem spMap_idR (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ :=
  Spec.map_id (CommRingCat.of A)

theorem algebraMap_dual (a : R) : algebraMap R (DualNumber R) a = TrivSqZeroExt.inl a := rfl

theorem dualMap_comp_algebraMap (f : R →+* R) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R (DualNumber R)).comp f := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_epsMul (f : R →+* R) (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  ext a <;> simp [dualMap, epsMul, algebraMap_dual]

theorem fst_comp_dualMap (f : R →+* R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_dualMap (f : R →+* R) (hf : ∀ a, f (f a) = a) :
    (dualMap f).comp (dualMap f) = RingHom.id _ := by
  ext a <;> simp [dualMap, hf, algebraMap_dual]

def trM (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) : epsAt x' ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    subst hx
    change spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap R (DualNumber R)) ≫ spMap f ≫ x
    rw [spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_algebraMap])

def tr (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  trM f hx ≫ v

theorem tr_left (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) :
    (tr f hx v).left = spMap (dualMap f) ≫ v.left := rfl

variable {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S}

theorem tr_mul (f : R →+* R) (hx : x' = spMap f ≫ x) (a b : epsAt x ⟶ G) :
    tr f hx (a * b) = tr f hx a * tr f hx b :=
  MonObj.comp_mul _ _ _

theorem tr_one (f : R →+* R) (hx : x' = spMap f ≫ x) : tr f hx (1 : epsAt x ⟶ G) = 1 := by
  rw [tr, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (trM f hx ≫ toUnit _) (toUnit _)]

def trHom (f : R →+* R) (hx : x' = spMap f ≫ x) : (epsAt x ⟶ G) →* (epsAt x' ⟶ G) where
  toFun := tr f hx
  map_one' := tr_one f hx
  map_mul' := tr_mul f hx

theorem tr_prod (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    tr f hx (List.ofFn u).prod = (List.ofFn fun i => tr f hx (u i)).prod := by
  have := map_list_prod (trHom (G := G) f hx) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact this

theorem isTanAt_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {v : epsAt x ⟶ G} (h : IsTanAt G x v) :
    IsTanAt G x' (tr f hx v) := by
  have h1 : (1 : Over.mk x' ⟶ G) = (Over.homMk (spMap f) hx.symm : Over.mk x' ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  unfold IsTanAt at h ⊢
  rw [h1, Over.comp_left, ← h, tr_left]
  change spMap _ ≫ spMap (dualMap f) ≫ v.left = spMap f ≫ spMap _ ≫ v.left
  rw [spMap_spMap_assoc, spMap_spMap_assoc, fst_comp_dualMap]

theorem isEigVec_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hx : x' = spMap f ≫ x) {τ : O →+* R}
    {v : epsAt x ⟶ G} (h : IsEigVec act x τ v) : IsEigVec act x' (f.comp τ) (tr f hx v) := by
  refine ⟨isTanAt_tr f hx h.1, fun a => ?_⟩
  have h2 : (tr f hx v ≫ act.act a).left = spMap (dualMap f) ≫ (v ≫ act.act a).left := by
    rw [tr, Category.assoc]; rfl
  rw [h2, h.2 a, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem isComb_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsAt x ⟶ G)}
    {w : epsAt x ⟶ G} (h : IsComb c v w) : IsComb (fun i => f (c i)) (fun i => tr f hx (v i)) (tr f hx w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => tr f hx (u i), fun i => ?_, tr_prod f hx u⟩
  rw [tr_left, hu, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem back (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) : x = spMap f ≫ x' := by
  have : f.comp f = RingHom.id R := RingHom.ext hf
  rw [hx, spMap_spMap_assoc, this, spMap_idR, Category.id_comp]

theorem tr_tr (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) (hx' : x = spMap f ≫ x')
    (v : epsAt x ⟶ G) : tr f hx' (tr f hx v) = v := by
  apply Over.OverMorphism.ext
  rw [tr_left, tr_left, spMap_spMap_assoc, dualMap_comp_dualMap f hf, spMap_idR, Category.id_comp]

theorem isEigFrame_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hf : ∀ a, f (f a) = a)
    (hx : x' = spMap f ≫ x) {τ : O →+* R} {n : ℕ} {v : Fin n → (epsAt x ⟶ G)} (h : IsEigFrame act x τ v) :
    IsEigFrame act x' (f.comp τ) (fun i => tr f hx (v i)) := by
  have hx' := back f hf hx
  refine ⟨fun i => isEigVec_tr act f hx (h.1 i), fun w hw => ?_⟩
  have hw0 : IsEigVec act x τ (tr f hx' w) := by
    have := isEigVec_tr act f hx' hw
    have e : f.comp (f.comp τ) = τ := RingHom.ext fun a => hf _
    rwa [e] at this
  obtain ⟨c, hc, hu⟩ := h.2 _ hw0
  refine ⟨fun i => f (c i), ?_, fun c' hc' => ?_⟩
  · have := isComb_tr f hx hc
    rwa [tr_tr f hf hx' hx] at this
  · have h3 := isComb_tr f hx' hc'
    simp only [tr_tr f hf hx hx'] at h3
    have h4 := hu _ h3
    funext i
    rw [← h4]
    exact (hf _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ConjPt in

theorem hasInfNorm_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  intro E _ _ _ H D l Xo c U τ φ s t hl hs y v w Γ Δ hfr hΓ hΔ
  have hcc : ∀ z : ℂ, (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := fun z => Complex.conj_conj z
  obtain ⟨h1, h2, h3, h4⟩ := hfr
  have hy : under (spMap (starRingEnd ℂ) ≫ y) = spMap (starRingEnd ℂ) ≫ under y := Category.assoc _ _ _
  have hcomp : ∀ {A : Type} [CommRing A] (g : A →+* ℂ), (starRingEnd ℂ).comp ((starRingEnd ℂ).comp g) = g :=
    fun g => RingHom.ext fun a => hcc _
  let v' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.p := fun i => tr (starRingEnd ℂ) hy (v i)
  let w' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.q := fun i => tr (starRingEnd ℂ) hy (w i)
  have hfr' : IsFramed U τ s (spMap (starRingEnd ℂ) ≫ y) v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h1, spMap_spMap, hcomp]
    · rintro _ ⟨a, rfl⟩
      exact h2 ⟨(spMap (starRingEnd ℂ)) a, by simp⟩
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h3
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c τ)) = s.comp (tauIn c τ) :=
        RingHom.ext fun a => hcc _
      rwa [e] at this
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h4
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c (ComplexEmbedding.conjugate τ))) =
          s.comp (tauIn c (ComplexEmbedding.conjugate τ)) := RingHom.ext fun a => hcc _
      rwa [e] at this
  have hΓ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ v v' Γ hy (fun a => tr_left _ hy _) hΓ
  have hΔ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ w w' Δ hy (fun a => tr_left _ hy _) hΔ
  have hnat := hl.nat ℂ ℂ (starRingEnd ℂ) ((starRingEnd ℂ).comp s) y v w (spMap (starRingEnd ℂ) ≫ y) v' w'
    ⟨h1, h2, h3, h4⟩ rfl (fun i => tr_left _ hy _) (fun i => tr_left _ hy _)
  have hm := hs _ v' w' _ _ hfr' hΓ' hΔ'
  have hdet : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), ‖(M.map star).det‖ = ‖M.det‖ := by
    intro n M
    have : (M.map star).det = (starRingEnd ℂ) M.det := by
      rw [RingHom.map_det]; rfl
    rw [this, RCLike.norm_conj]
  rw [hnat, RCLike.norm_conj, hdet, hdet] at hm
  exact hm

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_norm_conjugate_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero H

theorem tauIn_rt_eq (τ : E →+* ℂ) (σ : c.F →+* ℂ) :
    σ (tauIn c τ H.rt) = H.rt0 ∨ σ (tauIn c τ H.rt) = -H.rt0 := by
  have h : (σ (tauIn c τ H.rt)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, H.sqrt_neg_disc_sq]; simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem gram_det_ne_zero {τ : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    {y : Sp ℂ ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {Γ : Matrix (Fin D.p) (Fin D.p) ℂ}
    (hf : IsFramed Set.univ τ σ y v w) (hΓ : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ) :
    Γ.det ≠ 0 := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hf.1, ← Spec.map_comp]; rfl
  obtain ⟨i, P, hP, hu⟩ := FU.onto _ hs
  obtain ⟨V, hV, hli, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y)
    (σ.comp (tauIn c τ)) (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) D.p v hP hu.symm (fun a => rfl)
    hf.2.2.1
  obtain ⟨Hm, hH, hpos, him⟩ := hP.2.2.2.2
  have hG := (hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hH him (under y) hu.symm D.p v V Γ
    (fun a => (hV a (V a)).2 rfl)).1 hΓ
  let M : Matrix (Fin D.p) (Fin g) ℂ := Matrix.of V
  have hΓM : Γ = (Real.pi : ℂ) • (M * Hm * M.conjTranspose) := by
    ext a b
    rw [hG a b, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, M,
      Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set z := Matrix.vecMul (star x) M with hz
  have hq : dotProduct (star x) (Γ.mulVec x) = (Real.pi : ℂ) * hermForm Hm z z := by
    rw [hΓM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hermForm, hz, Matrix.star_vecMul, star_star,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hx, dotProduct_zero] at hq
  have hz0 : z = 0 := by
    by_contra hne
    have := hpos z hne
    have h2 : (hermForm Hm z z) = 0 := by
      rcases mul_eq_zero.1 hq.symm with h | h
      · exact absurd h (by exact_mod_cast Real.pi_ne_zero)
      · exact h
    rw [h2] at this; simp at this
  have hinj : Function.Injective M.vecMul := Matrix.vecMul_injective_iff.2 hli
  have : star x = 0 := hinj (show Matrix.vecMul (star x) M = Matrix.vecMul 0 M by rw [← hz, hz0, Matrix.zero_vecMul])
  exact hx0 (by simpa using this)

theorem exists_infNorm_of_rt (hR : Geo.ResK.ResKStatement) (hG : GagaSections) {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {τ : E →+* ℂ} {φ : FrameFn Xo c}
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hr : 1 ≤ D.p + D.q) (hτ : τ (H.rt : E) = H.rt0) (hZ : Z.IsGeom) (hl : IsLineFn U τ φ)
    (hm : FlatOnModel Z τ φ) (σ : c.F →+* ℂ) (hσ : σ (tauIn c τ H.rt) = H.rt0) :
    ∃ t : ℝ, HasInfNorm U τ φ σ t := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hK : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
    have e : (IntermediateField.inclusion c.le) (baseKA l).ρ = tauIn c τ H.rt :=
      Subtype.ext (show H.rt0 = τ (H.rt : E) from hτ.symm)
    show σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0
    rw [e, hσ]
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.T.abelianScheme_laws_unconditional.1 E H D l Xo _ g ty hr hK hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) σ g ty FU
    hty hσ (fun a => rfl)
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ σ Φ φ hβ hr hτ hσ hZ hΦ hl hm
  refine ⟨Real.log ‖κ‖, fun y v w Γ Δ hf h1 h2 => ?_⟩
  have hf' : IsFramed Set.univ τ σ y v w := ⟨hf.1, Set.subset_univ _, hf.2.2⟩
  have hΓ : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 (gram_det_ne_zero FU hf' h1)
  have hΦ0 : ‖Φ y v w‖ ≠ 0 := norm_ne_zero_iff.2 (hΦ.ne y v w hf')
  have hn := congrArg Real.log (hΦ.norm y v w Γ Δ hf' h1 h2)
  rw [Real.log_mul (pow_ne_zero 2 hΦ0) hΓ, Real.log_pow] at hn
  rw [hκ y v w hf, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hκ0) hΦ0]
  push_cast at hn
  linarith

theorem flat_first_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → FlatLineGeneratorComponent := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y U Z τ φ hβ hr hτ hZ hl hm
  have key : ∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t := by
    intro s
    rcases tauIn_rt_eq (c := c) (H := H) τ s with h | h
    · exact exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm s h
    · obtain ⟨t, ht⟩ := exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm ((starRingEnd ℂ).comp s)
        (by rw [RingHom.comp_apply, h, map_neg, rt0_conj_neg_ne_zero, neg_neg])
      refine ⟨t, ?_⟩
      have := GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ _ t hl ht
      rwa [show (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s from RingHom.ext fun x => by simp] at this
  refine ⟨fun s => ?_, fun g ty FU i hty hmem => ?_⟩
  · obtain ⟨t, ht⟩ := key s
    exact ⟨t, ht, GlobalTheory.T.inf_norm_conjugate_invariant E H D l Xo c U τ φ s t hl ht⟩
  · obtain ⟨Φ, hΦ, hfl⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun a => rfl)
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.frame_function_analytic_norm hR hG E H D l Xo c O β Y U Z τ (algebraMap c.F ℂ) Φ φ hβ hr hτ hτ hZ hΦ hl hm
    obtain ⟨e, ρ, -, he, hρ⟩ := hfl i
    refine ⟨hmem, hl, e, κ * ρ, he, ?_⟩
    intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
    rw [hκ y v w h3, _root_.mul_assoc, hρ P y v w V W C Fm B h1 h2 ⟨h3.1, Set.subset_univ _, h3.2.2⟩ h4 h5 h6 h7 h8]

end GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_first_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGeneratorComponent := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga
end
