import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedChart_exponential_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (x₀ : CxPts (genStr T.Z) σ), ∃ (n a g r₀ : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧ Function.Surjective (ex x₀) ∧ AnalyticOnNhd ℂ ζ (Metric.ball 0 1) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ex (e.symm z) (ζ z i) = 1) ∧ IsLatBasis {w | ex x₀ w = 1} (ζ 0) ∧ (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) ∧ ∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1 := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart | exact GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Core.core | exact GlobalTheory.ShFam.Hor.LogCh.Core.core | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Core.core <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExponential_modelFiber_of_uniformisationExp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx | exact GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pushEx_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have hw : ∀ (b : Fin 0 → ℂ) (z : Fin g → ℂ), (Fu.ex i P z).left ≫ Xo.univ.t.G.hom =
      (fun _ => y) b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := fun _ z => by
    rw [Over.w (Fu.ex i P z), ← hu]; rfl
  have h2 := GlobalTheory.TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ
    (fun (_ : Fin 0 → ℂ) z => (Fu.ex i P z).left) (fun _ => y) h1
    (GlobalTheory.TrueCx.TorHolo.isHolTo_const isOpen_univ y) hw
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_hol <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.PushKer

theorem unit_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem one_left {S T : Scheme.{0}} (a : T ⟶ S) (G : Over S) [MonObj G] :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def]; simp

theorem one_iff {S T : Scheme.{0}} {a : T ⟶ S} {G : Over S} [MonObj G] (x : Over.mk a ⟶ G) :
    x = 1 ↔ x.left = a ≫ (η[G]).left := by
  rw [← one_left]
  exact ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩

end GlobalTheory.ShFam.Hor.LogCh.PushKer

namespace GlobalTheory.ShFam.Hor.LogCh

open PushKer

theorem pushEx_eq_one_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z
  rw [← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]
  have u0 := unit_comp Z.m0.toSABMap.cart
  have u1 := unit_comp Z.m.cart
  have hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c) := Over.w (η[Z.oF.t.G])
  constructor
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m.cart.1.hom_ext
      · rw [h, Category.assoc, u1, ← hp]
        simp only [Model.j, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [e, Category.assoc, u1, ← hp]
    simp only [Category.assoc]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pow_eq_one_of_toBase {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {T : Over S'} (x : T ⟶ G') (N : ℕ)
    (hx : Out.toBase h.1.w x ^ N = 1) : x ^ N = 1 := by
  let β := GlobalTheory.UU.toBaseHom (hw := h.1.w) (GlobalTheory.TowerAlg.toBase_mul h) T
  have hinj : Function.Injective β := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  exact hinj ((map_pow β x N).trans (hx.trans (map_one β).symm))

theorem pushEx_cubWeil (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ)
    (hk : 0 < k) (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k)) :
    GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b))
      (unitOn ζ) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'

  have tors : ∀ d : (Fu.Di i).La, Fu.ex i P ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d => by
    have hpow : ∀ (n : ℕ) (z : Fin g → ℂ), Fu.ex i P z ^ n = Fu.ex i P (n • z) := fun n z => by
      induction n with
      | zero => simpa using ((Fu.ex_ker i P hP 0).2 (zero_mem _)).symm
      | succ n ih => rw [pow_succ, ih, ← Fu.ex_add i P hP, succ_nsmul]
    rw [hpow, Fu.ex_ker i P hP]
    exact ⟨d, by
      ext j
      simp [hk']⟩
  have h₀ : GlobalTheory.UU.CubWeil Xo.univ.t.cub k (Fu.ex i P ((k : ℂ)⁻¹ • P a)) (Fu.ex i P ((k : ℂ)⁻¹ • P b)) (unitOn ζ) :=
    (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme Xo.univ) (tors a) (tors b) _).2
      (by exact_mod_cast Fu.ex_weil i P hP k a b ζ hk hζ)
  let f₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let m₀ := Z.m0.toSABMap

  let σ : Over.mk (y ≫ f₀) ⟶ Over.mk (Fu.u i P) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hu)
  have h₁ := h₀.comp σ
  have e₁ : Units.map σ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [σ]
  rw [e₁] at h₁

  let lf : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
    Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
  have eb : ∀ z, Out.toBase m₀.cart.1.w (lf z) = σ ≫ Fu.ex i P z := fun z =>
    Over.OverMorphism.ext ((liftEx_fst Z Fu y i P hu z).trans (by simp [σ]))
  have tl : ∀ d : (Fu.Di i).La, lf ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d =>
    pow_eq_one_of_toBase m₀.cart _ k (by
      rw [eb, ← MonObj.comp_pow, tors, MonObj.comp_one])
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil Z.oF.t.cub (tl a) (tl b)
  have h₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₀ _ _ m₀.cm m₀.cart.1.w (GlobalTheory.TowerAlg.toBase_mul m₀.cart) _ _ _ _ m₀.lin
    k _ _ _ ζ' hζ'
  rw [eb, eb] at h₂
  obtain rfl : ζ' = unitOn ζ := h₂.unique h₁
  have h₃ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ _ _ _ Z.m.cm Z.m.cart.1.w (GlobalTheory.TowerAlg.toBase_mul Z.m.cart) _ _ _ _ Z.m.lin
    k _ _ _ _ hζ'

  let τ : Over.mk p ⟶ Over.mk ((Over.mk y).hom ≫ Z.jQ ≫ pullback.fst Z.s (spMap β)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hp)
  have h₄ := h₃.comp τ
  have e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [τ]
  rw [e₂] at h₄
  have e₃ : ∀ z, τ ≫ Out.toBase Z.m.cart.1.w (lf z) = pushEx Z Fu y i P p hu hp z := fun z =>
    Over.OverMorphism.ext (Category.id_comp _)
  rwa [e₃, e₃] at h₄

end GlobalTheory.ShFam.Hor.LogCh
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_eq_comp_linearEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : Sp ℂ ⟶ X) (g g' : ℕ) (ex : (Fin g → ℂ) → (Over.mk p ⟶ t.G)) (e' : (Fin g' → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p ex → IsHolTo Set.univ (fun w => (ex w).left) → IsExpAt t p e' → IsHolTo Set.univ (fun w => (e' w).left) → ∃ L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' z = ex (L z) := by
  intro E _ _ _ H X t p g g' ex e' hex hhol he' hhol'
  have one : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), (∀ z w, f (z + w) = f z * f w) → f 0 = 1 := by
    intro m f hf
    have h := hf 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have der : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p f →
      ∀ v : epsPt p ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (f 0).left →
        ∃! w, IsDerivAt0 (fun z => (f z).left) w v.left := by
    intro m f hf v hv
    refine hf.2.2 v.left ⟨Over.w v, ?_⟩
    rw [hv, one f hf.1]
  have H3 := (GlobalTheory.holomorphic_hom_determined X t.G).2.2.1 p
  obtain ⟨h, hh, -⟩ := H3 (Fin g' → ℂ) g e' ex he'.1 hex.1 hhol' hhol (der ex hex)
  obtain ⟨h', hh', -⟩ := H3 (Fin g → ℂ) g' ex e' hex.1 he'.1 hhol hhol' (der e' he')
  obtain ⟨k, -, hk⟩ := H3 (Fin g' → ℂ) g' e' e' he'.1 he'.1 hhol' hhol' (der e' he')
  obtain ⟨k', -, hk'⟩ := H3 (Fin g → ℂ) g ex ex hex.1 hex.1 hhol hhol (der ex hex)
  have c1 : h' ∘ₗ h = LinearMap.id :=
    (hk _ fun z => by rw [LinearMap.comp_apply, ← hh', ← hh]).trans (hk _ fun z => rfl).symm
  have c2 : h ∘ₗ h' = LinearMap.id :=
    (hk' _ fun z => by rw [LinearMap.comp_apply, ← hh, ← hh']).trans (hk' _ fun z => rfl).symm
  exact ⟨LinearEquiv.ofLinear h h' c2 c1, hh⟩

theorem exists_hermForm_transport : ∀ (g g' : ℕ) (L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Hm₀ : Matrix (Fin g') (Fin g') ℂ), Hm₀.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (hermForm Hm₀ z z).re) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ v w, hermForm Hm (L v) (L w) = hermForm Hm₀ v w := by
  intro g g' L Hm₀ hH hpos
  let A : Matrix (Fin g') (Fin g) ℂ := LinearMap.toMatrix' L.symm.toLinearMap
  have hA : ∀ v, A.mulVec v = L.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have key : ∀ v w, hermForm (Aᵀ * Hm₀ * A.map star) v w = hermForm Hm₀ (L.symm v) (L.symm w) := by
    intro v w
    simp only [hermForm, ← hA]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    congr 1
    ext j
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  refine ⟨Aᵀ * Hm₀ * A.map star, ?_, fun z hz => ?_, fun v w => ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    congr 1
    · ext a b
      simp [Matrix.conjTranspose_apply]
  · rw [key]
    exact hpos _ (by simpa using hz)
  · rw [key, L.symm_apply_apply, L.symm_apply_apply]

theorem exists_pushed_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X), IsPeriod (Fu.Di i) ty P → Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) → y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p → ∃ e' : (Fin g → ℂ) → (Over.mk p ⟶ Z.t.G), IsExpAt Z.t p e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ z, e' z = 1 ↔ z ∈ P.range) ∧ ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hP hu hp
  exact ⟨pushEx Z Fu y i P p hu hp, GlobalTheory.T.isExponential_modelFiber_of_uniformisationExp E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.expModelFiber_eq_one_iff_mem_periodLattice E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP⟩

theorem kernel_lattice_of_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g x ex hσ hpq hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  let e₀ : Fin (Fintype.card (Letter Dw)) ≃ Letter Dw := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c σ (e₀ j).1) hpq hσ hty
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ Fu y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨Hm, hH, hpos, ?_, ?_, ?_⟩
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(Fu.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner | exact GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner | (intros; apply GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairFam

open HolTorsion in

theorem cubWeil_const_of_isHolTo : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ b₁ hN _ hB hx hx' htor hb₀ hb₁ h₀
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.TorsionPairFam
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  first | exact @GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | exact GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | (intros; apply GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibTors

open GlobalTheory.Models GlobalTheory.UU

theorem exists_relDim_fibre (X : Scheme.{0}) (G : Over X) [GrpObj G] (hG : IsSemiAbelian G) (y : Sp ℂ ⟶ X) :
    ∃ n, SmoothOfRelativeDimension n ((Over.pullback y).obj G).hom := by
  have hG' : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj G).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback y).obj G).hom
  exact exists_dim_of_preconnected _ (((1 : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G).left) (default : PrimeSpectrum ℂ))

theorem lieBasis_card (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (y : Sp ℂ ⟶ X) (g n : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (v : Fin n → (epsR ℂ ⟶ (Over.pullback y).obj G)) (hv : IsLieBasis v) : n = g := by
  classical
  let G' := (Over.pullback y).obj G
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let ρ : epsPt y ⟶ Over.mk ((epsR ℂ).hom ≫ y) := Over.homMk (𝟙 _) rfl
  let T : (epsR ℂ ⟶ G') →* (epsPt y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G y) (epsR ℂ))
  have hT : ∀ a, (T a).left = a.left ≫ pullback.fst G.hom y := fun a => Category.id_comp _
  let U : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
  let ρ0 : Over.mk y ⟶ Over.mk (U.hom ≫ y) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ0).comp (toBaseHom (toBase_mul_pullback G y) U)
  have hη : η[G'].left ≫ pullback.fst G.hom y = (1 : Over.mk y ⟶ G).left := by
    have h' : (φ 1).left = (1 : U ⟶ G').left ≫ pullback.fst G.hom y := Category.id_comp _
    rw [map_one] at h'
    rw [h']
    congr 2
  have hTb : Function.Bijective T := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hT, ← hT, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (epsR ℂ).hom (Over.w p)) (pullback.lift_snd _ _ _),
        Over.OverMorphism.ext ((hT _).trans (pullback.lift_fst _ _ _))⟩
  have htan : ∀ a : epsR ℂ ⟶ G', IsTangent a ↔
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T a).left = (e 0).left := by
    intro a
    rw [h0, hT, ← hη]
    refine ⟨fun h => by rw [← Category.assoc, h], fun h => pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h
    · have e1 : a.left ≫ pullback.snd G.hom y = (epsR ℂ).hom := Over.w a
      have e2 : η[G'].left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w η[G']
      rw [Category.assoc, e1, e2]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.TanMod.spMap_comp']
      have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
        RingHom.ext fun _ => rfl
      rw [this]
      exact Spec.map_id _
  let Te := MulEquiv.ofBijective T hTb
  have hTe : ∀ a, Te a = T a := fun _ => rfl
  choose D hD _ using h1
  have hDmul : ∀ w w', D (w + w') = D w * D w' := fun w w' =>
    Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD (w + w'))
      (GlobalTheory.UnifCompare.isDerivAt0_mul (congrArg (·.left) h0) (hD w) (hD w')))
  have hDtan : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (D w).left = (e 0).left := fun w => (hD w).1
  let Dl : (Fin g → ℂ) → (epsR ℂ ⟶ G') := fun w => Te.symm (D w)
  have hTDl : ∀ w, T (Dl w) = D w := fun w => Te.apply_symm_apply (D w)
  have hDl_tan : ∀ w, IsTangent (Dl w) := fun w => (htan _).2 (by rw [hTDl]; exact hDtan w)
  have hDl_add : ∀ w w', Dl (w + w') = Dl w * Dl w' := fun w w' => by
    apply Te.injective
    rw [map_mul, hTe, hTe, hTe, hTDl, hTDl, hTDl, hDmul]
  have hDl_zero : Dl 0 = 1 := by
    have := hDl_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hDl_smul : ∀ (c : ℂ) w, (Dl (c • w)).left = spMap (epsScaleR c) ≫ (Dl w).left := by
    intro c w
    have hov : (spMap (epsScaleR c) ≫ (Dl w).left) ≫ G'.hom = (epsR ℂ).hom := by
      rw [Category.assoc, Over.w (Dl w)]
      show spMap _ ≫ spMap _ = spMap _
      rw [GlobalTheory.TanMod.spMap_comp']
      have hc : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) :=
        RingHom.ext fun a => by ext <;> simp [epsScaleR]
      rw [hc]
    let a : epsR ℂ ⟶ G' := Over.homMk (spMap (epsScaleR c) ≫ (Dl w).left) hov
    have ha : T a = D (c • w) := by
      refine Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique ?_ (hD (c • w)))
      rw [hT]
      have := GlobalTheory.UnifCompare.isDerivAt0_smul (hD w) c
      rw [← hTDl w, hT] at this
      show IsDerivAt0 _ _ ((spMap (epsScaleR c) ≫ (Dl w).left) ≫ pullback.fst G.hom y)
      rw [Category.assoc]
      exact this
    have : a = Dl (c • w) := by
      apply Te.injective
      rw [hTe, hTe, ha, hTDl]
    rw [← this]
    rfl
  have hDl_inj : ∀ w w', Dl w = Dl w' → w = w' := by
    intro w w' h
    have h' : D w = D w' := by rw [← hTDl, ← hTDl, h]
    exact (h2 (D w) (hDtan w)).unique (hD w) (h' ▸ hD w')
  have hDl_onto : ∀ a, IsTangent a → ∃ w, Dl w = a := by
    intro a ha
    obtain ⟨w, hw, -⟩ := h2 (T a) ((htan a).1 ha)
    refine ⟨w, Te.injective ?_⟩
    rw [Te.apply_symm_apply, hTe]
    exact Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD w) hw)
  have hsum : ∀ (k : ℕ) (f : Fin k → Fin g → ℂ), Dl (∑ i, f i) = (List.ofFn fun i => Dl (f i)).prod := by
    intro k
    induction k with
    | zero => intro f; simp [hDl_zero]
    | succ k ih =>
      intro f
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, hDl_add, ih]
  choose ws hws using fun i => hDl_onto (v i) (hv.1 i)
  have hcomb : ∀ c : Fin n → ℂ, IsLieComb c v (Dl (∑ i, c i • ws i)) := by
    intro c
    refine ⟨fun i => Dl (c i • ws i), fun i => ?_, hsum n _⟩
    rw [hDl_smul, hws]
  have hdet : ∀ (c : Fin n → ℂ) (a a' : epsR ℂ ⟶ G'), IsLieComb c v a → IsLieComb c v a' → a = a' := by
    rintro c a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
    rw [this]
  have hli : LinearIndependent ℂ ws := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have e1 := hcomb c
    rw [hc] at e1
    have e2 := hcomb 0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e2
    have := (hv.2 (Dl 0) (hDl_tan 0)).unique e1 e2
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ws) := by
    intro w _
    obtain ⟨c, hc, -⟩ := hv.2 (Dl w) (hDl_tan w)
    have := hDl_inj _ _ (hdet c _ _ hc (hcomb c))
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  simpa using hb.symm

end GlobalTheory.FibTors

open GlobalTheory.FibTors GlobalTheory.Models GlobalTheory.UU in

theorem GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro E _ _ _ H X t y g N e hN hexp _ _
  obtain ⟨hadd, hd1, hd2⟩ := hexp
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h1 : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro w
    obtain ⟨v, ⟨hv1, hv2⟩, hu⟩ := hd1 w
    refine ⟨Over.homMk v hv1.1, hv2, fun v' hv' => Over.OverMorphism.ext (hu v'.left ⟨⟨Over.w v', ?_⟩, hv'⟩)⟩
    refine hv'.1.trans ?_
    show (e 0).left = _
    rw [h0]
  have h2 : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro v hv
    exact hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩
  obtain ⟨n, hn⟩ := exists_relDim_fibre X t.G t.semi y
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hn
  have hng := lieBasis_card X t.G y g n e hadd h1 h2 v hv
  subst hng
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let G : Over X := t.G
  let x := y
  let k := ℂ
  have h3 := GlobalTheory.laws3
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G t.semi
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension n G'.hom := hn
  obtain ⟨E⟩ := t.semi.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) t.PP t.cub
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e' := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e' a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e'.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E n N hG' dG' hN'
  refine ⟨e' '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, s0, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e'.surjective y
    have ht : s0 ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) t.PP _ t.cub c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e'.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e'.injective _
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  atlas_forward_decl GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_lattice_torsion_count : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  intro Q _ g r N e b T hN he _hs hb hT hcard
  haveI : NeZero N := ⟨hN.ne'⟩
  have e0 : e 0 = 1 := by
    have h := he 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := e 0) (h.symm.trans (_root_.mul_one _).symm)
  have esub : ∀ v w, e (v - w) = e v * (e w)⁻¹ := by
    intro v w
    have h := he (v - w) w
    rw [sub_add_cancel] at h
    exact eq_mul_inv_of_mul_eq h.symm
  have ensmul : ∀ (n : ℕ) v, e (n • v) = e v ^ n := by
    intro n v
    induction n with
    | zero => simp [e0]
    | succ n ih => rw [succ_nsmul, he, ih, pow_succ]
  set ψ : (Fin r → ℤ) → Q := fun a => e ((N : ℂ)⁻¹ • ∑ j, a j • b j) with hψ
  have hdiff : ∀ a a' : Fin r → ℤ, (N : ℂ)⁻¹ • ∑ j, a j • b j - (N : ℂ)⁻¹ • ∑ j, a' j • b j
      = (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j := by
    intro a a'
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    simp [sub_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hdvd : ∀ (c m : Fin r → ℤ), (N : ℂ)⁻¹ • ∑ j, c j • b j = ∑ j, m j • b j → ∀ j, c j = N * m j := by
    intro c m h
    have h2 : ∑ j, c j • b j = (N : ℂ) • ∑ j, m j • b j := by
      rw [← h, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    have h3 : ∑ j, ((c j : ℝ) - (N : ℝ) * (m j : ℝ)) • b j = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, Int.cast_smul_eq_zsmul]
      rw [h2, Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℝ, sub_self]
    have h4 := Fintype.linearIndependent_iff.1 hb.1 _ h3
    intro j
    have := h4 j
    rw [sub_eq_zero] at this
    exact_mod_cast this
  have key : ∀ a a' : Fin r → ℤ, ψ a = ψ a' ↔ ∀ j, (a j : ZMod N) = a' j := by
    intro a a'
    constructor
    · intro h
      have h1 : e ((N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j) = 1 := by
        rw [← hdiff, esub]
        exact mul_inv_eq_one.2 h
      obtain ⟨m, hm⟩ := (hb.2 _).1 h1
      have := hdvd (fun j => a j - a' j) m hm
      intro j
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-m j, by have := this j; push_cast at this ⊢; linarith⟩
    · intro h
      have hk : ∀ j, ∃ k : ℤ, a j - a' j = N * k := fun j =>
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h j).symm |>.imp fun k hk => by linarith
      choose k hk using hk
      have h1 : e (∑ j, k j • b j) = 1 := (hb.2 _).2 ⟨k, rfl⟩
      have h2 : (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j = ∑ j, k j • b j := by
        simp_rw [hk, mul_smul, ← Finset.smul_sum]
        rw [Nat.cast_smul_eq_nsmul ℤ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      have h3 := hdiff a a'
      rw [h2] at h3
      have h4 : (N : ℂ)⁻¹ • ∑ j, a j • b j = (N : ℂ)⁻¹ • ∑ j, a' j • b j + ∑ j, k j • b j := by
        rw [← h3]; abel
      simp only [hψ, h4, he, h1, _root_.mul_one]
  have hpow : ∀ a, ψ a ^ N = 1 := by
    intro a
    show e _ ^ N = 1
    rw [← ensmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (hb.2 _).2 ⟨a, rfl⟩
  have hsurj : ∀ p : Q, p ^ N = 1 → ∃ a, ψ a = p := by
    intro p hp
    obtain ⟨u, rfl⟩ := _hs p
    have h1 : e (N • u) = 1 := by rw [ensmul, hp]
    obtain ⟨m, hm⟩ := (hb.2 _).1 h1
    refine ⟨m, ?_⟩
    show e _ = e u
    rw [← hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let F : (Fin r → ZMod N) → Q := fun s => ψ (fun j => ((s j).val : ℤ))
  have hFval : ∀ a : Fin r → ℤ, F (fun j => (a j : ZMod N)) = ψ a := by
    intro a
    exact (key _ _).2 fun j => by simp
  have hFinj : Function.Injective F := by
    intro s s' h
    funext j
    have h1 := (key _ _).1 h j
    simpa using h1
  have hR : Nat.card {p : Q // p ^ N = 1} = N ^ r := by
    have hbij : Function.Bijective (fun s => (⟨F s, hpow _⟩ : {p : Q // p ^ N = 1})) := by
      refine ⟨fun s s' h => hFinj (congrArg Subtype.val h), fun p => ?_⟩
      obtain ⟨a, ha⟩ := hsurj p.1 p.2
      exact ⟨fun j => (a j : ZMod N), Subtype.ext (by show F _ = _; rw [hFval, ha])⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  refine ⟨{s | F s ∈ T}, ?_, ?_⟩
  · have hS : Nat.card {s | F s ∈ T} = Nat.card T := by
      have hbij : Function.Bijective (fun s : {s | F s ∈ T} => (⟨F s.1, s.2⟩ : T)) := by
        refine ⟨fun s s' h => Subtype.ext (hFinj (congrArg Subtype.val h)), fun τ => ?_⟩
        obtain ⟨a, ha⟩ := hsurj τ.1 (hT _ τ.2)
        refine ⟨⟨fun j => (a j : ZMod N), ?_⟩, Subtype.ext ?_⟩
        · show F _ ∈ T
          rw [hFval, ha]
          exact τ.2
        · show F _ = _
          rw [hFval, ha]
      exact Nat.card_eq_of_bijective _ hbij
    rw [hS, ← hR, hcard]
  · intro a ha
    show ψ a ∈ T
    rw [← hFval]
    exact ha

end GlobalTheory.ShFam.Hor.LogCh
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_count_through_exponential_lattice_kernel : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem unitOn_injective : Function.Injective (unitOn (R := ℂ)) := by
  intro c c' h
  ext
  have := congrArg (fun u : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (u : Γ(Sp ℂ, ⊤))) h
  simpa [unitOn] using this

theorem unitOn_one : unitOn (1 : ℂˣ) = 1 := by simp [unitOn]

theorem map_nsmul_eq_pow {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) (N : ℕ) (u : Fin g → ℂ) : f ((N : ℂ) • u) = f u ^ N := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Nat.cast_succ, add_smul, one_smul, hf, ih, pow_succ]

theorem pow_eq_one_of_map {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) {N : ℕ} (hN : 0 < N) {v : Fin g → ℂ} (hv : f v = 1) : f ((N : ℂ)⁻¹ • v) ^ N = 1 := by
  rw [← map_nsmul_eq_pow f hf h0, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_smul, hv]

theorem exists_isLogChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → ∀ x₀ : CxPts (genStr T.Z) σ, ∃ (n g r a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsLogChart a e ex lam ρ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ hσ hpq x₀
  obtain ⟨n, a, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩ :=
    GlobalTheory.T.exists_framedChart_exponential_toroidalModel E H Dw l Xo c O β Y T σ x₀
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hEC
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz =>
    e.map_target (by rw [htarget]; exact hz)
  have hExpAt : ∀ x ∈ e.source, IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := fun x hx =>
    ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hzero : ∀ x ∈ e.source, ex x 0 = 1 := fun x hx => by
    have := hadd x hx 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left) :=
    fun z hz => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ
        ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)
      dsimp only at this
      exact this
  have h0 : e.symm 0 = x₀ := by rw [← he0]; exact e.left_inv hx₀
  have hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  let Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H T.Z.X T.Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι T.Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hB0 : IsLatBasis (K 0) (ζ 0) := by
    show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)
    rw [h0]
    exact hζB
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B →
      Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c := by
    intro m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family T.Z.X T.Z.t.G T.Z.t.PP T.Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι T.Z)
      (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc
      h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hz hnz
    have hin : Inner (e.symm z) := (hbd _ (hsymm z hz)).2 fun k hk => by
      rw [e.right_inv (by rw [htarget]; exact hz)]
      exact hnz k hk
    obtain ⟨Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary E H Dw l Xo c O β T.Z σ g (e.symm z) (ex (e.symm z)) hσ hpq
      hin (hExpAt _ (hsymm z hz)) (hslice z hz)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1 := by
    intro N hN
    have hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left) := by
      have := hslice 0 hmem0
      rw [h0] at this
      exact this
    obtain ⟨Tt, hT1, hT2, hTc⟩ := GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H T.Z.X T.Z.t (x₀.1 ≫ genι T.Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl
    obtain ⟨S, hSc, hS⟩ := GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc
    refine ⟨S, hSc, fun a a' ha => ?_⟩
    show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, a j • ζ 0 j))
      (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, a' j • ζ 0 j)) (unitOn 1)
    rw [h0, unitOn_one]
    exact hT2 _ (hS a ha) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨a', rfl⟩))
  obtain ⟨r, lam, ρ, hc, hs, hg⟩ := GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  exact ⟨n, g, r, a, e, ex, lam, ρ, hx₀, he0, ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩, hbd, hc, hs, hg⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end
