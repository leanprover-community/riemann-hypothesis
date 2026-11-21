import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMapCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapFlatExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitOfDvrUnit
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.property_of_codim_one_local_units : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (P : ∀ (k : Type) [Field k], (A →+* k) → k → Prop) (good : Set (PrimeSpectrum A)),
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ good →
    (∀ 𝔭 : PrimeSpectrum A, (𝔭 ∈ good ∨ 𝔭.asIdeal.height = 1) → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), P k (φ.comp (algebraMap A _)) (φ u)) →
    (∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', P k φ v → P k φ v' → v = v') →
    (∀ (k : Type) [Field k] (φ : A →+* k) (v : k),
      (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∉ good → P k φ v) →
    ∃ f : Aˣ, ∀ (k : Type) [Field k] (φ : A →+* k), P k φ (φ f) := by
  first | exact @GlobalTheory.HartogsUnit.exists_unit_of_local_units | exact GlobalTheory.HartogsUnit.exists_unit_of_local_units | (intros; apply GlobalTheory.HartogsUnit.exists_unit_of_local_units <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

theorem GlobalTheory.openImmersion_factor_localization_atPrime : ∀ {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] {A : Type} [CommRing A] (ξ : Sp A ⟶ X)
    (𝔭 : PrimeSpectrum A), ξ 𝔭 ∈ Set.range j →
    ∃ y : Sp (Localization.AtPrime 𝔭.asIdeal) ⟶ U, y ≫ j = spMap (algebraMap A _) ≫ ξ := by
  intro X U j _ A _ ξ 𝔭 h𝔭
  have hopen : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
  have hsub : Set.range (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x ⤳ IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal) :=
      IsLocalRing.specializes_closedPoint x
    have h2 := hx.map (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) ≫ ξ).continuous
    refine h2.mem_open hopen ?_
    have hc : (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) (IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal)) = 𝔭 := by
      apply PrimeSpectrum.ext
      exact Localization.AtPrime.under_maximalIdeal
    change ξ ((spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) (IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal))) ∈ _
    rw [hc]; exact h𝔭
  exact ⟨IsOpenImmersion.lift j _ hsub, IsOpenImmersion.lift_fac _ _ _⟩
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_to_local_ring_open_immersion : ∀ {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] {A : Type} [CommRing A] (ξ : Sp A ⟶ X)
    (𝔭 : PrimeSpectrum A), ξ 𝔭 ∈ Set.range j →
    ∃ y : Sp (Localization.AtPrime 𝔭.asIdeal) ⟶ U, y ≫ j = spMap (algebraMap A _) ≫ ξ := by
  atlas_forward_decl GlobalTheory.openImmersion_factor_localization_atPrime
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) {L k : Type}
    [CommRing L] [CommRing k] (φ : L →+* k) (yL : Sp L ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber L) ⟶ Y.t.G.left)) (cf : Fin g → L) (w : Sp (DualNumber L) ⟶ Y.oF.t.G.left)
    (w' : Sp (DualNumber k) ⟶ Y.oF.t.G.left),
    IsCombAtG Y.t (yL ≫ Y.j) e cf (w ≫ Y.m.φ) →
    IsCombAtG Y.t (spMap φ ≫ yL ≫ Y.j) (bcV Y.t φ e) (fun b => φ (cf b)) (w' ≫ Y.m.φ) →
    w' = spMap (dualMap φ) ≫ w := by
  first | exact @GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG | exact GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG | (intros; apply GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG <;> assumption)
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_frame_invariance : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) →
    ∀ {k : Type} [Field k] [Algebra c.F k] (z y : FrPt Xo c k), z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) k),
      (∀ i, IsCombAt y.x (y.u τ.1) (g₁ i) (z.u τ.1 i)) →
      (∀ i, IsCombAt y.x (y.u (conjEmb τ.1)) (g₂ i) (z.u (conjEmb τ.1) i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y := by
  first | exact @GlobalTheory.FlatGL.evR_flat_chg | exact GlobalTheory.FlatGL.evR_flat_chg | (intros; apply GlobalTheory.FlatGL.evR_flat_chg <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.GenChartAlg

theorem exists_algebra_of_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L), (yL ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c L ∧
      (∀ z : FrPt Xo c L, z.x = yL ≫ r ≫ pullback.fst _ _ → ptF z = yL ≫ r) ∧
      ∀ (σ : E →+* ℂ) (a : 𝓞 E), algebraMap c.F L (embK c σ a) = io (β (embV c' W σ a)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r hle hr A _ ξ β hβ L _ io yL hyL
  obtain ⟨f', hf'⟩ : ∃ f' : c'.F →+* L, yL ≫ pullback.snd _ _ = spMap f' :=
    ⟨(Spec.preimage (yL ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  letI alg : Algebra c.F L := (f'.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hsnd : yL ≫ r ≫ pullback.snd _ _ = spMap (algebraMap c.F L) := by
    rw [hr, ← Category.assoc, hf']
    simp only [spMap, ← Spec.map_comp]
    rfl
  have e1 : yL ≫ Y.j ≫ Y.s = spMap (io.comp β) := by
    rw [← Category.assoc, hyL, Category.assoc, hβ]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have e2 : yL ≫ Y.j ≫ Y.s = spMap (f'.comp (c'.V W).subtype) := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hf']
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : f'.comp (c'.V W).subtype = io.comp β := by
    have h := e2.symm.trans e1
    simp only [spMap] at h
    have h2 := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨alg, ?_, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc r, ← Category.assoc yL, hsnd]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  · intro z hz
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hz, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hsnd]
  · intro σ a
    exact RingHom.congr_fun key (embV c' W σ a)

end GlobalTheory.GenChartAlg
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_point_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L), (yL ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c L ∧
      (∀ z : FrPt Xo c L, z.x = yL ≫ r ≫ pullback.fst _ _ → ptF z = yL ≫ r) ∧
      ∀ (σ : E →+* ℂ) (a : 𝓞 E), algebraMap c.F L (embK c σ a) = io (β (embV c' W σ a)) := by
  atlas_forward_decl GlobalTheory.GenChartAlg.exists_algebra_of_genPt
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatModel.LiftGen

theorem one_left_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] (P : Over S) :
    (1 : P ⟶ G).left = P.hom ≫ eSec G := by
  rw [CategoryTheory.Hom.one_def]
  simp [eSec]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem epsMul_comp_alg {R : Type} [CommRing R] (c : R) :
    (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul]

theorem fst_comp_epsMul {R : Type} [CommRing R] (c : R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (epsMul c) = (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun z => ?_
  simp [epsMul]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun z => ?_
  simp [dualMap]

theorem exists_lift_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ cf : Fin g → L, ∃ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left,
      IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf (w ≫ Y.m.φ) ∧ IsTanAtG Y.oF.t yL w := by
  intro E _ _ _ H Dw l' Xo' c' W Y A _ ξ g e he L _ io yL hyL cf
  have hv : ∀ i, IsTanAtG Y.t (yL ≫ Y.j) (bcV Y.t io e i) := by
    intro i
    obtain ⟨h1, h2⟩ := he.1 i
    constructor
    · show (spMap (dualMap io) ≫ e i) ≫ Y.t.G.hom = _
      rw [Category.assoc, h1, ← Category.assoc, PullbackSections.spMap_comp_spMap, dualMap_comp_alg,
        ← PullbackSections.spMap_comp_spMap, Category.assoc, hyL]
    · show spMap _ ≫ spMap (dualMap io) ≫ e i = _
      rw [← Category.assoc, PullbackSections.spMap_comp_spMap, fst_comp_dualMap, ← PullbackSections.spMap_comp_spMap, Category.assoc, h2,
        one_left_eq, one_left_eq]
      simp only [Over.mk_hom]
      rw [hyL, Category.assoc]
  let u : Fin g → (tEpsG (yL ≫ Y.j) ⟶ Y.t.G) := fun i =>
    Over.homMk (spMap (epsMul (cf i)) ≫ bcV Y.t io e i) (by
      show (spMap (epsMul (cf i)) ≫ bcV Y.t io e i) ≫ Y.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL ≫ Y.j
      rw [Category.assoc, (hv i).1, ← Category.assoc, PullbackSections.spMap_comp_spMap, epsMul_comp_alg])
  let wG : Sp (DualNumber L) ⟶ Y.t.G.left := ((List.ofFn u).prod).left
  have hcomb : IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf wG := ⟨u, fun i => rfl, rfl⟩
  have hwG : wG ≫ Y.t.G.hom = (spMap (algebraMap L (DualNumber L)) ≫ yL) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    have := Over.w ((List.ofFn u).prod)
    simpa [wG, Model.j] using this
  let w : Sp (DualNumber L) ⟶ Y.oF.t.G.left := Y.m.cart.1.lift wG _ hwG
  have hwφ : w ≫ Y.m.φ = wG := Y.m.cart.1.lift_fst _ _ _
  have hwh : w ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL := Y.m.cart.1.lift_snd _ _ _
  refine ⟨w, hwφ ▸ hcomb, hwh, ?_⟩

  let δ : Over.mk (yL ≫ Y.j) ⟶ tEpsG (yL ≫ Y.j) := Over.homMk (spMap (TrivSqZeroExt.fstHom L L L).toRingHom) (by
    show spMap _ ≫ spMap (algebraMap L (DualNumber L)) ≫ yL ≫ Y.j = yL ≫ Y.j
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (algebraMap L (DualNumber L)) = RingHom.id L := by
      refine RingHom.ext fun z => ?_
      simp
    rw [this, spMap_id']
    exact Category.id_comp _)
  have hδu : ∀ i, δ ≫ u i = 1 := by
    intro i
    refine Over.OverMorphism.ext ?_
    show spMap _ ≫ spMap (epsMul (cf i)) ≫ bcV Y.t io e i = _
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, fst_comp_epsMul]
    exact (hv i).2
  have hδ : δ ≫ (List.ofFn u).prod = 1 := by
    have h := map_list_prod (Formalism.L2.Pj.preHom (G := Y.t.G) δ) (List.ofFn u)
    rw [List.map_ofFn] at h
    refine (congrArg _ rfl).trans (h.trans ?_)
    have hf : (⇑(Formalism.L2.Pj.preHom (G := Y.t.G) δ) ∘ u) = fun _ => 1 := by
      funext i
      exact hδu i
    rw [hf, List.ofFn_const, List.prod_replicate, one_pow]
  refine Y.m.cart.1.hom_ext ?_ ?_
  · show (spMap _ ≫ w) ≫ Y.m.cm.F = _
    rw [Category.assoc, hwφ]
    have h1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ wG = (δ ≫ (List.ofFn u).prod).left := rfl
    rw [h1, hδ, one_left_eq, one_left_eq, Category.assoc, Y.m.cm.e_comm, Y.m.base]
    rfl
  · rw [Category.assoc, hwh, Over.w (1 : Over.mk yL ⟶ Y.oF.t.G), ← Category.assoc, PullbackSections.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (algebraMap L (DualNumber L)) = RingHom.id L := by
      refine RingHom.ext fun z => ?_
      simp
    rw [this, spMap_id']
    exact Category.id_comp _

end GlobalTheory.FlatModel.LiftGen
end
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ cf : Fin g → L, ∃ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left,
      IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf (w ≫ Y.m.φ) ∧ IsTanAtG Y.oF.t yL w := by
  atlas_forward_decl GlobalTheory.FlatModel.LiftGen.exists_lift_comb
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_section_compatibility : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (L : Type) [CommRing L] [Algebra c.F L]
    (yL : Sp L ⟶ Xo'.XF c') (σ : E →+* ℂ) (s : 𝓞 E →+* L), (∀ a, algebraMap c.F L (embK c σ a) = s a) →
    ∀ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left, IsTanAtG Y.oF.t yL w → IsEigG Y.t s (w ≫ Y.m.φ) →
      IsTanAt (yL ≫ r ≫ pullback.fst _ _) (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  first | exact @GlobalTheory.FlatModel.tan_eig_push | exact GlobalTheory.FlatModel.tan_eig_push | (intros; apply GlobalTheory.FlatModel.tan_eig_push <;> assumption)
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_map_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (σ : E →+* ℂ) (U h : Fin (Dw.mult σ) → Fin g → A), IsUnit (pairDet h U) →
    ∀ (L : Type) [CommRing L] [Algebra c.F L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ z₀ : FrPt Xo c L, z₀.x = yL ≫ r ≫ pullback.fst _ _ →
    ∀ w : Fin (Dw.mult σ) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left),
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U i b)) (w i ≫ Y.m.φ)) →
      (∀ i, IsTanAtG Y.oF.t yL (w i)) → (∀ i, IsEigAt c σ (w i ≫ ν.φ)) →
      ∃ g₁ : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L, IsUnit g₁.det ∧
        ∀ i, IsCombAt z₀.x (z₀.u σ) (g₁ i) (w i ≫ ν.φ) := by
  first | exact @GlobalTheory.FrameCoordUnit.coord_unit | exact GlobalTheory.FrameCoordUnit.coord_unit | (intros; apply GlobalTheory.FrameCoordUnit.coord_unit <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FrameChangePair

theorem isCombAt_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w₁ w₂ : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h₁ : IsCombAt x v a w₁) (h₂ : IsCombAt x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

theorem psi_ne_conjEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : Psi H) :
    τ.1 ≠ conjEmb τ.1 := by
  intro h
  have hτ : τ.1 (H.rt : E) = H.rt0 := τ.2
  have hc : (starRingEnd ℂ) H.rt0 = H.rt0 := by
    have := congrArg (fun σ : E →+* ℂ => σ (H.rt : E)) h
    simp only [conjEmb, RingHom.comp_apply, hτ] at this
    exact this.symm
  have h1 : (H.rt0.re : ℂ) ^ 2 = -(H.d : ℂ) := by rw [Complex.conj_eq_iff_re.1 hc]; exact H.sqrt_neg_disc_sq
  have h2 : H.rt0.re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
  have h3 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  nlinarith [sq_nonneg H.rt0.re]

theorem exists_frPt_comb_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (L : Type) [CommRing L] [Algebra c.F L] (z₀ : FrPt Xo c L)
    (τ : Psi H) (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) L)
    (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) L)
    (v₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left))
    (v₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left)),
    IsUnit g₁.det → IsUnit g₂.det → (∀ i, IsCombAt z₀.x (z₀.u τ.1) (g₁ i) (v₁ i)) →
    (∀ i, IsCombAt z₀.x (z₀.u (conjEmb τ.1)) (g₂ i) (v₂ i)) →
    ∃ z : FrPt Xo c L, z.x = z₀.x ∧ (∀ i, z.u τ.1 i = v₁ i) ∧ ∀ i, z.u (conjEmb τ.1) i = v₂ i := by
  classical
  intro E _ _ _ H Dw l Xo c L _ _ z₀ τ g₁ g₂ v₁ v₂ hg₁ hg₂ hv₁ hv₂
  have hne : τ.1 ≠ conjEmb τ.1 := psi_ne_conjEmb τ
  let G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L :=
    Function.update (Function.update (fun σ => (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L)) τ.1 g₁)
      (conjEmb τ.1) g₂
  have hG₂ : G (conjEmb τ.1) = g₂ := Function.update_self _ _ _
  have hG₁ : G τ.1 = g₁ := by
    dsimp only [G]
    rw [Function.update_of_ne hne, Function.update_self]
  have hdet : ∀ σ, IsUnit (G σ).det := by
    intro σ
    by_cases h1 : σ = conjEmb τ.1
    · subst h1; rw [hG₂]; exact hg₂
    · by_cases h2 : σ = τ.1
      · subst h2; rw [hG₁]; exact hg₁
      · dsimp only [G]
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Matrix.det_one]
        exact isUnit_one
  obtain ⟨z, hz, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c L z₀ G 1 hdet
  obtain ⟨hx, hc, -⟩ := hz
  refine ⟨z, hx, fun i => ?_, fun i => ?_⟩
  · have h := hc τ.1 i
    rw [hG₁] at h
    exact isCombAt_unique h (hv₁ i)
  · have h := hc (conjEmb τ.1) i
    rw [hG₂] at h
    exact isCombAt_unique h (hv₂ i)

end GlobalTheory.FrameChangePair
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_tangent_matrices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (L : Type) [CommRing L] [Algebra c.F L] (z₀ : FrPt Xo c L)
    (τ : Psi H) (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) L)
    (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) L)
    (v₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left))
    (v₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Xo.univ.t.G.left)),
    IsUnit g₁.det → IsUnit g₂.det → (∀ i, IsCombAt z₀.x (z₀.u τ.1) (g₁ i) (v₁ i)) →
    (∀ i, IsCombAt z₀.x (z₀.u (conjEmb τ.1)) (g₂ i) (v₂ i)) →
    ∃ z : FrPt Xo c L, z.x = z₀.x ∧ (∀ i, z.u τ.1 i = v₁ i) ∧ ∀ i, z.u (conjEmb τ.1) i = v₂ i := by
  atlas_forward_decl GlobalTheory.FrameChangePair.exists_frPt_comb_pair
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.FrameLoc

theorem exists_frPt_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (τ : Psi H) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ (L : Type) [CommRing L] [IsLocalRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L) (z : FrPt Xo c L) (w₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left)),
      ptF z = yL ≫ r ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧
      (∀ i, z.u τ.1 i = w₁ i ≫ ν.φ) ∧ ∀ i, z.u (conjEmb τ.1) i = w₂ i ≫ ν.φ := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hov τ A _ ξ β hβ g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ L _ _ io yL hyL
  obtain ⟨alg, hs, hpt, hemb⟩ := GlobalTheory.T.integral_model_point_over_inclusion E H Dw l l' Xo Xo' c c' W Y r hle hov A ξ β hβ L io yL hyL
  letI := alg
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.FlagTan.exists_frPt (yL ≫ r ≫ pullback.fst _ _) hs
  choose w₁ hc₁ ht₁ using fun i => GlobalTheory.T.tangent_basis_generic_point E H Dw l' Xo' c' W Y A ξ g e he L io yL hyL (fun b => io (U₁ i b))
  choose w₂ hc₂ ht₂ using fun i => GlobalTheory.T.tangent_basis_generic_point E H Dw l' Xo' c' W Y A ξ g e he L io yL hyL (fun b => io (U₂ i b))
  have hE₁ := (heig L io).1
  have hE₂ := (heig L io).2
  rw [← hyL] at hE₁ hE₂
  have hp₁ := fun i => GlobalTheory.T.embedding_section_compatibility E H Dw l l' Xo Xo' c c' W Y r ν L yL τ.1
    (io.comp (β.comp (embV c' W τ.1))) (fun a => hemb _ a) (w₁ i) (ht₁ i) (hE₁ i _ (hc₁ i))
  have hp₂ := fun i => GlobalTheory.T.embedding_section_compatibility E H Dw l l' Xo Xo' c c' W Y r ν L yL (conjEmb τ.1)
    (io.comp (β.comp (embV c' W (conjEmb τ.1)))) (fun a => hemb _ a) (w₂ i) (ht₂ i) (hE₂ i _ (hc₂ i))
  obtain ⟨g₁, hg₁, hcg₁⟩ := GlobalTheory.T.tangent_basis_map_compatible E H Dw l l' Xo Xo' c c' W Y r ν A ξ g e he τ.1 U₁ h₁ hu₁ L io yL hyL z₀ hz₀
    w₁ hc₁ ht₁ fun i => (hp₁ i).2
  obtain ⟨g₂, hg₂, hcg₂⟩ := GlobalTheory.T.tangent_basis_map_compatible E H Dw l l' Xo Xo' c c' W Y r ν A ξ g e he (conjEmb τ.1) U₂ h₂ hu₂ L io yL hyL z₀ hz₀
    w₂ hc₂ ht₂ fun i => (hp₂ i).2
  obtain ⟨z, hzx, hz₁, hz₂⟩ := GlobalTheory.T.frame_point_tangent_matrices E H Dw l Xo c L z₀ τ g₁ g₂ (fun i => w₁ i ≫ ν.φ) (fun i => w₂ i ≫ ν.φ)
    hg₁ hg₂ hcg₁ hcg₂
  exact ⟨alg, z, w₁, w₂, hpt z (hzx.trans hz₀), hc₁, hc₂, hz₁, hz₂⟩

end GlobalTheory.FlatModel.FrameLoc
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_tangent_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (τ : Psi H) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ (L : Type) [CommRing L] [IsLocalRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L) (z : FrPt Xo c L) (w₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left)),
      ptF z = yL ≫ r ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧
      (∀ i, z.u τ.1 i = w₁ i ≫ ν.φ) ∧ ∀ i, z.u (conjEmb τ.1) i = w₂ i ≫ ν.φ := by
  atlas_forward_decl GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModelOpen

theorem unit_loc : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, ξ 𝔭 ∈ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  intro _ _ _ E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x _ Z τ s la p Xw _ hcov A _ _ _ ξ β _ hβ _ hgen
    g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ 𝔭 h𝔭
  haveI := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  obtain ⟨yL, hyL⟩ := GlobalTheory.T.lift_to_local_ring_open_immersion Y.j ξ 𝔭 h𝔭
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨alg, z, w₁, w₂, hz, hc₁, hc₂, hz₁, hz₂⟩ := GlobalTheory.T.integral_model_tangent_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hcov.1 τ A ξ β
    hβ g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ (Localization.AtPrime 𝔭.asIdeal) (algebraMap A _) yL hyL
  have hlies : LiesOn Z z := by
    intro q
    have hZc : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
    have h1 : Y.j (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) ∈ Xw := by
      have e : (yL ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) =
          Y.j (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) := Scheme.Hom.comp_apply _ _ _
      rw [← e, hyL, bot_map hinj]; exact hgen
    have h0 : ptF z (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) ∈ (Z : Set (Xo.XF c)) := by
      have e : (yL ≫ r) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) =
          r (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) := Scheme.Hom.comp_apply _ _ _
      rw [hz, e]; exact hcov.2.2.2.2.2.2.1 _ h1
    have hs : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) ⤳ q :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact (hs.map (ptF z).continuous).mem_closed hZc h0
  have hT : Tested z := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  have hone : evR Xo c s.sig z * evR Xo c s.inv z = 1 := by
    rw [← evR_idem hlies hT, ← s.mul_inv]
    exact (Formalism.L2.Pj.evalAt_mul _ _ _ _ _).symm
  have hU : IsUnit (evR Xo c s.sig z) := IsUnit.of_mul_eq_one _ hone
  refine ⟨hU.unit, fun k _ φ => ?_⟩
  intro alg' yy hyy y _ hy w₁' w₂' g₁ g₂ hw₁ hw₂ hg₁ hg₂
  have hyy' : yy = spMap φ ≫ yL := by
    apply (cancel_mono Y.j).1
    rw [hyy, Category.assoc, hyL, sp_sp]
  have hcomp : algebraMap c.F k = φ.comp (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal)) := by
    have e1 : ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F k) := pullback.lift_snd _ _ _
    have e2 : ptF z ≫ pullback.snd _ _ = spMap (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal)) :=
      pullback.lift_snd _ _ _
    have e3 : spMap (algebraMap c.F k) = spMap (φ.comp (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal))) := by
      rw [← e1, hy, hyy', Category.assoc, Category.assoc, ← Category.assoc yL, ← hz, e2, spMap_spMap]
    have e4 := Spec.map_injective e3
    exact congrArg CommRingCat.Hom.hom e4
  let φA : Localization.AtPrime 𝔭.asIdeal →ₐ[c.F] k :=
    { φ with commutes' := fun a => (RingHom.congr_fun hcomp a).symm }
  obtain ⟨zk, hzk⟩ := GlobalTheory.FlagTan.exists_frMap φA z
  have hev : evR Xo c s.sig zk = φ (evR Xo c s.sig z) := GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hzk
  have hx : zk.x = y.x := by
    have e1 : y.x = ptF y ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have e2 : z.x = ptF z ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    rw [hzk.1, e1, e2, hy, hz, hyy']
    simp only [Category.assoc]
  have hv₁ : ∀ i, zk.u τ.1 i = w₁' i ≫ ν.φ := by
    intro i
    have h2 := hw₁ i
    rw [hyy', Category.assoc, ← bcV_bcV] at h2
    have hw := GlobalTheory.T.tangent_frame_base_change Y φ yL _ _ (w₁ i) (w₁' i) (hc₁ i) h2
    rw [hzk.2.1 τ.1 i, hz₁ i, hw, Category.assoc]
  have hv₂ : ∀ i, zk.u (conjEmb τ.1) i = w₂' i ≫ ν.φ := by
    intro i
    have h2 := hw₂ i
    rw [hyy', Category.assoc, ← bcV_bcV] at h2
    have hw := GlobalTheory.T.tangent_frame_base_change Y φ yL _ _ (w₂ i) (w₂' i) (hc₂ i) h2
    rw [hzk.2.1 (conjEmb τ.1) i, hz₂ i, hw, Category.assoc]
  have key := GlobalTheory.T.flat_section_frame_invariance τ s.sig_mem zk y hx g₁ g₂ (fun i => by rw [hv₁ i]; exact hg₁ i)
    (fun i => by rw [hv₂ i]; exact hg₂ i)
  rw [hev] at key
  rw [IsUnit.unit_spec]
  exact key

end GlobalTheory.FlatModelOpen
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_extension : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, ξ 𝔭 ∈ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  atlas_forward_decl GlobalTheory.FlatModelOpen.unit_loc
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unit_of_dvr_unit : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT → ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ, (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by
  first | exact @GlobalTheory.unitMultiple_descends_of_height_eq_one | exact GlobalTheory.unitMultiple_descends_of_height_eq_one | (intros; apply GlobalTheory.unitMultiple_descends_of_height_eq_one <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem flatSec_unit_at_bdry_height_one : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  intro hP1 hP2 hP3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov A _ _ _ ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ 𝔭 hht hnr
  haveI hN : IsNoetherianRing A := GlobalTheory.T.integral_model_open_noetherian E H Dw l' Xo' c' W Y A ξ hξ
  let P0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hbotR : ξ P0 ∈ Set.range Y.j := hcov.2.2.2.2.1 hbot
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.integral_model_map_extension hP1 hP2 hP3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov
    A ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ P0 hbotR
  obtain ⟨T, iT, hiT, hloc, hval⟩ := GlobalTheory.T.section_value_unit_at_boundary_height_one_prime hP1 hP2 hP3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov
    A ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ 𝔭 hht hnr

  set gT : A →+* T.Fr := (algebraMap T.V T.Fr).comp (iT.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) with hgT
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔭.asIdeal)
  have hgTinj : Function.Injective gT :=
    (IsFractionRing.injective T.V T.Fr).comp (hiT.comp hAinj)
  have hunits : ∀ b : P0.asIdeal.primeCompl, IsUnit (gT b) := fun b =>
    isUnit_iff_ne_zero.2 fun h => b.2 (by
      have : (b : A) = 0 := hgTinj (by rw [h, map_zero])
      simp [P0, this])
  let κ : Localization.AtPrime P0.asIdeal →+* T.Fr := IsLocalization.lift hunits
  have hκ : κ.comp (algebraMap A _) = gT := IsLocalization.lift_comp hunits
  obtain ⟨w, hw⟩ := hval (κ u₀) fun k _ φ => by
    have h0 := hu₀ k (φ.comp κ)
    rwa [RingHom.comp_assoc, hκ] at h0
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective P0.asIdeal.primeCompl (u₀ : Localization.AtPrime P0.asIdeal)
  have h1 : gT a = gT b * algebraMap T.V T.Fr w :=
    (IsLocalization.lift_mk'_spec _ _ _ _).1 (by simp only at hab; rw [hab, hw])
  have h2 : iT (algebraMap A _ a) = iT (algebraMap A _ b) * w := by
    apply IsFractionRing.injective T.V T.Fr
    simpa [hgT, map_mul] using h1
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_local_unit_of_dvr_unit A 𝔭 hht T.V iT hiT hloc a b ⟨w, h2⟩
  refine ⟨u, fun k _ φ => ?_⟩
  set ψ : A →+* k := φ.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) with hψ
  by_cases hk : Function.Injective ψ
  ·
    have hunits' : ∀ b : P0.asIdeal.primeCompl, IsUnit (ψ b) := fun b =>
      isUnit_iff_ne_zero.2 fun h => b.2 (by
        have : (b : A) = 0 := hk (by rw [h, map_zero])
        simp [P0, this])
    let φ' : Localization.AtPrime P0.asIdeal →+* k := IsLocalization.lift hunits'
    have hφ' : φ'.comp (algebraMap A _) = ψ := IsLocalization.lift_comp hunits'
    have hle' : 𝔭.asIdeal.primeCompl ≤ P0.asIdeal.primeCompl.comap (RingHom.id A) := fun x hx hx0 => by
      apply hx
      have : x = 0 := by simpa [P0] using hx0
      rw [this]; exact 𝔭.asIdeal.zero_mem
    let mp : Localization.AtPrime 𝔭.asIdeal →+* Localization.AtPrime P0.asIdeal :=
      IsLocalization.map _ (RingHom.id A) hle'
    have hφ : φ = φ'.comp mp := by
      apply IsLocalization.ringHom_ext 𝔭.asIdeal.primeCompl
      rw [RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_id, hφ']
    have hmu : mp u = u₀ := by
      rw [← hab, IsLocalization.eq_mk'_iff_mul_eq]
      have := congrArg mp hu
      rw [map_mul] at this
      simpa [mp, IsLocalization.map_eq] using this
    have e2 : φ u = φ' u₀ := by
      rw [← hmu]
      exact congrArg (fun f : Localization.AtPrime 𝔭.asIdeal →+* k => f u) hφ
    rw [e2, ← hφ']
    exact hu₀ k φ'
  ·
    intro _ yy hyy
    exfalso
    apply hnr
    have hker : RingHom.ker ψ = 𝔭.asIdeal := by
      have hle : RingHom.ker ψ ≤ 𝔭.asIdeal := fun x hx => by
        by_contra hx'
        have hu' : IsUnit (algebraMap A (Localization.AtPrime 𝔭.asIdeal) x) :=
          IsLocalization.map_units _ (⟨x, hx'⟩ : 𝔭.asIdeal.primeCompl)
        have := (hu'.map φ).ne_zero
        exact this hx
      have hne : RingHom.ker ψ ≠ ⊥ := fun h => hk ((RingHom.injective_iff_ker_eq_bot ψ).2 h)
      by_contra hne'
      have hlt : RingHom.ker ψ < 𝔭.asIdeal := lt_of_le_of_ne hle hne'
      have hlt0 : (⊥ : Ideal A) < RingHom.ker ψ := bot_lt_iff_ne_bot.2 hne
      have a1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt0
      have a2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, hht] at *
      rw [zero_add] at a1
      have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add a1 le_rfl).trans a2
      exact absurd this (by decide)
    have hpt : (spMap ψ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) = 𝔭 := PrimeSpectrum.ext hker
    refine ⟨yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    calc Y.j (yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k))
        = (yy ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap ψ ≫ ξ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := by rw [hyy]
      _ = ξ ((spMap ψ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)) := Scheme.Hom.comp_apply _ _ _
      _ = ξ 𝔭 := by rw [hpt]

end GlobalTheory.FlatModel
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_uniqueness : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  atlas_forward_decl GlobalTheory.FlatModel.flatSec_unit_at_bdry_height_one
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.GenUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}

theorem rows_indep {A K : Type} [CommRing A] [Field K] (φ : A →+* K) {n g : ℕ} (h U : Fin n → Fin g → A)
    (hu : IsUnit (pairDet h U)) (a : Fin n → K) (ha : ∀ b, ∑ i, a i * φ (U i b) = 0) : a = 0 := by
  by_contra ha0
  let M : Matrix (Fin n) (Fin n) K := fun k k' => ∑ b, φ (h k' b) * φ (U k b)
  have hM : φ (pairDet h U) = M.det := by
    rw [pairDet, RingHom.map_det]
    congr 1
    ext k k'
    simp [M, map_sum, map_mul]
  have hdet : M.det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨a, ha0, ?_⟩
    ext k'
    simp only [Matrix.vecMul, dotProduct, M, Pi.zero_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    calc ∑ k, a k * (φ (h k' b) * φ (U k b)) = φ (h k' b) * ∑ k, a k * φ (U k b) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [ha b, mul_zero]
  exact (hu.map φ).ne_zero (hM.trans hdet)

theorem rows_data (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) {A K : Type} [CommRing A] [Field K] [Algebra c.F K]
    (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A) (φ : A →+* K) {g : ℕ} (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left))
    (hbas : IsTanBasis Y.t ξ e) (yy : Sp K ⟶ Xo'.XF c') (hyy : yy ≫ Y.j = spMap φ ≫ ξ) (y : FrPt Xo c K)
    (hyx : yy ≫ r ≫ pullback.fst _ _ = y.x) (ρ : E →+* ℂ) (U : Fin (Dw.mult ρ) → Fin g → A)
    (heig : EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W ρ))) (bcV Y.t φ e) (fun k b => φ (U k b)))
    (hσ : ∀ a, φ (β (embV c' W ρ a)) = algebraMap c.F K (embK c ρ a)) :
    ∃ (w : Fin (Dw.mult ρ) → (Sp (DualNumber K) ⟶ Y.oF.t.G.left)) (G : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) K),
      (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U i b)) (w i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAt y.x (y.u ρ) (G i) (w i ≫ ν.φ)) ∧
      (∀ h : Fin (Dw.mult ρ) → Fin g → A, IsUnit (pairDet h U) → G.det ≠ 0) := by
  have hb := isTanBasis_bc hbas φ
  let Eb : Fin g → PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G := fun b => GlobalTheory.LieMet.tanOf (hb.1 b)
  let C : Fin (Dw.mult ρ) → PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G := fun i => ∑ b, φ (U i b) • Eb b
  let Pm := GlobalTheory.LieMet.pushE Y.m yy hyy
  let Pν := GlobalTheory.LieMet.pushE ν yy hyx
  let N : Fin (Dw.mult ρ) → PullbackSections.TanM y.x Xo.univ.t.G := fun i => Pν (Pm.symm (C i))
  have hCc : ∀ i, IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (fun b => φ (U i b)) (PullbackSections.tv (C i)).left :=
    fun i => (GlobalTheory.LieMet.isComb_iff Eb _ (C i)).2 rfl
  have hsm : ∀ (a : K) (v : PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G), (PullbackSections.tv (a • v)).left = spMap (epsMul a) ≫ (PullbackSections.tv v).left :=
    fun _ _ => rfl
  have hact : ∀ (a : 𝓞 E) (v : PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G),
      (PullbackSections.tv (PullbackSections.actR Y.t.act a v)).left = (PullbackSections.tv v).left ≫ (Y.t.act.act a).left := fun _ _ => rfl

  have hCe : ∀ i (a : 𝓞 E), PullbackSections.actR Y.t.act a (C i) = φ (β (embV c' W ρ a)) • C i := fun i a =>
    GlobalTheory.LieMet.tan_ext (by rw [hact, hsm]; exact heig i _ (hCc i) a)
  have hNe : ∀ i (a : 𝓞 E), PullbackSections.actR Xo.univ.t.act a (N i) = φ (β (embV c' W ρ a)) • N i := by
    intro i a
    have h1 : PullbackSections.actR Y.oF.t.act a (Pm.symm (C i)) = φ (β (embV c' W ρ a)) • Pm.symm (C i) := by
      apply Pm.injective
      refine (GlobalTheory.LieMet.pushE_act Y.m yy hyy a _).trans ?_
      rw [map_smul]
      simp only [Pm, LinearEquiv.apply_symm_apply]
      exact hCe i a
    show PullbackSections.actR Xo.univ.t.act a (Pν (Pm.symm (C i))) = _
    refine (GlobalTheory.LieMet.pushE_act ν yy hyx a _).symm.trans ?_
    show Pν _ = _
    rw [h1, map_smul]
  have hN : ∀ i, ∃! a, IsCombAt y.x (y.u ρ) a (PullbackSections.tv (N i)).left := fun i =>
    y.basis ρ _ (GlobalTheory.LieMet.isTan_tv (N i)) fun a => by
      rw [← hσ]
      exact congrArg (fun v => (PullbackSections.tv v).left) (hNe i a)
  choose G hG using fun i => (hN i).exists
  refine ⟨fun i => (PullbackSections.tv (Pm.symm (C i))).left, G, fun i => ?_, fun i => ?_, fun h hu hd => ?_⟩
  · rw [hyy, ← GlobalTheory.LieMet.left_pushE Y.m yy hyy, LinearEquiv.apply_symm_apply]
    exact hCc i
  · rw [← GlobalTheory.LieMet.left_pushE ν yy hyx]
    exact hG i
  · obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    let Ub : Fin (Dw.mult ρ) → PullbackSections.TanM y.x Xo.univ.t.G := fun j => GlobalTheory.LieMet.tanOf (y.tan ρ j)
    have hNi : ∀ i, N i = ∑ j, G i j • Ub j := fun i => (GlobalTheory.LieMet.isComb_iff Ub (G i) (N i)).1 (hG i)
    have h0 : ∑ i, a i • N i = 0 := by
      simp only [hNi, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun ha j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    have h1 : ∑ i, a i • C i = 0 := by
      have : Pν (Pm.symm (∑ i, a i • C i)) = 0 := by
        rw [← h0]; simp only [map_sum, map_smul]; rfl
      exact Pm.symm.injective (Pν.injective (this.trans ((congrArg Pν (map_zero Pm.symm)).trans (map_zero Pν)).symm))
    let cv : Fin g → K := fun b => ∑ i, a i * φ (U i b)
    have h2 : ∑ i, a i • C i = ∑ b, cv b • Eb b := by
      simp only [C, cv, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : cv = 0 := by
      have hz := (GlobalTheory.LieMet.isComb_iff Eb cv 0).2 (h2.symm.trans h1).symm
      have hz' := (GlobalTheory.LieMet.isComb_iff Eb 0 0).2 (by simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero])
      exact (hbas.2 K φ _ (GlobalTheory.LieMet.isTan_tv 0)).unique hz hz'
    exact ha0 (rows_indep φ h U hu a fun b => congrFun h3 b)

end GlobalTheory.FlatModel.GenUniq

namespace GlobalTheory.FlatModel

theorem secValAt_unique_generic : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v → SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v' → v = v' := by
  intro _ _ _ E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x _ Z τ s la p Xw hp hcov A _ _ _ ξ β _ hξs _ hξX g e U₁
    h₁ U₂ h₂ hbas heig hu₁ hu₂
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  refine ⟨K, inferInstance, φ, IsFractionRing.injective A K, fun v v' hv hv' => ?_⟩
  have hsc : ∀ {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (f' : R₂ →+* R₃),
      spMap (f'.comp f) = spMap f' ≫ spMap f := fun f f' => by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hinj : ∀ {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (f f' : R₁ →+* R₂), spMap f = spMap f' → f = f' :=
    fun f f' h => congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)
  have hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hcov.2.2.1 Y
  have hrange : Set.range (spMap φ ≫ ξ) ⊆ Set.range Y.j := by
    rintro _ ⟨z, rfl⟩
    refine hcov.2.2.2.2.1 ?_
    have hz : (spMap φ).base z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap φ (z : PrimeSpectrum K).asIdeal = ⊥
      haveI := (z : PrimeSpectrum K).isPrime
      rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum K).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective A K)
    show ξ.base ((spMap φ).base z) ∈ Xw
    rw [hz]
    exact hξX
  let yy := IsOpenImmersion.lift Y.j (spMap φ ≫ ξ) hrange
  have hyy : yy ≫ Y.j = spMap φ ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  let ψ : c'.F →+* K := (Spec.preimage (yy ≫ pullback.snd _ _)).hom
  have hψ : spMap ψ = yy ≫ pullback.snd _ _ := Spec.map_preimage _
  letI : Algebra c.F K := (ψ.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hψβ : ψ.comp (c'.V W).subtype = φ.comp β := by
    refine hinj _ _ ?_
    rw [hsc, hsc, hψ, Category.assoc, ← GlobalTheory.LocM.BaseMdl.j_s, ← Category.assoc, hyy, Category.assoc, hξs]
  have hsnd : yy ≫ r ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [hcov.1, ← Category.assoc, ← hψ]
    exact (hsc _ _).symm
  have hx : (yy ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
    rw [sOf, hsc, ← hsnd]
    simp only [Category.assoc, pullback.condition]
  obtain ⟨y, hyx⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (yy ≫ r ≫ pullback.fst _ _) hx
  have hT : Tested y := GlobalTheory.NonIntegralFrameExample.spread_holds Xo c K y
  have hpt : GlobalTheory.AllWt.ptF y = yy ≫ r := by
    unfold GlobalTheory.AllWt.ptF
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hyx, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, hsnd]
  have hσ : ∀ (ρ : E →+* ℂ) (a : 𝓞 E), φ (β (embV c' W ρ a)) = algebraMap c.F K (embK c ρ a) := by
    intro ρ a
    rw [← RingHom.comp_apply φ β, ← hψβ]
    show ψ ((embV c' W ρ a : c'.V W) : c'.F) = ψ (IntermediateField.inclusion hle (embK c ρ a))
    congr 1
  obtain ⟨w₁, G₁, hw₁, hg₁, hd₁⟩ :=
    GenUniq.rows_data Y r ν ξ β φ e hbas yy hyy y hyx.symm τ.1 U₁ (heig K φ).1 (hσ τ.1)
  obtain ⟨w₂, G₂, hw₂, hg₂, -⟩ :=
    GenUniq.rows_data Y r ν ξ β φ e hbas yy hyy y hyx.symm (conjEmb τ.1) U₂ (heig K φ).2 (hσ _)
  have e₁ := hv inferInstance yy hyy y hT hpt w₁ w₂ G₁ G₂ hw₁ hw₂ hg₁ hg₂
  have e₂ := hv' inferInstance yy hyy y hT hpt w₁ w₂ G₁ G₂ hw₁ hw₂ hg₁ hg₂
  exact mul_right_cancel₀ (hd₁ h₁ hu₁) (e₁.trans e₂.symm)

end GlobalTheory.FlatModel

end
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_compatibility : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v → SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v' → v = v' := by
  atlas_forward_decl GlobalTheory.FlatModel.secValAt_unique_generic
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem genSt_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
    GenSt := by
  intro h1 h2 h3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A _ _ _ ξ β hξ hβ hpu hgen
    g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂
  haveI := GlobalTheory.T.integral_model_open_noetherian E H Dw l' Xo' c' W Y A ξ hξ
  obtain ⟨f, hf⟩ := GlobalTheory.T.property_of_codim_one_local_units A (SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂) {𝔭 | ξ 𝔭 ∈ Set.range Y.j} (hC.2.2.2.2.1 hgen)
    (fun 𝔭 h𝔭 => by
      by_cases hg : ξ 𝔭 ∈ Set.range Y.j
      · exact GlobalTheory.T.integral_model_map_extension h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
          g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂ 𝔭 hg
      · exact GlobalTheory.T.integral_model_map_uniqueness h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
          g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂ 𝔭 (h𝔭.resolve_left hg) hg)
    (GlobalTheory.T.integral_model_map_compatibility h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
                   g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂)
    (fun k _ φ v hv inst yy hyy => by
      exfalso
      apply hv
      refine ⟨yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
      have e1 : (yy ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) =
          (spMap φ ≫ ξ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := by rw [hyy]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        (e1.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg ξ (PrimeSpectrum.ext rfl)))))
  exact ⟨f, fun k _ _ φ yy hyy => hf k φ _ yy hyy⟩
end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_statement_of_canonical_extension : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GenSt := by
  atlas_forward_decl GlobalTheory.FlatModel.genSt_of_hypotheses
end
