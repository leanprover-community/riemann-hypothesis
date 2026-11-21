import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsForComponent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGeneratorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatiosStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelLeft
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelAddedCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjective

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_coords_descend_subfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (Ω₀ : Type) [Field Ω₀] [Algebra Ω₀ Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (d : ℕ), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) → IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) → IsGenericFlag (Ω' := Ω) j V₀ b d → (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y ∅ y') (g : 𝔐.X ⟶ X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K' → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ 𝔐.ξ ≫ g = ξ ∧ 𝔐.f = g ≫ f ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ Fl.deg = d ∧ Fl.RootLines xdeg e ∧ (∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = (M.pt (b s i)).left ≫ m.φ) ∧ (∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt 𝔐.ξ q' = regAt ξ ⟨g q'.1, h⟩) ∧ ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sat_model | exact GlobalTheory.CompanionTheory.Ar.exists_sat_model | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sat_model <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CharZeroModel

theorem charZero_of_flat {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (s : X ⟶ Spec (CommRingCat.of R)) [Flat s] {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : Function.Injective (Scheme.stalkClosedPointTo ξ).hom) : CharZero Ω := by
  classical
  set x := ξ.base (IsLocalRing.closedPoint Ω) with hx
  have hfl : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  have hgerm := germ_injective_of_isIntegral (X := Spec (CommRingCat.of R)) (U := ⊤) (x := s.base x)
    (hx := trivial)
  have hA : ∀ n : ℕ, n ≠ 0 → (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) ≠ 0 := by
    intro n hn h0
    apply (Nat.cast_ne_zero (R := R)).mpr hn
    apply hinv
    apply hgerm
    simp only [map_zero, map_natCast]
    exact h0
  have hO : ∀ n : ℕ, n ≠ 0 → (n : X.presheaf.stalk x) ≠ 0 := by
    intro n hn h0
    let _ := (s.stalkMap x).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) (X.presheaf.stalk x) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
      (mem_nonZeroDivisors_of_ne_zero (hA n hn))
    have h3 : (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (1 : X.presheaf.stalk x) =
        (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (0 : X.presheaf.stalk x) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one, map_natCast]
      exact h0
    exact one_ne_zero (hreg h3)
  exact charZero_of_inj_zero fun n hn => by
    by_contra hne
    apply hO n hne
    apply h
    rw [map_natCast, map_zero]
    exact hn

theorem charZero_function_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  have := Y.flat
  exact charZero_of_flat Y.s ξ₀ hξ.bij.1

end GlobalTheory.CompanionTheory.Ar.CharZeroModel
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_generic_char_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EmbedsOfTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isLocalRing_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem unitAt_iff_isUnit {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ) (s : regAt ξ p) :
    unitAt ξ p (s : Ω) ↔ IsUnit s := by
  constructor
  · rintro ⟨h0, -, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(s : Ω)⁻¹, hinv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · intro hs
    obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hs
    have ht' : (s : Ω) * (t : Ω) = 1 := by simpa using congrArg Subtype.val ht
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one ht'
    refine ⟨h0, s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2

theorem mem_adjoin_rat_of_int [CharZero Ω] {S : Set Ω} {a : Ω} (h : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin ℚ S := by
  induction h using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem embedsGeneric_of_coordTie : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  intro X Ω _ _ ξ κ x h
  unfold EmbedsGeneric
  intro p _
  refine ⟨h.cover p, fun i hi => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h i p hi a).mp ha
    exact ⟨s, mem_adjoin_rat_of_int hs, hu, mem_adjoin_rat_of_int hsa⟩
  · intro q _ hq hpq
    haveI := isLocalRing_regAt h.gen p
    have hmem : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x i), a ∈ regAt ξ p :=
      fun a ha => (h.ring i hi.1 a).mp ha p hi
    let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x i) →+* regAt ξ p :=
      { toFun := fun s => ⟨s, hmem s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x i)) :=
      Ideal.comap φ (IsLocalRing.maximalIdeal (regAt ξ p))
    have hI : I.IsPrime := Ideal.comap_isPrime φ _
    have key : ∀ s : Algebra.adjoin ℤ (Set.range fun j => x j / x i), s ∉ I ↔ unitAt ξ p (s : Ω) := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact (unitAt_iff_isUnit p (φ s)).symm
    obtain ⟨p', -, huniq⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x h i hi.1 I hI
    have e1 := huniq p ⟨hi, key⟩
    have e2 := huniq q ⟨hq, fun s => (key s).trans (hpq s (mem_adjoin_rat_of_int s.2))⟩
    exact e1.trans e2.symm

end GlobalTheory.CompanionTheory.Ar.EmbedsOfTie
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeds_generic_of_char_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coords_for_component : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω₀ Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) ∧ (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_eigBase | exact GlobalTheory.CompanionTheory.Ar.exists_eigBase | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_eigBase <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

section Surj

variable {X : Scheme.{0}}

theorem germ_closedPoint_eq_appLE {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (U : X.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Scheme.Hom.appLE]
  rfl

theorem val_comp_spec {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S] (φ : R ⟶ S) (z : Spec R ⟶ X)
    (w : Spec S ⟶ X) (hw : Spec.map φ ≫ z = w) (U : X.Opens)
    (h1 : z (IsLocalRing.closedPoint R) ∈ U) (h2 : w (IsLocalRing.closedPoint S) ∈ U) (t : Γ(X, U)) :
    φ.hom ((Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ U _ h1).hom t)) =
      (Scheme.stalkClosedPointTo w).hom ((X.presheaf.germ U _ h2).hom t) := by
  subst hw
  have key : (Spec.map φ ≫ z).appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem _ h2).ge ≫
      (Scheme.ΓSpecIso S).hom =
      z.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge ≫ (Scheme.ΓSpecIso R).hom ≫ φ := by
    have e₂ : (⊤ : (Spec S).Opens) ≤ (Spec.map φ) ⁻¹ᵁ ⊤ := by simp
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) z U ⊤ ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge e₂,
      Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e1 := congrArg (fun g => (g ≫ φ).hom t) (germ_closedPoint_eq_appLE z U h1)
  have e2 := congrArg (fun g => g.hom t) (germ_closedPoint_eq_appLE (Spec.map φ ≫ z) U h2)
  have e3 := congrArg (fun g => g.hom t) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1 e2 e3
  rw [e1, e2, e3]

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Ω' : Type} [Field Ω']

def DomAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω') (A : ValuationSubring Ω') (p : Cpt ξ) : Prop :=
  ∃ ν : X.presheaf.stalk p.1 →+* A, IsLocalHom ν ∧ ∀ s, (ν s : Ω') = i (genMap ξ p s)

theorem DomAt.inv_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p) {a : Ω}
    (h0 : a ≠ 0) (ha : a ∈ regAt ξ p) (hi : i a⁻¹ ∈ A) : a⁻¹ ∈ regAt ξ p := by
  obtain ⟨ν, hloc, hν⟩ := h
  obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
  have hu : IsUnit (ν s) := by
    refine IsUnit.of_mul_eq_one (a := ν s) ⟨i (genMap ξ p s)⁻¹, hi⟩ ?_
    apply Subtype.ext
    show (ν s : Ω') * i (genMap ξ p s)⁻¹ = 1
    rw [hν s, ← map_mul, mul_inv_cancel₀ h0, map_one]
  have hs : IsUnit s := (isUnit_map_iff ν s).mp hu
  refine RingHom.mem_range.mpr ⟨↑hs.unit⁻¹, ?_⟩
  rw [map_units_inv, IsUnit.unit_spec]

theorem genMap_germ (r : Cpt ξ) {U : X.Opens} (hr : r.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ r ((X.presheaf.germ U r.1 hr).hom t) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr)).hom t) := by
  have e := congrArg (fun g => g.hom t) (X.presheaf.germ_stalkSpecializes hr r.2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes r.2).hom ((X.presheaf.germ U r.1 hr).hom t)) = _
  rw [e]

theorem DomAt.eq_of_mem_affine {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p p' : Cpt ξ} (h : DomAt ξ i A p)
    (h' : DomAt ξ i A p') {U : X.Opens} (hU : IsAffineOpen U) (hp : p.1 ∈ U) (hp' : p'.1 ∈ U) : p.1 = p'.1 := by
  obtain ⟨ν, hν1, hν⟩ := h
  obtain ⟨ν', hν1', hν'⟩ := h'
  have key : ∀ b : Γ(X, U), p.1 ∈ X.basicOpen b ↔ p'.1 ∈ X.basicOpen b := by
    intro b
    have e : ν ((X.presheaf.germ U p.1 hp).hom b) = ν' ((X.presheaf.germ U p'.1 hp').hom b) := by
      apply Subtype.ext
      simp only [hν, hν', genMap_germ]
    rw [X.mem_basicOpen b p.1 hp, X.mem_basicOpen b p'.1 hp', ← isUnit_map_iff ν, ← isUnit_map_iff ν', e]
  have sp : ∀ {a c : X}, a ∈ U → c ∈ U → (∀ b : Γ(X, U), a ∈ X.basicOpen b → c ∈ X.basicOpen b) → c ⤳ a := by
    intro a c ha hc hab
    rw [specializes_iff_forall_open]
    intro s hs has
    obtain ⟨b, hb, hab'⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨a, has⟩ ha
    exact hb (hab b hab')
  exact ((sp hp' hp (fun b => (key b).2)).antisymm (sp hp hp' (fun b => (key b).1))).eq

theorem domAt_of_spec {i : Ω →+* Ω'} {A : ValuationSubring Ω'} (z : Spec (CommRingCat.of A) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ ξ)
    (h : genPt ξ ⤳ z (IsLocalRing.closedPoint A)) :
    DomAt ξ i A ⟨z (IsLocalRing.closedPoint A), h⟩ := by
  refine ⟨(Scheme.stalkClosedPointTo z).hom, inferInstance, fun s => ?_⟩
  obtain ⟨U, hU, t, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : genPt ξ ∈ U := h.mem_open U.isOpen hU
  have hw : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') ∈ U := by
    rw [← hz]
    exact ((IsLocalRing.specializes_closedPoint _).map z.continuous).mem_open U.isOpen hU
  have e1 := val_comp_spec (CommRingCat.ofHom (algebraMap A Ω')) z _ hz U hU hw t
  have e2 := val_comp_spec (CommRingCat.ofHom i) ξ _ rfl U hg hw t
  have e3 := congrArg i (genMap_germ (ξ := ξ) ⟨z (IsLocalRing.closedPoint A), h⟩ hU t)
  exact e1.trans (e2.symm.trans e3.symm)

private theorem exists_domAt_of_injective_genMap (i : Ω →+* Ω') (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p)) :
    ∃ A : ValuationSubring Ω', DomAt ξ i A p := by
  let g : X.presheaf.stalk p.1 →+* Ω' := i.comp (genMap ξ p)
  have hg : Function.Injective g := i.injective.comp hinj
  obtain ⟨A, hA⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range g)
  obtain ⟨hle, hloc⟩ := hA
  have hmem : ∀ s, g s ∈ A.toSubring := fun s => hle ⟨s, rfl⟩
  refine ⟨A, g.codRestrict A.toSubring hmem, ⟨fun s hs => ?_⟩, fun s => rfl⟩
  obtain ⟨v, hv⟩ := hs.exists_right_inv
  have hv' : g s * (v : Ω') = 1 := congrArg Subtype.val hv
  let y : (LocalSubring.range g).toSubring := ⟨g s, ⟨s, rfl⟩⟩
  have hy : IsUnit y := by
    apply hloc.map_nonunit
    refine IsUnit.of_mul_eq_one ⟨v, v.2⟩ ?_
    exact Subtype.ext hv'
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨s', hs'⟩ := w.2
  refine IsUnit.of_mul_eq_one s' ?_
  apply hg
  rw [map_mul, map_one, hs']
  exact congrArg Subtype.val hw

private theorem inChart_of_domAt_of_div_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p)
    {κ : Type} {x : κ → Ω} {c : κ} (hxc : x c ≠ 0) (hA : ∀ c', i (x c' / x c) ∈ A) {c'' : κ}
    (h'' : InChart ξ x c'' p) : InChart ξ x c p := by
  refine ⟨hxc, fun c' => ?_⟩
  have hc'' : x c'' ≠ 0 := h''.1
  have h1 : x c / x c'' ∈ regAt ξ p := h''.2 c
  have h0 : x c / x c'' ≠ 0 := div_ne_zero hxc hc''
  have h2 : (x c / x c'')⁻¹ ∈ regAt ξ p := h.inv_mem h0 h1 (by rw [inv_div]; exact hA c'')
  have e : x c' / x c = (x c' / x c'') * (x c / x c'')⁻¹ := by
    rw [inv_div, div_mul_div_cancel₀ hc'']
  rw [e]
  exact mul_mem (h''.2 c') h2

private theorem div_mem_of_valuation_le {K : Type} [Field K] (A : ValuationSubring K) {a b : K} (hb : b ≠ 0)
    (h : A.valuation a ≤ A.valuation b) : a / b ∈ A := by
  rw [← A.valuation_le_one_iff, map_div₀]
  have hb' : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  exact div_le_one_of_le₀ h zero_le'

theorem surjective_of_dominates (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type)
    [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω') (hc : CoordTie ℤ ξ x)
    (hg : ∀ q : X, genPt ξ ⤳ q) (hp : IsProper s') (hd : Dominates ξ' ξ f i) : Function.Surjective f := by
  intro q
  obtain ⟨A, hdom⟩ := exists_domAt_of_injective_genMap i ⟨q, hg q⟩ (hc.gen.inj ⟨q, hg q⟩)
  have hex : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s' := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    infer_instance
  let S : ValuativeCommSq s' :=
    { R := A, K := Ω', i₁ := ξ', i₂ := specZIsTerminal.from _, commSq := ⟨specZIsTerminal.hom_ext _ _⟩ }
  obtain ⟨⟨l, hl1, -⟩⟩ := (hex.1 S).exists_lift
  have hl : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ l = ξ' := hl1
  have hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ (l ≫ f) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [← Category.assoc, hl]
    exact hd
  have hdom' := domAt_of_spec (i := i) (A := A) (l ≫ f) hz (hg _)
  obtain ⟨c₁, hc₁⟩ := hc.cover ⟨q, hg q⟩
  have : Nonempty κ := ⟨c₁⟩
  obtain ⟨c, hcmax⟩ := Finite.exists_max (fun c => A.valuation (i (x c)))
  have hxc : x c ≠ 0 := by
    intro h0
    have h1 := hcmax c₁
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hc₁.1 ((map_eq_zero i).1 h1)
  have hA : ∀ c', i (x c' / x c) ∈ A := fun c' => by
    rw [map_div₀]
    exact div_mem_of_valuation_le A ((map_ne_zero i).2 hxc) (hcmax c')
  obtain ⟨U, hUaff, hUmem⟩ := hc.affine c hxc
  have hq : q ∈ U := (hUmem q).2 ⟨hg q, inChart_of_domAt_of_div_mem hdom hxc hA hc₁⟩
  obtain ⟨c₂, hc₂⟩ := hc.cover ⟨(l ≫ f) (IsLocalRing.closedPoint A), hg _⟩
  have hq' : (l ≫ f) (IsLocalRing.closedPoint A) ∈ U :=
    (hUmem _).2 ⟨hg _, inChart_of_domAt_of_div_mem hdom' hxc hA hc₂⟩
  have e := DomAt.eq_of_mem_affine hdom hdom' hUaff hq hq'
  exact ⟨l (IsLocalRing.closedPoint A), e.symm⟩

end Surj
end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_dominating_surjective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω'), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → IsProper s' → Dominates ξ' ξ f i → Function.Surjective f := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.FlagBun in
theorem GlobalTheory.CompanionTheory.Ar.exists_flagBundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L hx hirr hL
  classical
  have hc : ∀ s, ∃ c : Fin (r s) → E, LinearIndependent Ω c ∧ Submodule.span Ω (Set.range c) = V s := by
    intro s
    obtain ⟨U, hU, b, hb, hfr⟩ := hL s ⟨genPt ξ, specializes_refl _⟩ trivial
    exact ⟨b, (hfr ⟨genPt ξ, specializes_refl _⟩ trivial hU).1, hb⟩
  choose c hc using hc
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x (L s) m φ :=
    fun s => GlobalTheory.T.exists_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) hx hirr (hL s)
  choose m n φ hφ using hg
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt ξ, specializes_refl _⟩
  have hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1 :=
    fun s => GlobalTheory.T.frame_via_twisted_generators X Ω ξ E κ x (L s) (r s) (V s) (m s) (n s) (φ s) (c s) hx (hL s) (hφ s) (hc s).1 (hc s).2
  obtain ⟨J₀, hJ₀, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω E S r n κ x φ c c₀ hc₀.1 (GlobalTheory.T.function_field_ratio_generators X Ω ξ κ x c₀ hx hc₀.1) hB
  haveI : Finite (FlagIx κ n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx κ n r) (flagCoord κ x φ c) J₀ hJ₀ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular X Ω ξ ℤ κ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simpa using intCast_mem (regAt ξ' p') z) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord κ x φ c (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsurj := GlobalTheory.T.proper_dominating_surjective X Ω ξ κ x X' (GenField Ω r) ξ' s' f _ hx hirr hprop hdom
  have hsm := GlobalTheory.T.flag_frames_generic_model_right X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hfl := GlobalTheory.T.flag_frames_generic_model_left X Ω ξ E κ x S r V L m n φ c X' ξ' f hx hirr hL hφ hc hx' hirr' hdom hch
  have hgen := GlobalTheory.T.generic_flag_over_generic_field Ω E S r V c hc
  have hne : Nonempty (FlagIx κ n r) := ⟨J₀⟩
  have hpos : 0 < Nat.card (FlagIx κ n r) := Nat.card_pos
  let e : Fin (Nat.card (FlagIx κ n r) - 1 + 1) ≃ FlagIx κ n r :=
    (finCongr (Nat.sub_add_cancel hpos)).trans (Finite.equivFin (FlagIx κ n r)).symm
  exact ⟨X', GenField Ω r, inferInstance, inferInstance, ξ', f, _, flagCoord κ x φ c ∘ e, genB c,
    (by convert coordTie_comp_equiv hx' e using 1 <;> first | exact Subsingleton.elim _ _ | skip), hirr', hdom, hsm, hsurj, hgen, hfl⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_vector_bundles : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.exists_flagBundle
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem block_ratio_mem {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {c : (k : K) → J k} {p : Cpt ξ}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : J k) :
    y ⟨k, c k⟩ ≠ 0 ∧ y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  obtain ⟨h0, hc⟩ := hc
  have hck : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 h0) k (Finset.mem_univ k)
  refine ⟨hck k, ?_⟩
  have h := hc (Function.update c k i)
  have e : (∏ k', y ⟨k', Function.update c k i k'⟩) / (∏ k', y ⟨k', c k'⟩) = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      rw [Function.update_of_ne hb]
      exact div_self (hck b)
    · simp
  rw [← e]
  exact h

theorem tie_blocks : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' _ hy hx hd
  have h1 : CoordTie ℤ ξ' (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x' p.2) ⟨k, c' k⟩) := by
    simpa using CoordBase.coordTie_reindex (Equiv.funUnique Unit (Fin (N + 1))) hx
  have h2 : ∀ (k : K) (p : Cpt ξ'), ∃ i, InChart ξ'
      (fun i' : J k => (fun p : (Σ k, J k) => algebraMap Ω₀ Ω (y p)) ⟨k, i'⟩) i p := by
    intro k p
    obtain ⟨h, hreg, -⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f (algebraMap Ω₀ Ω) hd p
    obtain ⟨c, hc⟩ := hy.cover ⟨f p.1, h⟩
    refine ⟨c k, ?_, fun i => ?_⟩
    · exact (map_ne_zero _).2 (block_ratio_mem hc k (c k)).1
    · have := hreg _ (block_ratio_mem hc k i).2
      rwa [map_div₀] at this
  have h3 := GlobalTheory.T.coords_join_blocks X' Ω ξ' Unit (fun _ => Fin (N + 1)) (fun p => x' p.2) K J
    (fun p => algebraMap Ω₀ Ω (y p)) h1 h2
  convert h3 using 2 with c'
  exact Fintype.prod_sum_type _

end GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_added_projective : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict

variable {X X' : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]

theorem valAt_unique {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (hg : IsCptGen ξ')
    {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a : Ω} {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z a t) :
    r = t := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  have e : s₁ = s₂ := hg.inj ⟨centre z, hA⟩ (hs₁.trans hs₂.symm)
  rw [← hr, ← ht, e]

theorem valAt_mul {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a b : Ω}
    {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z b t) : ValAt ξ' z (a * b) (r * t) := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  exact ⟨hA, s₁ * s₂, by rw [map_mul, hs₁, hs₂],
    (map_mul _ s₁ s₂).trans (congrArg₂ (· * ·) hr ht)⟩

theorem valAt_one {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h : genPt ξ' ⤳ centre z) : ValAt ξ' z (1 : Ω) 1 :=
  ⟨h, 1, map_one _, map_one _⟩

theorem isUnit_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (s : A) (h : φ s ≠ 0) :
    IsUnit s := by
  exact IsUnit.of_map φ s (Ne.isUnit h)

theorem unitAt_of_valAt {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : ℂ} (hr : r ≠ 0) (hv : ValAt ξ' z a r) :
    unitAt ξ' ⟨centre z, h'⟩ a := by
  obtain ⟨h, s, hs, hr'⟩ := hv
  have hu : IsUnit s := isUnit_of_local (Scheme.stalkClosedPointTo z).hom s (by rw [hr']; exact hr)
  obtain ⟨u, rfl⟩ := hu
  have hinv : genMap ξ' ⟨centre z, h'⟩ ↑u⁻¹ * genMap ξ' ⟨centre z, h'⟩ ↑u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : genMap ξ' ⟨centre z, h'⟩ ↑u ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hinv
    exact zero_ne_one hinv
  refine ⟨?_, ⟨↑u, hs⟩, ⟨↑u⁻¹, ?_⟩⟩
  · rw [← hs]; exact hne
  · rw [← hs]; exact eq_inv_of_mul_eq_one_left hinv

private theorem stalkSpecializes_comp_stalkClosedPointTo_congr {K : Type} [Field K] (g₁ g₂ : Spec (CommRingCat.of K) ⟶ X)
    (e : g₁ = g₂) {q : X} (h₁ : g₁ (IsLocalRing.closedPoint K) ⤳ q) (h₂ : g₂ (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo g₁ =
      X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo g₂ := by
  subst e; rfl

private theorem stalkSpecializes_comp_stalkClosedPointTo_specMap_comp {K K' : Type} [Field K] [Field K'] (i : K →+* K')
    (g : Spec (CommRingCat.of K) ⟶ X) {q : X}
    (h₂ : (Spec.map (CommRingCat.ofHom i) ≫ g) (IsLocalRing.closedPoint K') ⤳ q)
    (hp : g (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ g) =
      X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom i := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.germ_stalkClosedPointTo, Scheme.germ_stalkClosedPointTo_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality]
  simp only [← Category.assoc]
  congr 1

theorem valAt_of_regAt {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ X}
    {i : Ω₀ →+* Ω} (hd : Dominates ξ' ξ f i) (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h' : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) {a : Ω₀}
    (ha : a ∈ regAt ξ ⟨f (centre z), hp⟩) :
    ∃ r : ℂ, ValAt ξ (z ≫ f) a r ∧ ValAt ξ' z (i a) r := by
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 ha
  refine ⟨(Scheme.stalkClosedPointTo (z ≫ f)).hom s, ⟨hp, s, hs, rfl⟩, h', (f.stalkMap (centre z)).hom s, ?_, ?_⟩
  · have h₁ : (ξ' ≫ f) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := f.base.hom.map_specializes h'
    have h₂ : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := by
      rw [← hd]; exact h₁
    have h'' : ξ' (IsLocalRing.closedPoint Ω) ⤳ centre z := h'
    have hp'' : ξ (IsLocalRing.closedPoint Ω₀) ⤳ f (centre z) := hp
    have key : f.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h'' ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes hp'' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      rw [← Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap, Category.assoc,
        ← Scheme.stalkClosedPointTo_comp]
      exact (stalkSpecializes_comp_stalkClosedPointTo_congr (ξ' ≫ f) (Spec.map (CommRingCat.ofHom i) ≫ ξ) hd h₁ h₂).trans
        (stalkSpecializes_comp_stalkClosedPointTo_specMap_comp i ξ h₂ hp'')
    have := congrArg (fun φ => φ.hom s) key
    rw [← hs]
    exact this
  · rw [Scheme.stalkClosedPointTo_comp]
    rfl

theorem coordsAt_restrict : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' z w hgen htie hcpt hgen' hd hc
  classical
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨fun k => hc1 (Sum.inr k), fun k c hu => ?_⟩
  have hyA : ∀ j : J k, addY y x' ⟨Sum.inr k, j⟩ = algebraMap Ω₀ Ω (y ⟨k, j⟩) := fun j => rfl
  obtain ⟨hy, hv⟩ := hc2 (Sum.inr k) c hu
  rw [hyA] at hy
  have hyc : y ⟨k, c⟩ ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
  refine ⟨hyc, fun j => ?_⟩
  have hp : genPt ξ ⤳ f (centre z) := hgen _
  have h' : genPt ξ' ⤳ centre z := hgen' _
  obtain ⟨c₀, hc₀ne, hc₀⟩ := htie.cover ⟨f (centre z), hp⟩
  have hx0 : (∏ k', y ⟨k', c₀ k'⟩) ≠ 0 := hc₀ne
  have hy0 : y ⟨k, c₀ k⟩ ≠ 0 := fun h0 => hx0 (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  have hprod : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) * y ⟨k, c₀ k⟩ =
      (∏ k', y ⟨k', c₀ k'⟩) * y ⟨k, j⟩ := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c₀ k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c₀ k'⟩) (Finset.mem_univ k)]
    have e : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update c₀ k j x⟩ =
        ∏ x ∈ Finset.univ.erase k, y ⟨x, c₀ x⟩ :=
      Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    simp only [Function.update_self]
    rw [e]
    ring
  have hratio : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) / (∏ k', y ⟨k', c₀ k'⟩) =
      y ⟨k, j⟩ / y ⟨k, c₀ k⟩ := by
    intro j
    rw [div_eq_div_iff hx0 hy0, hprod j, mul_comm]
  have hreg : ∀ j : J k, y ⟨k, j⟩ / y ⟨k, c₀ k⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := fun j => by
    rw [← hratio j]
    exact hc₀ (Function.update c₀ k j)
  obtain ⟨r₂, hr₂a, hr₂b⟩ := valAt_of_regAt hd z h' hp (hreg c)
  obtain ⟨r₀, hr₀, -⟩ := hv (c₀ k)
  rw [hyA, hyA] at hr₀
  have hmul := valAt_mul hr₂b hr₀
  have hy0' : algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) ≠ 0 := (map_ne_zero _).2 hy0
  have hone : algebraMap Ω₀ Ω (y ⟨k, c⟩ / y ⟨k, c₀ k⟩) *
      (algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) / algebraMap Ω₀ Ω (y ⟨k, c⟩)) = 1 := by
    rw [map_div₀]
    field_simp
  rw [hone] at hmul
  have h1 : r₂ * r₀ = 1 := valAt_unique hcpt hmul (valAt_one h')
  have hr₂ne : r₂ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hunit := unitAt_of_valAt hp hr₂ne hr₂a
  have hinvreg : (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ ∈ regAt ξ ⟨f (centre z), hp⟩ := hunit.2.2
  have hregjc : y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := by
    have e : y ⟨k, j⟩ / y ⟨k, c⟩ = (y ⟨k, j⟩ / y ⟨k, c₀ k⟩) * (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ := by
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hreg j) hinvreg
  obtain ⟨r, hr1, hr2⟩ := valAt_of_regAt hd z h' hp hregjc
  obtain ⟨r', hr', hw⟩ := hv j
  rw [hyA, hyA] at hr'
  rw [map_div₀] at hr2
  have e3 : r = r' := valAt_unique hcpt hr2 hr'
  refine ⟨r, hr1, ?_⟩
  rw [e3]
  exact hw

end GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coords_added : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_action_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X)
    (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω')
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω' V')
    (j : V →+ V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) →
    ∀ a e, j (ρ a e) = ρ' a (j e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | exact GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.lieMap_act_pull <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.Transport

theorem flagStep_equiv {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (Φ : F ≃ₗ[Ω] F') {r : ℕ} (b : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (b k)) i = (flagStep Ω b i).map Φ.toLinearMap := by
  rw [flagStep, flagStep, Submodule.map_span, Set.image_image]
  rfl

theorem isGenericFlag_transport : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  intro Ω₀ Ω _ _ _ E₀ E F F' _ _ _ _ _ _ _ _ a j Φ S r V V₀ b d hV hG
  obtain ⟨c, u, hc, hjlin, hjc, hb, hu1, hu0, hflag, halg, hd, hrank⟩ := hG
  refine ⟨fun σ k => a.symm (c σ k), u, fun σ => ⟨?_, ?_⟩, ?_, fun σ => ?_, fun σ => ?_, hu1, hu0,
    fun σ i => ?_, halg, hd, hrank⟩
  · exact (hc σ).1.map' a.symm.toLinearMap a.symm.ker
  · have h1 : Submodule.span Ω₀ (Set.range fun k => a.symm (c σ k)) =
        (Submodule.span Ω₀ (Set.range (c σ))).map a.symm.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, (hc σ).2]
    ext e
    rw [hV σ e, Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  · intro x e
    show Φ (j (a (x • e))) = algebraMap Ω₀ Ω x • Φ (j (a e))
    rw [map_smul, hjlin, map_smul]
  · have hfe : (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom)
        (a.symm (c σ k))) = ⇑Φ.toLinearMap ∘ fun k => j (c σ k) := by
      funext k
      show Φ (j (a (a.symm (c σ k)))) = Φ (j (c σ k))
      rw [LinearEquiv.apply_symm_apply]
    have h3 : LinearIndependent Ω (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp
        a.toLinearMap.toAddMonoidHom) (a.symm (c σ k))) := by
      rw [hfe]
      exact (hjc σ).map' Φ.toLinearMap Φ.ker
    exact h3
  · exact (hb σ).map' Φ.toLinearMap Φ.ker
  · have hfun : (fun k => ∑ l, u σ l k •
        ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) =
        fun k => Φ (∑ l, u σ l k • j (c σ l)) := by
      funext k
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      show u σ l k • Φ (j (a (a.symm (c σ l)))) = u σ l k • Φ (j (c σ l))
      rw [LinearEquiv.apply_symm_apply]
    calc flagStep Ω (fun k => Φ (b σ k)) i = (flagStep Ω (b σ) i).map Φ.toLinearMap := flagStep_equiv Φ (b σ) i
      _ = (flagStep Ω (fun k => ∑ l, u σ l k • j (c σ l)) i).map Φ.toLinearMap := by rw [hflag σ i]
      _ = flagStep Ω (fun k => Φ (∑ l, u σ l k • j (c σ l))) i := (flagStep_equiv Φ _ i).symm
      _ = flagStep Ω (fun k => ∑ l, u σ l k •
          ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) i := by
        rw [hfun]

end GlobalTheory.CompanionTheory.Ar.FlagStep.Transport
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_under_equiv : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FlagStep.Transport.isGenericFlag_transport
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_constants_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | exact GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem card_strictLower (n : ℕ) [Fintype {lk : Fin n × Fin n // lk.2 < lk.1}] :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n.choose 2 := by
  let e : {lk : Fin n × Fin n // lk.2 < lk.1} ≃ Σ i : Fin n, Fin i.val :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2.val, x.2⟩⟩
      invFun := fun y => ⟨(y.1, ⟨y.2.val, y.2.2.trans y.1.2⟩), y.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

theorem choose_two_add (p q : ℕ) :
    (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + k) 1, Nat.choose_succ_succ' k 1, ih,
      Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem dim_add_card_strictLower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (c : Coeff l) [Fintype (CMType H)] [Fintype (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1})],
    D.dim + Fintype.card (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Top.dimFl (CMType H) (D.p + D.q) := by
  intro E _ _ _ H D l c _ _
  have hc : 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
    have h := (GlobalTheory.CompanionTheory.Ar.labels_all_once E H l c).2
    rw [Nat.card_eq_fintype_card, Fintype.card_sum] at h
    omega
  have hs : Fintype.card (Σ s : CMType H ⊕ CMType H,
      {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Fintype.card (CMType H) * D.p.choose 2 + Fintype.card (CMType H) * D.q.choose 2 := by
    classical
    rw [← Nat.card_eq_fintype_card, Nat.card_sigma, Fintype.sum_sum_type]
    simp only [Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inl a))),
      Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inr a)))]
    simp only [labelRk, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hs, Top.dimFl, Datum.dim, ← hc, ← Nat.choose_two_right, choose_two_add,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dimension_plus_flag_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (c : Coeff l) [Fintype (CMType H)] [Fintype (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1})],
    D.dim + Fintype.card (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Top.dimFl (CMType H) (D.p + D.q) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FlagStep.dim_add_card_strictLower
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower

theorem adjoin_lower_eq_top : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (S : Type) (r : S → ℕ)
    (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω),
    (∀ σ k, u σ k k = 1) → (∀ σ l k, l < k → u σ l k = 0) →
    Module.finrank (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω = 1 →
    IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) = ⊤ := by
  intro Ω₀ Ω _ _ _ S r u hdiag hup hfin
  rw [IntermediateField.finrank_eq_one_iff_eq_top] at hfin
  rw [← hfin]
  apply le_antisymm
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨⟨σ, ⟨l, k⟩, _⟩, rfl⟩
    exact ⟨⟨σ, l, k⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨σ, l, k⟩, rfl⟩
    rcases lt_trichotomy l k with h | h | h
    · simp only [hup σ l k h]
      exact zero_mem _
    · subst h
      simp only [hdiag σ l]
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨l, k⟩, h⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_entries_field_degree : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (S : Type) (r : S → ℕ)
    (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω),
    (∀ σ k, u σ k k = 1) → (∀ σ l k, l < k → u σ l k = 0) →
    Module.finrank (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω = 1 →
    IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower.adjoin_lower_eq_top
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

set_option maxHeartbeats 1000000 in
open GlobalTheory.CompanionTheory.Ar.FlagStep in

theorem GlobalTheory.CompanionTheory.Ar.exists_flagStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω₀ Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), IsCptGen ξ₀ → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ξ ≫ f = ξ₀ → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) → (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) → Cmp.IsSncModel y D.dim bd → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G)) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra Ω₀ Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module Ω₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) ∧ IsGenericFlag (Ω' := Ω) j V₀ b 1 ∧ (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) ∧ Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  classical
  intro E _ _ _ H D l Xo c Y Ω₀ _ _ ξ₀ K _ J _ y X ξ f cst t m Li _ _ M ρ L bd hgen hall htie hξ hcst hact hvb hLeq hsnc hbd
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  obtain ⟨X', Ω', _, _, ξ', f', N, x', b₁, htie', hall', hdom, hsm, -, hgf, hfl⟩ :=
    GlobalTheory.T.exists_model_vector_bundles X Ω₀ ξ Li ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) (CMType H ⊕ CMType H) (labelRk D)
      (fun s => eigSp ρ (cst.comp (labelEmb c s))) L htie hall hvb
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω₀ Ω').injective
  have hg : IsCptGen ξ := htie.gen
  have hg' : IsCptGen ξ' := htie'.gen
  obtain ⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H X', Nonempty (SABMap t' t f') := by
    obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.proved_CubePullSt f' t
    exact ⟨_, ⟨m₁⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H Y.X X X' Y.t t t' f f' m m₁
  obtain ⟨Li', _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t'.G Ω' ξ'
  obtain ⟨ρ', hact', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom
    t'.act.one t'.act.mul t'.act.add
  obtain ⟨j', hj₁, hj₂, hj₃, hj₄, hj₅⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' f' m₁ Ω₀ Ω' ξ ξ' (algebraMap Ω₀ Ω') Li Li' M M'
    hg hg' hdom
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G Ω₀ ξ₀
  have hdom₀ : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (RingHom.id Ω₀) := by
    show ξ ≫ f = _
    rw [hξ]
    simp
  obtain ⟨a₀, ha₁, ha₂, ha₃, ha₄, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H Y.X Y.t X t f m Ω₀ Ω₀ ξ₀ ξ (RingHom.id Ω₀) Li₀ Li M₀ M
    hgen hg hdom₀

  let aL : Li₀ →ₗ[Ω₀] Li := { toFun := a₀, map_add' := a₀.map_add, map_smul' := fun c e => ha₂ c e }
  have hainj : Function.Injective aL := by
    refine (injective_iff_map_eq_zero aL).2 fun e he => ?_
    by_contra hne
    have h1 := ha₃ 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hasurj : Function.Surjective aL := by
    have : LinearMap.range aL = ⊤ := by
      rw [eq_top_iff, ← ha₄]
      exact Submodule.span_le.2 (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
    exact LinearMap.range_eq_top.1 this
  let a : Li₀ ≃ₗ[Ω₀] Li := LinearEquiv.ofBijective aL ⟨hainj, hasurj⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.tensor_equiv_of_basis_extension Ω₀ Ω' Li Li' j' hj₂ hj₃ hj₄
  have hjinj : Function.Injective j' := by
    refine (injective_iff_map_eq_zero j').2 fun e he => ?_
    by_contra hne
    have h1 := hj₃ 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  have hint := GlobalTheory.T.lie_model_pullback_action_ring E H X X' t t' f' m₁ Ω₀ Ω' ξ ξ' (algebraMap Ω₀ Ω') Li Li' M M' ρ ρ' j' hdom hact hact' hj₁
  have hjΦ : Φ.toLinearMap.toAddMonoidHom.comp (TensorProduct.mk Ω₀ Ω' Li 1).toAddMonoidHom = j' :=
    AddMonoidHom.ext hΦ
  let cst' : c.F →+* Ω' := (algebraMap Ω₀ Ω').comp cst
  have heig : ∀ (σ : 𝓞 E →+* Ω₀) e, j' e ∈ eigSp ρ' ((algebraMap Ω₀ Ω').comp σ) ↔ e ∈ eigSp ρ σ := by
    intro σ e
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← hint a e, RingHom.comp_apply, ← hj₂]
    exact hjinj.eq_iff
  let V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀ := fun s => (eigSp ρ (cst.comp (labelEmb c s))).comap aL
  have hgf' := GlobalTheory.T.generic_flag_under_equiv Ω₀ Ω' Li₀ Li _ Li' a _ Φ _ (labelRk D) _ V₀ b₁ 1 (fun s e => Iff.rfl) hgf
  obtain ⟨cc, u, -, -, -, -, hu1, hu0, -, halg, -, hfr⟩ := hgf
  have htop := GlobalTheory.T.unipotent_entries_field_degree Ω₀ Ω' _ (labelRk D) u hu1 hu0 hfr
  have hgf'' : IsGenericFlag (Ω' := Ω') (j'.comp aL.toAddMonoidHom) V₀ (fun s k => Φ (b₁ s k)) 1 := by
    rw [← hjΦ]
    exact hgf'
  have hg'' : IsCptGen ξ' := hg'
  have tie₁ := GlobalTheory.T.coords_added_projective X X' Ω₀ Ω' ξ ξ' f' K J y N x' hall htie htie' hdom
  have snc₁ := GlobalTheory.T.snc_model_added_coords X X' Ω₀ Ω' ξ ξ' f' K J y N x' D.dim bd _ _ hall hall' htie tie₁ hdom hsm halg htop hsnc
  rw [GlobalTheory.T.dimension_plus_flag_count E H D l c] at snc₁
  refine ⟨Ω', inferInstance, inferInstance, inferInstance, Unit ⊕ K, inferInstance, addJ J N, inferInstance,
    addY y x', X', ξ', f' ≫ f, cst', t', n, Li', inferInstance, inferInstance, M', ρ', Li₀, inferInstance,
    inferInstance, M₀, j'.comp aL.toAddMonoidHom, V₀, fun s k => Φ (b₁ s k),
    bd.map (MvPolynomial.rename (addV J N)), hall', tie₁, fun q hq => EigBase.isIntegrallyClosed_of_snc tie₁ snc₁ q hq,
    ?_, ?_, hact', ?_, ?_, ?_, ?_, snc₁, ?_⟩
  · show ξ' ≫ f' ≫ f = _
    rw [← Category.assoc, show ξ' ≫ f' = _ from hdom, Category.assoc, hξ]
  · have hd : ξ' ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap Ω₀ Ω')) ≫ ξ := hdom
    have e₁ : ξ' ≫ (f' ≫ f) ≫ Y.s = (ξ' ≫ f') ≫ f ≫ Y.s := by simp only [Category.assoc]
    rw [e₁, hd, Category.assoc, hcst]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · intro e
    rw [hn]
    show (M'.pt (j' (a₀ e))).left ≫ m₁.φ ≫ m.φ = _
    rw [← Category.assoc, hj₁, Category.assoc, ha₁, SatModel.spMap_dualMap_id, Category.id_comp]
  · intro s e
    exact (heig _ _).symm.trans Iff.rfl
  · exact hgf''
  · intro s
    have heig' : ∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
        j' e ∈ eigSp ρ' (((algebraMap Ω₀ Ω').comp cst).comp (labelEmb c s)) := by
      intro s e he
      rw [RingHom.comp_assoc]
      exact (heig _ e).2 he
    have hfl' : ∀ s, ((L s).pull ξ' f' j').IsFlagVBOn Set.univ (fun k => Φ (b₁ s k)) := by
      intro s
      rw [← hjΦ]
      exact GlobalTheory.T.flag_bundle_under_equiv X X' Ω₀ Ω' ξ ξ' f' Li _ Li' (L s) _ Φ Set.univ _ (b₁ s) (hfl s)
    have hi₀ : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q) :=
      fun q hq => EigBase.isIntegrallyClosed_of_snc htie hsnc q hq
    have hi₁ : ∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q) :=
      fun q hq => EigBase.isIntegrallyClosed_of_snc tie₁ snc₁ q hq
    exact GlobalTheory.T.lie_model_constants_extension E H l c X X' t t' f' Ω₀ Ω' ξ ξ' cst Li Li' M M' ρ ρ' L j' (labelRk D) (fun s k => Φ (b₁ s k)) hg hg'
      hdom hact hact' hi₀ hi₁ hLeq hj₅ heig' hfl' s
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_added X X' Ω₀ Ω' ξ ξ' f' K J y N x' z w hall htie hg'' hall' hdom hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (addV J N ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [EigBase.mem_mcPts_rename (addV J N) bd w hne hne']
    exact hbd (z ≫ f') _ hw₁
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_with_constants_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω₀ Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), IsCptGen ξ₀ → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ξ ≫ f = ξ₀ → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) → (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) → Cmp.IsSncModel y D.dim bd → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G)) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra Ω₀ Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module Ω₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) ∧ IsGenericFlag (Ω' := Ω) j V₀ b 1 ∧ (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) ∧ Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.exists_flagStep
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

section Segre

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

abbrev segJ (J : K → Type) : K ⊕ Unit → Type := Sum.elim J fun _ : Unit => ∀ k, J k

instance segJ.instFintype : ∀ k, Fintype (segJ J k)
  | .inl k => inferInstanceAs (Fintype (J k))
  | .inr _ => (Fintype.ofFinite (∀ k, J k) : Fintype (∀ k, J k))

def segBlock (y : (Σ k, J k) → Ω) : (Σ _ : Unit, ∀ k, J k) → Ω := fun p => ∏ k, y ⟨k, p.2 k⟩

def segY (y : (Σ k, J k) → Ω) : (Σ k, segJ J k) → Ω
  | ⟨.inl k, i⟩ => y ⟨k, i⟩
  | ⟨.inr _, c⟩ => ∏ k, y ⟨k, c k⟩

theorem segY_prod (y : (Σ k, J k) → Ω) (c : (k : K ⊕ Unit) → segJ J k) :
    ∏ k, segY y ⟨k, c k⟩ = (∏ k, y ⟨k, c (Sum.inl k)⟩) * ∏ k, y ⟨k, c (Sum.inr ()) k⟩ := by
  rw [Fintype.prod_sum_type]
  simp [segY]

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {y : (Σ k, J k) → Ω}

theorem segTie (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) :
    CoordTie ℤ ξ fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩ := by
  have key := @GlobalTheory.T.coords_join_blocks X Ω _ ξ K _ J _ y Unit _ (fun _ => ∀ k, J k) (fun _ => Fintype.ofFinite _) (segBlock y) h
    (fun _ p => by
      obtain ⟨c, hc⟩ := h.cover p
      exact ⟨c, hc⟩)
  have e : (fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩) =
      fun c' : (k : K ⊕ Unit) → Sum.elim J (fun _ : Unit => ∀ k, J k) k =>
        (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, segBlock y ⟨k, c' (Sum.inr k)⟩ := by
    funext c'
    rw [segY_prod]
    simp [segBlock]
  rw [e]
  exact key

theorem segChart {c : (k : K ⊕ Unit) → segJ J k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩) c p) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (fun k => c (Sum.inl k)) p := by
  obtain ⟨h0, h1⟩ := h
  simp only [segY_prod] at h0 h1
  have hB := right_ne_zero_of_mul h0
  refine ⟨left_ne_zero_of_mul h0, fun c' => ?_⟩
  have h2 := h1 (fun k => match k with
    | .inl k => c' k
    | .inr u => c (Sum.inr u))
  simp only at h2
  rwa [mul_div_mul_right _ _ hB] at h2

theorem segDeg {F : Type} [AddCommGroup F] [Module Ω F] {L : Lat ξ F} {a : K → ℤ} {e₀ : F}
    (h : L.IsDegOn Set.univ y a e₀) : L.IsDegOn Set.univ (segY y) (Sum.elim a 0) e₀ := by
  refine ⟨h.1, fun p _ c' hc => ?_⟩
  have h1 := h.2 p trivial (fun k => c' (Sum.inl k)) (segChart hc)
  have e : (∏ k, segY y ⟨k, c' k⟩ ^ (Sum.elim a 0 : K ⊕ Unit → ℤ) k) =
      ∏ k, y ⟨k, c' (Sum.inl k)⟩ ^ a k := by
    rw [Fintype.prod_sum_type]
    simp [segY]
  rw [e]
  exact h1

end Segre

section Ideal

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)]

theorem mem_mcPts_map (v : (Σ k, J k) → Σ k, J' k) (bd : Ideal (MRing J)) (w : (Σ k, J' k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hw' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0) :
    w ∈ mcPts (bd.map (MvPolynomial.rename v)) ↔ (fun p => w (v p)) ∈ mcPts bd := by
  have e : ∀ f : MRing J, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ)
      (MvPolynomial.rename v f)) =
      MvPolynomial.eval (fun p => w (v p)) (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro f
    rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
    rfl
  constructor
  · intro h
    exact ⟨hw', fun f hf => by
      rw [← e]
      exact h.2 _ (Ideal.mem_map_of_mem _ hf)⟩
  · intro h
    refine ⟨hw, fun f hf => ?_⟩
    let φ : MRing J' →+* ℂ := (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))
    have hle : bd.map (MvPolynomial.rename v) ≤ RingHom.ker φ :=
      Ideal.map_le_iff_le_comap.2 fun g hg => by
        show φ (MvPolynomial.rename v g) = 0
        show MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.rename v g)) = 0
        rw [e]
        exact h.2 g hg
    exact hle hf

end Ideal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HodgeCpt.retie {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type} {y₂ : (Σ k, J₂ k) → Ω}
    (h : CoordTie ℤ 𝔐.ξ fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) : HodgeCpt Y S y₂ where
  X := 𝔐.X
  ξ := 𝔐.ξ
  all := 𝔐.all
  tie := h
  normal := 𝔐.normal
  f := 𝔐.f
  Ω₀ := 𝔐.Ω₀
  ξ₀ := 𝔐.ξ₀
  gen₀ := 𝔐.gen₀
  cst := 𝔐.cst
  cst_over := 𝔐.cst_over
  fn := 𝔐.fn
  fn_over := 𝔐.fn_over
  t := 𝔐.t
  m := 𝔐.m
  Li := 𝔐.Li
  M := 𝔐.M
  ρ := 𝔐.ρ
  act := 𝔐.act
  S_prime := 𝔐.S_prime
  R := 𝔐.R
  R_ge := 𝔐.R_ge
  tors := 𝔐.tors
  vb := 𝔐.vb

def HodgeCpt.Flag.retie {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type}
    {y₂ : (Σ k, J₂ k) → Ω} (h : CoordTie ℤ 𝔐.ξ fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) :
    (𝔐.retie h).Flag where
  b := Fl.b
  sub := Fl.sub
  Li₀ := Fl.Li₀
  acg := Fl.acg
  mod := Fl.mod
  M₀ := Fl.M₀
  j := Fl.j
  j_pt := Fl.j_pt
  V₀ := Fl.V₀
  V₀_mem := Fl.V₀_mem
  deg := Fl.deg
  generic := Fl.generic

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_refGeo : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ G : RefGeo Y, genPt G.𝔐.ξ₀ = genPt ξ₀ := by
  intro hRes E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hgen
  haveI : CharZero Ω₀ := GlobalTheory.T.component_generic_char_zero E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨K₀, _, J₀, _, y₀, X₀, ξ', f₀, cst₀, t₀, m₀, Li', _, _, M', ρ', L', bd₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
    GlobalTheory.T.exists_coords_for_component hRes E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨Ω, _, _, _, K, _, J, _, y, X, ξ, f, cst, t, m, Li, _, _, M, ρ, Li₀, _, _, M₀, j, V₀, b, bd,
    hall, htie, hnorm, hdom, hcst, hact, hjpt, hV, hflag, hvb, hsnc, hbd⟩ :=
    GlobalTheory.T.coords_with_constants_map E H D l Xo c Y Ω₀ ξ₀ K₀ J₀ y₀ X₀ ξ' f₀ cst₀ t₀ m₀ Li' M' ρ' L' bd₀ hgen h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  obtain ⟨K', _, J', _, y', bk, bx, 𝔐, g, Fl, xdeg, e, hbk, hy, hξ, hf, hg0, hdeg, hlines, -, hreg, hinj⟩ :=
    GlobalTheory.T.generic_coords_descend_subfield E H D l Xo c Y Ω K J y X ξ f Ω₀ ξ₀ cst t m Li M ρ Li₀ M₀ j V₀ b 1 hall htie hnorm hgen hdom hcst
      hact hjpt hV hflag hvb
  have tie₂ := segTie (y := y') 𝔐.tie
  have hy₂ : ∀ k (a : J k), segY y' ⟨Sum.inl (bk k), bx k a⟩ = y ⟨k, a⟩ := hy
  let v : (Σ k, J k) → Σ k, segJ J' k := fun p => ⟨Sum.inl (bk p.1), bx p.1 p.2⟩
  refine ⟨{ Ω := Ω, K := K' ⊕ Unit, J := segJ J', y := segY y', 𝔐 := 𝔐.retie tie₂, Fl := Fl.retie tie₂,
            deg_one := hdeg, xdeg := fun r => Sum.elim (xdeg r) 0, e := e, lines := ?_,
            bd := bd.map (MvPolynomial.rename v), snc := ?_, bd_iff := ?_, k₀ := Sum.inr (), embeds := ?_ }, hg0⟩
  · exact fun r => segDeg (hlines r)
  · exact GlobalTheory.T.snc_model_reindexed_coords X 𝔐.X Ω ξ 𝔐.ξ g K J y (K' ⊕ Unit) (segJ J') (segY y') (fun k => Sum.inl (bk k)) bx _ bd
      hall 𝔐.all htie tie₂ hξ hy₂ hreg hinj hsnc
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_reindexed X 𝔐.X Ω ξ 𝔐.ξ g K J y (K' ⊕ Unit) (segJ J') (segY y') (fun k => Sum.inl (bk k)) bx z w
      hall 𝔐.all 𝔐.tie.gen hξ hy₂ hreg hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [mem_mcPts_map v bd w hne hne']
    refine (show (fun p => w (v p)) ∈ mcPts bd ↔ _ from hbd (z ≫ g) _ hw₁).trans ?_
    have hab := abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre z)
    have hc : f (centre (z ≫ g)) = 𝔐.f (centre z) := by
      rw [hf]
      rfl
    rw [hc]
    exact not_congr hab
  · exact GlobalTheory.T.embeds_generic_of_char_zero 𝔐.X Ω 𝔐.ξ _ _ 𝔐.tie

end GlobalTheory.CompanionTheory.Ar
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reference_geometry_same_generic : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ G : RefGeo Y, genPt G.𝔐.ξ₀ = genPt ξ₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.exists_refGeo
end
