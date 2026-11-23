module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord

namespace GlobalTheory.SS.Ord

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma model_isPullback_genericFibre_spMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm


variable {R K : Type} [CommRing R] [Field K] [Algebra R K] in
theorem _root_.GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M N : _root_.GlobalTheory.SS.Model R A)
      (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left),
      _root_.GlobalTheory.SS.Extends M N (𝟙 A) U g → Etale g → IsOpenImmersion g := by
  intro R K _ _ _ _ _ _ A M N U g hE _
  haveI := M.smooth
  haveI := M.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI : IsSeparated (g ≫ N.Y.hom) := by rw [hE.1]; infer_instance
  haveI : IsSeparated g := IsSeparated.of_comp g N.Y.hom
  haveI := FormallyUnramified.isOpenImmersion_diagonal g
  let ψ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)
  let q := pullback.fst g g ≫ U.ι ≫ M.Y.hom
  let φ := pullback.fst q ψ
  haveI : IsSchemeTheoreticallyDominant φ :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback q ψ).flip
  have hU := ((isPullback_morphismRestrict M.j U).paste_vert
    (model_isPullback_genericFibre_spMap M))
  have hN := model_isPullback_genericFibre_spMap N
  have hs : (φ ≫ pullback.fst g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [Category.assoc]
    exact pullback.condition
  have hs' : (φ ≫ pullback.snd g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [← hs, ← hE.1]
    simp only [Category.assoc, pullback.condition_assoc]
  have key : ∀ (c : pullback q ψ ⟶ U) (hc : c ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ),
      (hU.lift c _ hc ≫ (M.j ⁻¹ᵁ U).ι) ≫ N.j = c ≫ g := by
    intro c hc
    have h2 := hE.2
    conv_rhs => rw [← hU.lift_fst c _ hc]
    rw [Category.assoc (hU.lift c _ hc) (M.j ∣_ U) g, h2]
    simp
  have hl : hU.lift _ _ hs ≫ (M.j ⁻¹ᵁ U).ι =
      hU.lift _ _ hs' ≫ (M.j ⁻¹ᵁ U).ι := by
    apply hN.hom_ext
    · rw [key _ hs, key _ hs']
      simp only [Category.assoc, pullback.condition]
    · have e1 := hU.lift_snd _ _ hs
      have e2 := hU.lift_snd _ _ hs'
      simp only [Category.assoc] at e1 e2 ⊢
      rw [e1, e2]
  have hab : φ ≫ pullback.fst g g = φ ≫ pullback.snd g g := by
    rw [← hU.lift_fst _ _ hs, ← hU.lift_fst _ _ hs', (cancel_mono _).1 hl]
  have hφ : φ = (φ ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [hab]
  have hrange : Set.range φ ⊆ Set.range (pullback.diagonal g) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(φ ≫ pullback.fst g g) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) :=
    (pullback.diagonal g).isClosedEmbedding.isClosed_range
  have huniv : Set.range (pullback.diagonal g) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (IsDominant.denseRange (f := φ)).closure_eq]
    exact closure_minimal hrange hclosed
  haveI : IsIso (pullback.diagonal g) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using huniv))
  haveI : Mono g := (pullback.isIso_diagonal_iff g).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono g

end GlobalTheory.SS.Ord
