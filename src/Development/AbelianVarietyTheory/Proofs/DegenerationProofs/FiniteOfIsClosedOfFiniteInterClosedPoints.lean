module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_of_isClosed_of_finite_inter_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem finite_pullback_over_closedPoint {X Z P : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] (s : X ⟶ Z) (t : P ⟶ Z) (σ : X) (hσ : IsClosed ({σ} : Set X))
    {F : Set P} (hF : F.Finite) :
    {w : ↑(pullback s t) | pullback.fst s t w = σ ∧ pullback.snd s t w ∈ F}.Finite := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hσ
  let i := X.fromSpecResidueField σ
  have h1 : LocallyOfFiniteType ((i ≫ s) ≫ specZIsTerminal.from Z) := by
    rw [specZIsTerminal.hom_ext ((i ≫ s) ≫ specZIsTerminal.from Z) (i ≫ π)]
    infer_instance
  have h2 : LocallyOfFiniteType (i ≫ s) := locallyOfFiniteType_of_comp _ (specZIsTerminal.from Z)
  have h3 : LocallyQuasiFinite (i ≫ s) :=
    .of_injective (Function.injective_of_subsingleton _)
  have h4 : QuasiCompact (i ≫ s) := ⟨fun U _ _ ↦ (Set.toFinite _).isCompact⟩
  have H := (IsPullback.of_hasPullback (pullback.fst s t) i).paste_horiz
    (IsPullback.of_hasPullback s t).flip
  have h5 : LocallyQuasiFinite (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h3
  have h6 : QuasiCompact (pullback.fst (pullback.fst s t) i ≫ pullback.snd s t) :=
    MorphismProperty.of_isPullback H.flip h4
  refine (((pullback.fst (pullback.fst s t) i ≫ pullback.snd s t).finite_preimage hF).image
    (pullback.fst (pullback.fst s t) i)).subset ?_
  rintro w ⟨hw, hw'⟩
  have : w ∈ Set.range (pullback.fst (pullback.fst s t) i) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hw
  obtain ⟨v, rfl⟩ := this
  exact ⟨v, by simpa using hw', rfl⟩

theorem locallyQuasiFinite_of_finite_fibres_closedPoints {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

end GlobalTheory
