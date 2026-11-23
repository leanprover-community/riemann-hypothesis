module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamRelationNaturalSmoothLiftMorphiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickeningsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftDegreeOneComparisonRelationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem exists_linearEquiv_of_rel {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : M → N → Prop) (h1 : ∀ c, ∃ h, p c h) (h2 : ∀ h, ∃ c, p c h)
    (h0 : ∀ c h, p c h → (c = 0 ↔ h = 0)) (hadd : ∀ a b h h', p a h → p b h' → p (a + b) (h + h'))
    (hsmul : ∀ (r : R) a h, p a h → p (r • a) (r • h)) : ∃ e : M ≃ₗ[R] N, ∀ c h, e c = h ↔ p c h := by
  choose f hf using h1
  have uniq : ∀ c h h', p c h → p c h' → h' = h := by
    intro c h h' ph ph'
    have q := hadd _ _ _ _ ph' (hsmul (-1) _ _ ph)
    rw [neg_one_smul, neg_one_smul, add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).1 rfl)
  let g : M →ₗ[R] N :=
    { toFun := f
      map_add' := fun a b ↦ uniq _ _ _ (hadd _ _ _ _ (hf a) (hf b)) (hf (a + b))
      map_smul' := fun r a ↦ uniq _ _ _ (hsmul r _ _ (hf a)) (hf (r • a)) }
  have inj : Function.Injective g := by
    intro a b hab
    have q := hadd _ _ _ _ (hf a) (hsmul (-1) _ _ (hf b))
    rw [neg_one_smul, neg_one_smul] at q
    have hab' : f a = f b := hab
    rw [hab', add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).2 rfl)
  have surj : Function.Surjective g := by
    intro h
    obtain ⟨c, hc⟩ := h2 h
    exact ⟨c, uniq _ _ _ hc (hf c)⟩
  refine ⟨LinearEquiv.ofBijective g ⟨inj, surj⟩, fun c h ↦ ⟨?_, fun ph ↦ uniq _ _ _ ph (hf c)⟩⟩
  rintro rfl
  exact hf c

end GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem crystallineSmoothLift_of_relations : GlobalTheory.Published.CrystallineSmoothLift := by
  have Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, hr2⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  have E2 : ∀ D : Data, ∃ e : CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s, ∀ c h, e c = h ↔ (Λ D).Rel2 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr2 D (Λ D)).1 (hr2 D (Λ D)).2.1 (hr2 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.2
  choose e₁ he₁ using E1
  choose e₂ he₂ using E2
  have r1 : ∀ D c, (Λ D).Rel1 c (e₁ D c) := fun D c ↦ (he₁ D c _).1 rfl
  have r2 : ∀ D c, (Λ D).Rel2 c (e₂ D c) := fun D c ↦ (he₂ D c _).1 rfl
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · intro D a b
    exact (he₂ D _ _).2 (GlobalTheory.T.comparison_relations_respect_cup D (Λ D) a b _ _ (r1 D a) (r1 D b))
  · intro D m c
    exact (he₁ D _ _).2 (GlobalTheory.T.smoothLift_degreeOne_comparisonRelation D (Λ D) m c)
  · intro D D' σ φ φ₀ h m hc
    exact ⟨fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r1 D c) (r1 D' _),
      fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.2 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r2 D c) (r2 D' _)⟩

end GlobalTheory.SmoothLift
