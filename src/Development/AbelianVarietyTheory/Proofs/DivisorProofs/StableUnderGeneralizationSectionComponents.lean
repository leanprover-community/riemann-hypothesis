module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecializationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionMemComponentGenericOfClosedValuationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem stableUnderGeneralization_sectionComponents :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ →
      StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro X S f e hf hef x x' hxx' hx
  obtain ⟨V, _, _, _, g, hgc, hgb⟩ := GlobalTheory.T.exists_valuationRing_dominating_specialization X x' x hxx'
  set p : Spec (CommRingCat.of V) ⟶ S := g ≫ f with hp
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p) f p := IsPullback.of_hasPullback f p
  let σ : Spec (CommRingCat.of V) ⟶ pullback f p := pullback.lift g (𝟙 _) (by simp [hp])
  let e' : Spec (CommRingCat.of V) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [Category.assoc, hef])
  have hσf : σ ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have hσq : σ ≫ pullback.fst f p = g := pullback.lift_fst _ _ _
  have he'f : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'q : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  haveI : Smooth f := hf
  have hf' : Smooth (pullback.snd f p) := inferInstance
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S (pullback f p) (Spec (CommRingCat.of V)) f (pullback.snd f p) p
    (pullback.fst f p) e e' hf hpb hef he'f he'q
  have hc : σ (IsLocalRing.closedPoint V) ∈ {y : ↥(pullback f p) | y ∈ connectedComponentIn
      (pullback.snd f p ⁻¹' {pullback.snd f p y}) (e' (pullback.snd f p y))} := by
    rw [← key]
    rw [Set.mem_preimage]
    have h1 : (pullback.fst f p) (σ (IsLocalRing.closedPoint V)) = x := by
      rw [← hgc, ← hσq]
      rfl
    rw [h1]
    exact hx
  have hb := GlobalTheory.T.section_mem_component_generic_of_closed_valuation V (pullback f p) (pullback.snd f p) e' σ hf' he'f hσf hc
  rw [← key] at hb
  have : (pullback.fst f p) (σ (⊥ : PrimeSpectrum V)) = x' := by
    rw [← hgb, ← hσq]
    rfl
  rw [← this]
  exact hb

end GlobalTheory
