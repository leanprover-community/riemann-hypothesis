module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Limits

theorem specQuotIdemCoprod_bij (R : Type) [CommRing R] (e e' : R) (he : IsIdempotentElem e)
    (hs : e + e' = 1) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))) := by
  have he' : e' = 1 - e := by rw [← hs]; ring
  have hee : e * e' = 0 := by rw [he', mul_sub, _root_.mul_one, he.eq, sub_self]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := hx
    have h1 : a * e * e' = 0 := by rw [_root_.mul_assoc, hee, mul_zero]
    have h2 : a * e * e = 0 := by
      rw [← hb, _root_.mul_assoc, mul_comm e' e, hee, mul_zero]
    calc a * e = a * e * (e + e') := by rw [hs, _root_.mul_one]
      _ = 0 := by rw [mul_add, h1, h2, add_zero]
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨a * e' + b * e, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨b - a, by rw [he']; ring⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨a - b, by rw [he']; ring⟩

theorem specQuotIdemCoprod : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  intro R _ e e' he hs
  let A := R ⧸ Ideal.span {e}
  let B := R ⧸ Ideal.span {e'}
  let φ : R →+* A × B := (Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))
  have hφ : Function.Bijective φ := specQuotIdemCoprod_bij R e e' he hs
  let ψ : R ≃+* A × B := RingEquiv.ofBijective φ hφ
  let g : Spec (CommRingCat.of A) ⨿ Spec (CommRingCat.of B) ⟶ Sp R :=
    coprodSpec A B ≫ Spec.map (CommRingCat.ofHom φ)
  haveI : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
    have : IsIso (CommRingCat.ofHom φ) := by
      change IsIso (RingEquiv.toCommRingCatIso ψ).hom
      infer_instance
    infer_instance
  haveI : IsIso g := by dsimp only [g]; infer_instance
  let i := asIso g
  refine ⟨IsColimit.ofIsoColimit (coprodIsCoprod (Spec (CommRingCat.of A)) (Spec (CommRingCat.of B)))
    (Cocone.ext i ?_)⟩
  rintro ⟨⟨⟩⟩
  · simp only [i, asIso_hom, g]
    show coprod.inl ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inl_assoc, ← Spec.map_comp]
    rfl
  · simp only [i, asIso_hom, g]
    show coprod.inr ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inr_assoc, ← Spec.map_comp]
    rfl

end GlobalTheory
