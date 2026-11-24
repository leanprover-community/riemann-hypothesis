module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenIso

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem genMap_bijective_of_eq {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X)
    (hη : IsCptGen η) (y : X) (hy : genPt η ⤳ y) (hyq : y = genPt η) :
    Function.Bijective (genMap η ⟨y, hy⟩) := by
  subst hyq
  have : genMap η ⟨genPt η, hy⟩ = (Scheme.stalkClosedPointTo η).hom := by
    simp [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [this]
  exact hη.bij

theorem genMap_comp {X : Scheme.{0}} {K : Type} [Field K] (η : Spec (CommRingCat.of K) ⟶ X) (y : X)
    (hy : genPt η ⤳ y) : spMap (genMap η ⟨y, hy⟩) ≫ X.fromSpecStalk y = η := by
  have hy' : η (IsLocalRing.closedPoint (CommRingCat.of K)) ⤳ y := hy
  change Spec.map (X.presheaf.stalkSpecializes hy' ≫ Scheme.stalkClosedPointTo η) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk η

theorem exists_iso_of_genPt_eq : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X),
    IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  intro X Ω Ω' _ _ ξ ξ' h h' hq
  have hs : genPt ξ ⤳ genPt ξ' := hq ▸ specializes_rfl
  let p : Cpt ξ := ⟨genPt ξ', hs⟩
  let p' : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  let e := RingEquiv.ofBijective (genMap ξ p) (genMap_bijective_of_eq ξ h _ hs hq.symm)
  let e' := RingEquiv.ofBijective (genMap ξ' p') (genMap_bijective_of_eq ξ' h' _ specializes_rfl rfl)
  refine ⟨e'.symm.trans e, ?_⟩
  have c1 : spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') = ξ := genMap_comp ξ _ hs
  have c2 : spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ') = ξ' := genMap_comp ξ' _ specializes_rfl
  calc spMap (e'.symm.trans e).toRingHom ≫ ξ'
      = spMap (e'.symm.trans e).toRingHom ≫ (spMap (genMap ξ' p') ≫ X.fromSpecStalk (genPt ξ')) := by
        rw [c2]
    _ = spMap (genMap ξ p) ≫ X.fromSpecStalk (genPt ξ') := by
        rw [← Category.assoc]
        congr 1
        rw [spMap, spMap, spMap, ← Spec.map_comp]
        congr 1
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
        change e (e'.symm (genMap ξ' p' x)) = genMap ξ p x
        rw [show e'.symm (genMap ξ' p' x) = x from e'.symm_apply_apply x]
        rfl
    _ = ξ := c1

end GlobalTheory.CompanionTheory.Ar.GenIso
