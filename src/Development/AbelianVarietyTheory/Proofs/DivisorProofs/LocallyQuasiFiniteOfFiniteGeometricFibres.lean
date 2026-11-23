module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GeomFibre

theorem finite_of_finite_sections {K : Type} [Field K] [IsAlgClosed K] {P : Scheme.{0}}
    (g : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (h : Finite {p : Spec (CommRingCat.of K) ⟶ P // p ≫ g = 𝟙 _}) : Finite P := by
  have := LocallyOfFiniteType.jacobsonSpace g
  have h1 : (closedPoints P).Finite :=
    Set.finite_coe_iff.mp ((pointEquivClosedPoint g).finite_iff.mp h)
  have hc : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact h1.isClosed_biUnion fun x hx ↦ hx
  have h2 := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := P))
  rw [Set.univ_inter, hc.closure_eq] at h2
  exact Set.finite_univ_iff.mp (h2 ▸ h1)

theorem locallyQuasiFinite_of_finite_geometric_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
        Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}) → LocallyQuasiFinite f := by
  intro X Y f _ H
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  rcases (f ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.finite_empty
  obtain rfl : f x₀ = y := hx₀
  let K := AlgebraicClosure (X.residueField x₀)
  let x : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have hx : ∀ z, x z = x₀ := fun z ↦ by
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hfin : Finite ↥(pullback f (x ≫ f)) := by
    refine finite_of_finite_sections (pullback.snd f (x ≫ f)) ?_
    have := (H K x).to_subtype
    refine Finite.of_injective (β := {y : Sp K ⟶ X | y ≫ f = x ≫ f})
      (fun p ↦ ⟨p.1 ≫ pullback.fst f (x ≫ f), ?_⟩) fun a b hab ↦ ?_
    · change (p.1 ≫ _) ≫ f = x ≫ f
      rw [Category.assoc, pullback.condition, reassoc_of% p.2]
    · exact Subtype.ext (pullback.hom_ext (congrArg Subtype.val hab) (a.2.trans b.2.symm))
  refine (Set.finite_range (pullback.fst f (x ≫ f))).subset fun z hz ↦ ?_
  rw [Scheme.Pullback.range_fst]
  exact ⟨IsLocalRing.closedPoint K,
    ((Scheme.Hom.comp_apply x f _).trans (congrArg f (hx _))).trans hz.symm⟩

end GlobalTheory.GeomFibre
