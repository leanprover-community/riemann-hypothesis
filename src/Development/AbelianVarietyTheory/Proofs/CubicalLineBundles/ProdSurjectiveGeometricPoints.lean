module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomSurj


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.GeomSurj.exists_lift_of_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ A) :
    ∃ p : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ P, x = p ≫ ψ := by
  have hΩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω = Spec (CommRingCat.of Ω) := rfl
  haveI : JacobsonSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : JacobsonSpace (pullback ψ x :) := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ x)
  obtain ⟨q₀, -⟩ := (pullback.snd ψ x).surjective (Classical.arbitrary _)
  obtain ⟨q, hq⟩ : (closedPoints (pullback ψ x :)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hc := closure_closedPoints (X := (pullback ψ x :))
    rw [h, closure_empty] at hc
    exact (hc ▸ Set.mem_univ q₀ : q₀ ∈ (∅ : Set _))
  haveI : LocallyOfFiniteType ((pullback ψ x).fromSpecResidueField q) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hq
  let g : Spec ((pullback ψ x).residueField q) ⟶ Spec (CommRingCat.of Ω) :=
    (pullback ψ x).fromSpecResidueField q ≫ pullback.snd ψ x
  have hg : LocallyOfFiniteType (Spec.map (Spec.preimage g)) := by
    rw [Spec.map_preimage]; dsimp only [g]; infer_instance
  have hft := HasRingHomProperty.Spec_iff.mp hg
  set f := Spec.preimage g with hf
  letI : Algebra Ω ((pullback ψ x).residueField q) := f.hom.toAlgebra
  haveI : Algebra.FiniteType Ω ((pullback ψ x).residueField q) := hft
  haveI : Module.Finite Ω ((pullback ψ x).residueField q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let φ : (pullback ψ x).residueField q →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have key : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g = 𝟙 _ := by
    rw [← Spec.map_preimage g, ← hf, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext a
    exact φ.commutes a
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullback ψ x).fromSpecResidueField q ≫
    pullback.fst ψ x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc (Scheme.fromSpecResidueField _ _), ← Category.assoc]
  change x = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) ≫ x
  rw [key, Category.id_comp]

end GlobalTheory.GeomSurj
