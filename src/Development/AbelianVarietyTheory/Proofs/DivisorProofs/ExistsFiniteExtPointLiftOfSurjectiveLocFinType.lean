module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_finite_ext_point_lift_of_surjective_lft :
    ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
        ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y),
          σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  intro X Y π hft hs K _ x
  haveI : Surjective π := ⟨hs⟩
  let P := Limits.pullback π x
  let s : P ⟶ Sp K := Limits.pullback.snd π x
  haveI : LocallyOfFiniteType s := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd π x))
  haveI : Surjective s := inferInstanceAs (Surjective (Limits.pullback.snd π x))
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨p₀, -⟩ := s.surjective (default : Sp K)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set P)) ⟨p₀, trivial⟩
    isClosed_univ.isLocallyClosed
  haveI : IsClosedImmersion (P.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  haveI : IsFinite (P.fromSpecResidueField z ≫ s) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  let φ := Spec.preimage (P.fromSpecResidueField z ≫ s)
  have hφ : Spec.map φ = P.fromSpecResidueField z ≫ s := Spec.map_preimage _
  refine ⟨P.residueField z, inferInstance, φ.hom,
    P.fromSpecResidueField z ≫ Limits.pullback.fst π x, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  · have h2 : spMap φ.hom = P.fromSpecResidueField z ≫ s := hφ
    rw [h2]
    exact (Category.assoc _ _ _).trans ((congrArg (P.fromSpecResidueField z ≫ ·)
      Limits.pullback.condition).trans (Category.assoc _ _ _).symm)

end GlobalTheory
