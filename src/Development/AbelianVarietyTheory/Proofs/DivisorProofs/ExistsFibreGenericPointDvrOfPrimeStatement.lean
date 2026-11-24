module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreGenericPointDvrOfPrime
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  first | exact @GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime | exact GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime | (intros; apply GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime <;> assumption)
