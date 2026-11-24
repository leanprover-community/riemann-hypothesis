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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

abbrev JetR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)

abbrev algOver (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R A))

def algOverHom {R : Type} [CommRing R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ψ : A →ₐ[R] B) : algOver R B ⟶ algOver R A :=
  Over.homMk (spMap (ψ : A →+* B)) (by
    dsimp
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)

def jetTruncR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

def jetZeroR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

abbrev zR {R : Type} [CommRing R] {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
