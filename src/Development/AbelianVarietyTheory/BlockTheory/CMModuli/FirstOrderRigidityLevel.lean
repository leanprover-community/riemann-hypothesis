module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

def Conv (g n k : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ 2 ≤ k ∧ 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < (((n ^ k) ^ 2 : ℕ) : ℝ)

section General
variable {S : Scheme.{0}}

end General

section Forms
variable {R : Type} [CommRing R] {P : PolAV (Sp R)} {I : Type} {e : ℤ}

end Forms

section Norm
variable {K : Type} [Field K] (P : PolAV (Sp K))

def HasTrace (ψ : P.A ⟶ P.A) (t : ℤ) : Prop :=
  ∀ M : ℕ, (M : K) ≠ 0 → ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ M = 1) →
    (∀ z : baseOver (Sp K) ⟶ P.A, z ^ M = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℕ,
      (∀ i, y i ≫ ψ = linComb y fun l => B l i) → ((B.trace : ℕ) : ZMod M) = (t : ZMod M)

end Norm

end GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel
