module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

variable (d : ℕ)

theorem X_mem_one (i : Fin (d + 1)) : (X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ 1 :=
  isHomogeneous_X ℂ i

abbrev chart (i : Fin (d + 1)) : (PSpace ℂ d).Opens := Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)

def ratioSec (i j : Fin (d + 1)) : Γ(PSpace ℂ d, chart d i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)
    (Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j))

variable {d} {Z : Scheme.{0}} [IsIntegral Z]


open Classical in
def rat (φ : Z ⟶ PSpace ℂ d) (i j : Fin (d + 1)) : Z.functionField :=
  if h : genericPoint Z ∈ φ ⁻¹ᵁ chart d i then
    Z.presheaf.germ (φ ⁻¹ᵁ chart d i) (genericPoint Z) h (φ.app (chart d i) (ratioSec d i j))
  else 0

variable [Algebra ℂ Z.functionField]

def fld (φ : Z ⟶ PSpace ℂ d) : IntermediateField ℂ Z.functionField := IntermediateField.adjoin ℂ (Set.range (rat φ 0))

def crd (φ : Z ⟶ PSpace ℂ d) : Fin (d + 1) → fld φ := fun j =>
  ⟨rat φ 0 j, IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩⟩

theorem crd_val (φ : Z ⟶ PSpace ℂ d) (j : Fin (d + 1)) : ((crd φ j : fld φ) : Z.functionField) = rat φ 0 j := rfl

end GlobalTheory.PD.XCover
