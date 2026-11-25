module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
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

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

variable {R : Type} [CommRing R]

def Lifts {X : Scheme.{0}} (s : X ⟶ Sp R) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X) : Prop :=
  z ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) ∧
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = P

def unitPt (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] : Sp B ⟶ A.left :=
  spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left)

def IsSum {B M B' M' : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [CommRing B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (α : B → B') (f : M → M') : Prop :=
  (∀ b, β (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (α b)) ∧ ∀ m, β (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (f m)

structure TanRep (A : Over (Sp R)) [GrpObj A] (W : Type) [AddCommGroup W] [Module R W] where

  Φ : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (_ : Sp (TrivSqZeroExt B M) ⟶ A.left), W →ₗ[R] M

  bij : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (l : W →ₗ[R] M),
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ Φ z = l

  nat : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M']
    [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] (α : B →ₐ[R] B') (f : M →ₗ[R] M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f →
    ∀ z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z → Φ (spMap β ≫ z) = f ∘ₗ Φ z

end GlobalTheory.AbTan

namespace GlobalTheory.AbTan.MultGroup

open LaurentPolynomial

variable (R : Type) [CommRing R]

local instance hopfLaurent : HopfAlgebra (CommRingCat.of R) (CommRingCat.of R[T;T⁻¹]) :=
  inferInstanceAs (HopfAlgebra R R[T;T⁻¹])

end GlobalTheory.AbTan.MultGroup
