module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

def IsCurve (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] : Prop :=
  SmoothOfRelativeDimension 1 (strHom k (X := C)) ∧ IsProjOver (strHom k (X := C)) ∧ GeometricallyConnected (strHom k (X := C))

def SemiNeg (k : Type) [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (F : C.Modules) : Prop :=
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ i : W ⟶ F, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

def IsGen {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) : Prop := IsDominant x ∧ IsPreimmersion x

theorem isGen_fromSpecStalk (C : Scheme.{0}) [IsIntegral C] :
    IsGen (K := C.functionField) (C.fromSpecStalk (genericPoint C)) :=
  ⟨show IsDominant (C.fromSpecStalk (genericPoint C)) from ⟨by
      refine Dense.mono (s₁ := {genericPoint C}) ?_ (dense_iff_closure_eq.2 (genericPoint_spec C).def)
      rintro _ rfl
      exact ⟨_, Scheme.fromSpecStalk_closedPoint⟩⟩,
    inferInstanceAs (IsPreimmersion (C.fromSpecStalk (genericPoint C)))⟩

end GlobalTheory.NeronCurve
