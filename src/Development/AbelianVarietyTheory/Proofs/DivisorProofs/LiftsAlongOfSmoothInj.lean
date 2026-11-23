module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldChartOfInj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongPrincipalSmallExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongSmallExtensionOfDualNumberLiftingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpectrumDualNumber
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem liftsAlong_of_smooth_inj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ g hA hg U M hU hM hI B _ _ t ht hsq
  have : Smooth U.hom := hU.smooth
  have : LocallyOfFiniteType U.hom := inferInstance
  have hF : FieldChart A M := fieldChart_of_inj _ A hA g hg U M hU hM hI
  have hT : TanLift A M := tanLift_of_fieldChart _ A hA U M hM hI hF
  have hS : SmallLift A M := GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting _ A hA U M hM hI hT
  exact GlobalTheory.T.liftsAlong_principal_small_extension R A U M hM hS B t ht hsq

end GlobalTheory.DualOpen
