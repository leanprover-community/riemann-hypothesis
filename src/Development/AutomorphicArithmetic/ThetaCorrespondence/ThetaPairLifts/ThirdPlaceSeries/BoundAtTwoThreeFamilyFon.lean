module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.NLink
variable {D : D7}
structure SetupAlt (L : SizeData₂ D) (nch : NChoice D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (C₂ : ℝ) : Prop where
  facts : _root_.GlobalTheory.NFacts.NormChoiceFacts D nch
  canon : GlobalTheory.HubX.Canon L HW (rowC C₂) X
  par : AdmissibleParameterJ.AdmPar L
  par67 : EmbeddingTypeJumps.ParametersPolynomiallyBounded L
  big : 8 ≤ L.sc.L
  split : 60 ≤ D.host.splitBound
  kill : KillingConditions.KillAt X.ρ
  sha : TwistedPlaces.ShaFinOdd D
def ExtraAlt (D : D7) (C : ℝ) (CT : ℕ) : Prop := KillingConditions.CommutingEndomorphismCondition D ∧ _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT
def FactsFAlt {eps : ℝ} (Fm : FamP eps) (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch ∧ _root_.GlobalTheory.NLink.ExtraAlt (Fm.D x i) C CT
def BoundAtTwoThreeFamilyFonAlt {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → BoundAtTwoThree (Fm.L x i) X.ρ C
end GlobalTheory.NLink
end
end
