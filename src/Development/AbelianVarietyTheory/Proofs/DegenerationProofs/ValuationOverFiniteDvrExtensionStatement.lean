module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtension
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.valuation_over_finite_dvr_extension : ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧ (∃ i' : FractionRing W →+* FractionRing W', (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧ ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 → ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧ ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K, ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  first | exact @GlobalTheory.FiniteDVRValuation.main | exact GlobalTheory.FiniteDVRValuation.main | (intros; apply GlobalTheory.FiniteDVRValuation.main <;> assumption)
