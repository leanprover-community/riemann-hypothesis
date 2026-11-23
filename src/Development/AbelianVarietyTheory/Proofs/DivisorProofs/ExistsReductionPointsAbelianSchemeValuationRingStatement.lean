module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRing
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  first | exact @GlobalTheory.ValReduction.reduction_points | exact GlobalTheory.ValReduction.reduction_points | (intros; apply GlobalTheory.ValReduction.reduction_points <;> assumption)
