module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → 3 ≤ m → ∀ s : Fam D.toPre F (m ^ 2), NuGe D Q F v (m ^ 2) s 0 ↔ ∃ (n : ℕ) (a : Fin n → F) (x : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F (m ^ 2)) (c : Fin n → F) (r : Fin n → Fam D.toPre F (m ^ 2)), (∀ i, 0 ≤ v (a i) ∧ x i ^ (m ^ 2) = 1 ∧ ThC A ρ m th (x i) (t i) (c i) ∧ U.ExpandsF F (m ^ 2) w₀ (t i) (r i)) ∧ s = ∑ i, a i • r i := by
  first | exact @GlobalTheory.UT.nuGe_zero_iff_span_translates | exact GlobalTheory.UT.nuGe_zero_iff_span_translates | (intros; apply GlobalTheory.UT.nuGe_zero_iff_span_translates <;> assumption)
