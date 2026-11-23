module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibre
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.Mum.exists_sec_nonzero_on_fibre | exact GlobalTheory.Mum.exists_sec_nonzero_on_fibre | (intros; apply GlobalTheory.Mum.exists_sec_nonzero_on_fibre <;> assumption)
