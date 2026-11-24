module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilIntegralParahoricEquivariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

theorem _root_.GlobalTheory.T.finite_projection_function_field : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  first | (exact @GlobalTheory.PD.XCover.finiteDimensional_fld) | (exact GlobalTheory.PD.XCover.finiteDimensional_fld) | (intros; apply GlobalTheory.PD.XCover.finiteDimensional_fld  <;> assumption)
