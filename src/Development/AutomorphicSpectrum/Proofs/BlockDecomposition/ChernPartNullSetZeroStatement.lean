module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.chern_part_null_set_zero : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : GlobalTheory.Weight q σ B)
    (ε : ℤˣ) (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) → φ.chernPart D ε Z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.chernPart_null_of_chart_null | exact GlobalTheory.CompanionTheory.MixZ.chernPart_null_of_chart_null | (intros; apply GlobalTheory.CompanionTheory.MixZ.chernPart_null_of_chart_null <;> assumption)
