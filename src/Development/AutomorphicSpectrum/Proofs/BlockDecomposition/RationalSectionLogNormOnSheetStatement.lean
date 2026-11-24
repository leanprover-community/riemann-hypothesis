module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheet
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

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.rational_section_log_norm_on_sheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero <;> assumption)
