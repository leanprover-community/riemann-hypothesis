module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  first | exact @GlobalTheory.KollarApp.isolatedNonKlt_smooth | exact GlobalTheory.KollarApp.isolatedNonKlt_smooth | (intros; apply GlobalTheory.KollarApp.isolatedNonKlt_smooth <;> assumption)
