module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinJetConjDirectionDiagonalExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  first | exact @GlobalTheory.HilbFam.jet_conj_expand | exact GlobalTheory.HilbFam.jet_conj_expand | (intros; apply GlobalTheory.HilbFam.jet_conj_expand <;> assumption)
