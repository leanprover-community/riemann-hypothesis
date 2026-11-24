module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoefficientValuationBound
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

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbertEisenstein_coefficient_valuation_bound : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (M b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → ![0, ((M * l ^ b : ℕ) : F)] ∈ L → (∀ v ∈ L, ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ)) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → QAll (Sz l lam ρ) N Ch → QAll (Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ)) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.sz_hfun_coef | exact GlobalTheory.HilbFam.sz_hfun_coef | (intros; apply GlobalTheory.HilbFam.sz_hfun_coef <;> assumption)
