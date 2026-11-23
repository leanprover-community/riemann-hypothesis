module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagHomogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem jet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ (v * c) (v * t) κ hk ha hτ
  have h2 := (GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ).mul_left (v ^ (∑ i, κ i))
  refine h1.unique (HasSum.congr_fun h2 fun ξ ↦ ?_)
  have hp : (∏ i : Emb F, lag k (κ i) (v * c) ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t))) =
      v ^ (∑ i, κ i) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show (2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t) = v * ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) by ring]
    exact (lag_homogeneous k (κ i) c _ v).1
  rw [hp]; ring

end GlobalTheory.HilbFam
