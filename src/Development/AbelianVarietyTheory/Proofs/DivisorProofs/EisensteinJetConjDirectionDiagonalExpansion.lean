module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirectionStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_conj_expand : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  intro hE F _ _ _ hf s N L hs hN hL τ κ Ch
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have hne : τ.im ≠ 0 := τ.im_pos.ne'
  set v : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) with hv
  set T : ℂ := 2 * Real.pi * Complex.I with hT
  have hT0 : T ≠ 0 := by
    simp [hT, Real.pi_ne_zero, Complex.I_ne_zero]
  have hw : v * (starRingEnd ℂ (τ : ℂ) - τ) = -T := by
    have : starRingEnd ℂ (τ : ℂ) - τ = -(2 * ((τ : ℂ).im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp <;> ring
    rw [this, hv, hT]
    have : ((τ : ℂ).im : ℂ) = (τ.im : ℂ) := rfl
    rw [this]; push_cast
    have h0 : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
    field_simp
  set C : ℂ := T ^ 2 * Ch τ with hC
  have h1 := GlobalTheory.T.hilbert_eisenstein_jet_smul_direction hE F hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) v κ him
  have h2 := GlobalTheory.T.hilbert_eisenstein_jet_add_direction hE F hf s N L hs hN hL τ C (-T) (v - C) κ him
  rw [mul_one, hw] at h1
  have h3 : jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * v ^ (∑ i, κ i) = jet (2 * s) L κ τ (C + (v - C)) (-T) := by
    rw [add_sub_cancel, h1, mul_comm]
  rw [h3, h2, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hle : μ ≤ κ := Finset.mem_Iic.mp hμ
  have hwt : wt (2 * s) κ = wt (2 * s) μ + 2 * ∑ i, (κ i - μ i) := by
    have : ∑ i, κ i = ∑ i, μ i + ∑ i, (κ i - μ i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (Nat.add_sub_of_le (hle i)).symm
    simp only [wt, this]; ring
  have hsub : v / T ^ 2 - Ch τ = (v - C) / T ^ 2 := by
    rw [hC]; field_simp
  rw [hsub, hfun, ← hT, ← hC, hwt, pow_add, pow_mul, div_pow]
  field_simp

end GlobalTheory.HilbFam
