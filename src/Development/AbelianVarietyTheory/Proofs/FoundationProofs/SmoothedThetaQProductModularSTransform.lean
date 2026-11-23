module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransformStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotientStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.Imports

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory

open GlobalTheory.Sieg

lemma Sieg.cthS_ee_pow (w : ℂ) (n : ℕ) : ee w ^ n = ee ((n : ℂ) * w) := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma Sieg.cthS_negI_pow (c : ℕ) (hc : Nat.Coprime c 6) : (-Complex.I) ^ (c ^ 2) = -Complex.I := by
  have h2 : Nat.Coprime c 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hodd : Odd c := by
    rcases Nat.even_or_odd c with h | h
    · exfalso
      obtain ⟨j, hj⟩ := h
      have : 2 ∣ Nat.gcd c 2 := Nat.dvd_gcd ⟨j, by omega⟩ dvd_rfl
      rw [h2] at this
      omega
    · exact h
  obtain ⟨j, rfl⟩ := hodd
  have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
  rw [this, pow_succ, pow_mul]
  have h4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  rw [h4, one_pow, one_mul]

theorem Sieg.cth_modular_S (c : ℕ) (τ : ℍ) (z : ℂ) (h1 : 1 < c) (hc : Nat.Coprime c 6)
    (hz : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) :
    cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [inv_neg]

  have hB : th ((c : ℂ) * z) τ ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice τ _).1 h
    exact hz m n hmn

  have hB' : th ((c : ℂ) * (z / (τ : ℂ))) (ModularGroup.S • τ) ≠ 0 := by
    intro h
    obtain ⟨m, n, hmn⟩ := (GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice _ _).1 h
    rw [hS] at hmn
    apply hz n (-m)
    have : (c : ℂ) * z = (τ : ℂ) * ((c : ℂ) * (z / (τ : ℂ))) := by field_simp
    rw [this, hmn]
    push_cast
    field_simp
    ring
  rw [GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB', GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient c _ _ h1 hc hB]
  rw [show (c : ℂ) * (z / (τ : ℂ)) = ((c : ℂ) * z) / (τ : ℂ) by ring]
  rw [GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ z, GlobalTheory.T.oddThetaProductSiegel_modularS_transform τ ((c : ℂ) * z)]
  have hee : ee (z ^ 2 / (2 * (τ : ℂ))) ^ (c ^ 2) = ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) := by
    rw [Sieg.cthS_ee_pow]
    congr 1
    push_cast
    ring
  have hE : ee (((c : ℂ) * z) ^ 2 / (2 * (τ : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hI : (-Complex.I) ≠ 0 := by simp
  rw [mul_pow, mul_pow, Sieg.cthS_negI_pow c hc, hee]
  field_simp
  rw [mul_comm, mul_div_assoc, div_self (by unfold ee; exact Complex.exp_ne_zero _), mul_one]

end GlobalTheory
