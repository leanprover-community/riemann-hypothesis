module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory
open Matrix

theorem exists_e8Form_value_not_dvd_prime (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (p : ℕ) (hp : p.Prime) :
    ∃ ε : Fin 8 → ℤ, ¬ (p : ℤ) ∣ ∑ u, ∑ v, W u v * ε u * ε v := by
  by_contra h
  push_neg at h
  have hQ : ∀ ε : Fin 8 → ℤ, ∑ u, ∑ v, W u v * ε u * ε v = ε ⬝ᵥ (W *ᵥ ε) := by
    intro ε
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hA : ∀ i j, (p : ℤ) ∣ (W + W.transpose) i j := by
    intro i j
    have h1 := h (Pi.single i 1 + Pi.single j 1)
    have h2 := h (Pi.single i 1)
    have h3 := h (Pi.single j 1)
    rw [hQ] at h1 h2 h3
    have e : (Pi.single i 1 + Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single j 1) = (W + W.transpose) i j := by
      simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
        single_dotProduct]
      ring
    rw [← e]
    exact dvd_sub (dvd_sub h1 h2) h3
  set A := W + W.transpose
  have hB : A = (p : ℤ) • Matrix.of (fun i j => A i j / p) := by
    ext i j
    simp [Int.mul_ediv_cancel' (hA i j)]
  have hdet : A.det = 1 := hW.2
  rw [hB, Matrix.det_smul] at hdet
  have : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by simp)) _
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

theorem exists_e8Form_value_coprime_oddPrimePow' : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 →
    ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  intro W hW p k hp hp2
  obtain ⟨ε, hε⟩ := exists_e8Form_value_not_dvd_prime W hW p hp
  refine ⟨ε, ?_⟩
  rw [← pow_mul]
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.mul_right
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact hp.one_lt.ne' h
    · exact hp2 h
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hε (Int.natCast_dvd.2 hd)

end GlobalTheory
