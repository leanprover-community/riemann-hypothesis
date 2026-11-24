module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoefBound

theorem cartierDivisor_mult_nsmul_eq_natCast_mul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem coef_lt_of_large : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  intro Y _ _ _ R Fd m r a hr hR
  classical
  have hfin := Fd.finite_support_mult
  set S : ℕ := ∑ z ∈ hfin.toFinset, ((m : ℤ) * Fd.mult z).toNat with hS
  refine ⟨a + 1 + S, by omega, fun z => ?_⟩
  have hF : (m : ℤ) * Fd.mult z < ((a + 1 + S : ℕ) : ℤ) := by
    by_cases hz : Fd.mult z = 0
    · rw [hz]; push_cast; omega
    · have hmem : z ∈ hfin.toFinset := by simpa using hz
      have h1 : ((m : ℤ) * Fd.mult z).toNat ≤ S :=
        Finset.single_le_sum (f := fun z => ((m : ℤ) * Fd.mult z).toNat) (fun _ _ => Nat.zero_le _) hmem
      have h2 : (m : ℤ) * Fd.mult z ≤ (((m : ℤ) * Fd.mult z).toNat : ℤ) := Int.self_le_toNat _
      have h3 : ((((m : ℤ) * Fd.mult z).toNat : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast h1
      push_cast; omega
  rw [CartierDiv.mult_add, cartierDivisor_mult_nsmul_eq_natCast_mul, cartierDivisor_mult_nsmul_eq_natCast_mul]
  set b : ℕ := a + 1 + S
  have hRz : R.mult z ≤ (m : ℤ) - 1 := by have := hR z; omega
  have hrb : (0 : ℤ) ≤ ((r * b : ℕ) : ℤ) := by positivity
  have key : ((r * b : ℕ) : ℤ) * R.mult z ≤ ((r * b : ℕ) : ℤ) * ((m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hRz hrb
  have hb : ((b : ℕ) : ℤ) ≤ ((r * b : ℕ) : ℤ) := by
    have : b ≤ r * b := Nat.le_mul_of_pos_left b hr
    exact_mod_cast this
  have e : (((m * r * b : ℕ)) : ℤ) = ((r * b : ℕ) : ℤ) * (m : ℤ) := by push_cast; ring
  rw [e]
  nlinarith

end GlobalTheory.CoefBound
