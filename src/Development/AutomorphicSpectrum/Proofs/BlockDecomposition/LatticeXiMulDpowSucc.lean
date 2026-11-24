module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDp

theorem mul_divPow_succ {B : Type} [CommRing B] [Algebra ℚ B] (c η : B) (i : ℕ) :
    (c * η) * (((i.factorial : ℚ)⁻¹) • η ^ i) =
      (c * ((i : B) + 1)) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) := by
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have key : ((i : B) + 1) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) =
      ((i.factorial : ℚ)⁻¹) • η ^ (i + 1) := by
    have h1 : ((i : B) + 1) = algebraMap ℚ B ((i : ℚ) + 1) := by simp
    rw [h1, ← Algebra.smul_def, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [mul_assoc c ((i : B) + 1), key, mul_assoc c η]
  simp only [Algebra.mul_smul_comm, pow_succ]
  congr 2
  ring

theorem natPow_mul_inv_smul {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) :
    (l : B) ^ M * ((((l : ℚ) ^ M)⁻¹) • x) = x := by
  have h0 : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl)
  have h1 : ((l : B) ^ M) = algebraMap ℚ B ((l : ℚ) ^ M) := by simp
  rw [h1, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem mul_divPow_eq_elem {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) (i : ℕ) :
    x * (((i.factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ i) =
      ((l : B) ^ M * ((i : B) + 1)) *
        ((((i + 1).factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ (i + 1)) := by
  have h := mul_divPow_succ ((l : B) ^ M) ((((l : ℚ) ^ M)⁻¹) • x) i
  rwa [natPow_mul_inv_smul x l M hl] at h

theorem mul_divPow_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ), l ≠ 0 → ∀ i : ℕ,
    f ξ * Lat.dpE f ξ l M i = ((l : B) ^ M * ((i : B) + 1)) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M hl i
  simp only [Lat.dpE, Lat.η]
  exact mul_divPow_eq_elem (f ξ) l M hl i

end GlobalTheory.CompanionTheory.LatDp
