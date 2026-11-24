module

public import Formalism.PadicSubsetSums.CentralIdempotents.ResidueAvoidanceOfPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.TOP

private theorem tsum_mul_inv_pow_succ_eq_div_sub_one (ℓ : ℕ) (H : ℝ) (hℓ : (2 : ℝ) ≤ ℓ) :
    ∑' j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = H / ((ℓ : ℝ) - 1) := by
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hl0 : (ℓ : ℝ) ≠ 0 := by positivity
  have hl1 : (ℓ : ℝ) - 1 ≠ 0 := by intro h; linarith
  have e : ∀ j : ℕ, H * ((ℓ : ℝ)⁻¹) ^ (j + 1) = (H * (ℓ : ℝ)⁻¹) * ((ℓ : ℝ)⁻¹) ^ j := by
    intro j; ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e2 : (1 : ℝ) - (ℓ : ℝ)⁻¹ = ((ℓ : ℝ) - 1) / ℓ := by field_simp
  rw [e2]
  field_simp

theorem carryFloorLeGeom : SgLe := by
  intro f _ ℓ h H hℓ hH i
  unfold sg
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hr0 : 0 ≤ (ℓ : ℝ)⁻¹ := by positivity
  have hr1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeom : Summable (fun j : ℕ => (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left ((H : ℝ) * (ℓ : ℝ)⁻¹)
    refine this.congr ?_
    intro j; ring
  have hle : ∀ j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) ≤
      (H : ℝ) * ((ℓ : ℝ)⁻¹) ^ (j + 1) := by
    intro j
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hH _) (by positivity)
  have hnn : ∀ j : ℕ, 0 ≤ (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1) :=
    fun j => by positivity
  have hs : Summable (fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)) :=
    hgeom.of_nonneg_of_le hnn hle
  have h1 := hs.tsum_le_tsum hle hgeom
  rw [tsum_mul_inv_pow_succ_eq_div_sub_one ℓ H hℓ'] at h1
  exact (Int.floor_le _).trans h1

end Formalism.IrreducibleCountingLemmas.TOP
