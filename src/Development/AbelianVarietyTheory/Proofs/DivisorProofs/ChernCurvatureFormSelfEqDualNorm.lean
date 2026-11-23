module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram

@[expose] public section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

namespace GlobalTheory.CurvForm

theorem form_mulVec_left {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K (M *ᵥ v) w = form (Mᵀ * K) v w := by
  simp only [form]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_mulVec_right {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K v (M *ᵥ w) = form (K * Mᴴᵀ) v w := by
  simp only [form]
  rw [star_mulVec, ← mulVec_transpose, mulVec_mulVec]

theorem form_curv_self_eq : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ),
    MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) →
    (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) →
    ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v =
      form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  intro n g H z h2 hu hs hh hdd ξ v
  have hP : (mdel H z ξ)ᵀ = mdel H z ξ := by
    rw [← mdel_transpose, mdel_congr (hs.mono fun x hx => hx.eq)]
  have hQ : mdbar H z ξ = (mdel H z ξ)ᴴ := (conjTranspose_mdel hh ξ).symm
  have hHt : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hHi : (H z)⁻¹ᵀ = (H z)⁻¹ := by rw [transpose_nonsing_inv, hHt]
  rw [curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero, sub_zero, hHt, hP, hQ]
  set P := mdel H z ξ with hPdef
  have hPc : Pᴴᵀ = Pᴴ := by
    ext i j
    have := congrFun (congrFun hP i) j
    simp only [transpose_apply, conjTranspose_apply] at this ⊢
    rw [this]
  simp only [form_mulVec_left, form_mulVec_right]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_mul, hHi, hP, transpose_transpose, hPc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

end GlobalTheory.CurvForm
