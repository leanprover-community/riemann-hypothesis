module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem nsmul_zmod_eq_zero_iff_dvd (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]

theorem natCast_mul_tors_mem_lattice_iff :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by
  intro N _ τ M x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val := by
    rw [← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]
    rfl
  have hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z := by
    intro z
    rw [PeriodPair.mem_lattice]; simp [tauPair]
  rw [hx, hm]
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0 := by
      unfold tors at h
      field_simp at h
      push_cast
      linear_combination h
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him
    rw [him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h1
    constructor
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨m, by push_cast at him ⊢; linear_combination -him⟩
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩
  · rintro ⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩
    refine ⟨m, n, ?_⟩
    have a : (M : ℂ) * ((x 0).val : ℂ) = N * m := by exact_mod_cast hm0
    have b : (M : ℂ) * ((x 1).val : ℂ) = N * n := by exact_mod_cast hn0
    unfold tors
    field_simp
    push_cast
    linear_combination -(τ : ℂ) * a - b

end GlobalTheory.WpFam
