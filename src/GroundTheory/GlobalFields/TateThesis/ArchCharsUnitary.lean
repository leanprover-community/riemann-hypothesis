module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Real.Sign
public import GroundTheory.GlobalFields.TateThesis.ArchChars
public import GroundTheory.GlobalFields.TateThesis.ArchCharsUnits
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace GroundTheory.Global

open Complex

theorem re_eq_zero_of_norm_exp_one_cpow {s : ℂ}
    (h : ‖((Real.exp 1 : ℝ) : ℂ) ^ s‖ = 1) : s.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow] at h
  exact Real.exp_eq_one_iff _ |>.mp h

theorem existsUnique_mul_I_of_re_eq_zero {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by
  obtain ⟨s, hs, hu⟩ := h
  have hs' : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre s hs]
  refine ⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩
  have := congrArg Complex.im (hu _ hτ)
  simpa using this

theorem existsUnique_prod_mul_I_of_re_eq_zero {α : Type*} {P : α × ℂ → Prop}
    (h : ∃! p, P p) (hre : ∀ p, P p → p.2.re = 0) :
    ∃! q : α × ℝ, P (q.1, (q.2 : ℂ) * I) := by
  obtain ⟨p, hp, hu⟩ := h
  have hp' : p = (p.1, (p.2.im : ℂ) * I) := by
    refine Prod.ext rfl ?_
    apply Complex.ext <;> simp [hre p hp]
  refine ⟨(p.1, p.2.im), by show P (p.1, (p.2.im : ℂ) * I); rw [← hp']; exact hp,
    fun q hq => ?_⟩
  have := hu _ hq
  refine Prod.ext ?_ ?_
  · simpa using congrArg Prod.fst this
  · simpa using congrArg (fun r : α × ℂ => r.2.im) this

theorem existsUnique_cpow_of_pos_circle (χ : {x : ℝ // 0 < x} →ₜ* Circle) :
    ∃! τ : ℝ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  apply existsUnique_mul_I_of_re_eq_zero (existsUnique_cpow_of_pos (circleToUnits.comp χ))
  intro s hs
  apply re_eq_zero_of_norm_exp_one_cpow
  have h : (χ ⟨Real.exp 1, Real.exp_pos 1⟩ : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ s :=
    hs ⟨Real.exp 1, Real.exp_pos 1⟩
  rw [← h, Circle.norm_coe]

theorem existsUnique_realUnits_circle (χ : ℝˣ →ₜ* Circle) :
    ∃! p : Fin 2 × ℝ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : Fin 2 × ℂ => ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2)
    (existsUnique_realUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have h := hp (Units.mk0 (Real.exp 1) (Real.exp_pos 1).ne')
  simp only [Units.val_mk0, Real.sign_of_pos (Real.exp_pos 1), abs_of_pos (Real.exp_pos 1),
    Complex.ofReal_one, one_pow, one_mul] at h
  rw [← h, Circle.norm_coe]

theorem existsUnique_complexUnits_circle (χ : ℂˣ →ₜ* Circle) :
    ∃! p : ℤ × ℝ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : ℤ × ℂ => ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2)
    (existsUnique_complexUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  have h := hp (Units.mk0 _ hne)
  rw [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1),
    div_self hne, one_zpow, one_mul] at h
  rw [← h, Circle.norm_coe]

theorem existsUnique_addChar_real_units (χ : AddChar ℝ ℂˣ) (hχ : Continuous χ) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) :=
  existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul

end GroundTheory.Global
