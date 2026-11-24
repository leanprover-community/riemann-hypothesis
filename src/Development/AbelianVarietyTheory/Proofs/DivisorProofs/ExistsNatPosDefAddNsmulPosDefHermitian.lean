module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posn_quad_hom {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (r : ℝ) :
    (((r : ℂ) • z) ⬝ᵥ H.mulVec (star ((r : ℂ) • z))).re = r ^ 2 * (z ⬝ᵥ H.mulVec (star z)).re := by
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, ← _root_.mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

theorem posn_quad_add {g : ℕ} (H₀ Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (z : Fin g → ℂ) :
    (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re
      = (z ⬝ᵥ Hm.mulVec (star z)).re + n * (z ⬝ᵥ H₀.mulVec (star z)).re := by
  have h1 : (n • H₀).mulVec (star z) = n • H₀.mulVec (star z) := by
    ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, _root_.mul_assoc]
  rw [Matrix.add_mulVec, dotProduct_add, h1, dotProduct_smul, Complex.add_re, nsmul_eq_mul,
    ← Complex.ofReal_natCast, Complex.re_ofReal_mul]

theorem posn_cont {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (z ⬝ᵥ H.mulVec (star z)).re := by
  fun_prop

theorem posn_main : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  intro g H₀ Hm hpos

  have hnorm : ∀ z : Fin g → ℂ, z ≠ 0 →
      ((((‖z‖⁻¹ : ℝ) : ℂ) • z) ∈ Metric.sphere (0 : Fin g → ℂ) 1) := by
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

  have hred : ∀ (H : Matrix (Fin g) (Fin g) ℂ),
      (∀ w ∈ Metric.sphere (0 : Fin g → ℂ) 1, 0 < (w ⬝ᵥ H.mulVec (star w)).re) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re := by
    intro H hS z hz
    have h := hS _ (hnorm z hz)
    rw [posn_quad_hom] at h
    exact pos_of_mul_pos_right h (sq_nonneg _)
  by_cases hne : (Metric.sphere (0 : Fin g → ℂ) 1).Nonempty
  · have hK : IsCompact (Metric.sphere (0 : Fin g → ℂ) 1) := isCompact_sphere 0 1
    obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne (posn_cont H₀).continuousOn
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (posn_cont Hm).continuousOn
    have hw₀ne : w₀ ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw₀; exact zero_ne_one hw₀
    set m := (w₀ ⬝ᵥ H₀.mulVec (star w₀)).re with hm
    have hm0 : 0 < m := hpos w₀ hw₀ne
    obtain ⟨n, hn⟩ := exists_nat_gt (C / m)
    refine ⟨n, hred _ ?_⟩
    intro w hw
    rw [posn_quad_add]
    have h1 : m ≤ (w ⬝ᵥ H₀.mulVec (star w)).re := hmin hw
    have h2 : |(w ⬝ᵥ Hm.mulVec (star w)).re| ≤ C := by
      simpa [Real.norm_eq_abs] using hC w hw
    have h3 : C < n * m := by rwa [div_lt_iff₀ hm0] at hn
    have h4 : (n : ℝ) * m ≤ n * (w ⬝ᵥ H₀.mulVec (star w)).re :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
    have h5 := neg_abs_le (w ⬝ᵥ Hm.mulVec (star w)).re
    linarith
  · refine ⟨0, fun z hz => absurd ⟨_, hnorm z hz⟩ hne⟩

end GlobalTheory
