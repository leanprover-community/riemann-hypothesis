import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbert_exists_lineBundle_posDef_hermitian : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ u.IsAH Hm χ := by
  first | exact @GlobalTheory.AHPos.exists_lb_of_posDef | exact GlobalTheory.AHPos.exists_lb_of_posDef | (intros; apply GlobalTheory.AHPos.exists_lb_of_posDef <;> assumption)
end
end

section
section
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
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  atlas_forward_decl GlobalTheory.posn_main
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  first | exact @GlobalTheory.TorusRM.ahFactor_im_int | exact GlobalTheory.TorusRM.ahFactor_im_int | (intros; apply GlobalTheory.TorusRM.ahFactor_im_int <;> assumption)
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHBundle

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

theorem mem_of_ex_eq {L L' : LB A.left} (u : HolUnif A L g) (u' : HolUnif A L' g) (hex : u'.ex = u.ex)
    {z : Fin g → ℂ} (hz : z ∈ u.Λ) : z ∈ u'.Λ := by
  rw [← u'.ker, hex, u.ker]; exact hz

theorem isFactorAH_divUnif {M M' : LB A.left} (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (h : IsFactorAH u H χ) (h' : IsFactorAH u' H' χ') :
    IsFactorAH (GlobalTheory.SameFactor.divUnif u u' hex) (H' - H)
      (fun l => χ' ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ / χ l) := by
  refine ⟨h'.1.sub h.1, fun l => ?_, fun l p z hz => ?_⟩
  · have := h.2.1 l
    rw [norm_div, h'.2.1]
    exact (by rw [this]; norm_num : (1 : ℝ) / ‖χ l‖ = 1)
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hl : u.ex (z + l) = u.ex z := by
      rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have e' := h'.2.2 ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ p.1 z (by rw [hex]; exact h1)
    have e := h.2.2 l p.2 z h2
    have n1 := u.fr_ne p.2 z h2
    have n2 := u.fr_ne p.2 (z + l) (by rw [hl]; exact h2)
    have nχ : χ l ≠ 0 := by
      intro h0; have := h.2.1 l; rw [h0, norm_zero] at this; exact zero_ne_one this
    show u'.fr p.1 z * (u.fr p.2 z)⁻¹ = _ * _ * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹)
    rw [e', e]
    simp only [Matrix.sub_mulVec, dotProduct_sub, mul_sub]
    rw [show ∀ a b c d : ℂ, a - b + (c - d) = (a + c) - (b + d) from fun _ _ _ _ => by ring, Complex.exp_sub]
    have ne := Complex.exp_ne_zero (↑Real.pi * (z ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) +
        ↑Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))))
    field_simp

end GlobalTheory.AHBundle

theorem GlobalTheory.AHBundle.exists_lb_of_factor_chain {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A]
    (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ) (hL₀ : L₀.IsLB)
    (h₀ : IsFactorAH u₀ H₀ χ₀) (H' : Matrix (Fin g) (Fin g) ℂ)
    (M₁ : LB A.left) (u₁ : HolUnif A M₁ g) (χ₁ : u₁.Λ → ℂ) (hM₁ : M₁.IsLB) (hex₁ : u₁.ex = u₀.ex)
    (h₁ : IsFactorAH u₁ H' χ₁) (k : ℕ) :
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u (H' - k • H₀) χ := by
  induction k with
  | zero => exact ⟨M₁, u₁, χ₁, hM₁, hex₁, by simpa using h₁⟩
  | succ k ih =>
    obtain ⟨M, u, χ, hM, hex, h⟩ := ih
    have hd := GlobalTheory.AHBundle.isFactorAH_divUnif u₀ u hex h₀ h
    have e : H' - (k + 1) • H₀ = (H' - k • H₀) - H₀ := by rw [succ_nsmul, sub_add_eq_sub_sub]
    rw [← e] at hd
    exact ⟨_, _, _, LB.isLB_div hM hL₀, rfl, hd⟩

theorem GlobalTheory.AHBundle.exists_lb_of_hermitian_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hint
  obtain ⟨n, hn⟩ := (GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian) g H₀ Hm hAH.2.1
  have hint0 := (GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice) g A L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
  have hint' : ∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ m : ℤ, (l ⬝ᵥ (Hm + n • H₀).mulVec (star l')).im = m := by
    intro l hl l' hl'
    obtain ⟨m₁, e₁⟩ := hint l hl l' hl'
    obtain ⟨m₂, e₂⟩ := hint0 l hl l' hl'
    refine ⟨m₁ + n * m₂, ?_⟩
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, Complex.add_im,
      nsmul_eq_mul, Complex.mul_im, e₁, e₂]
    push_cast; simp
  have hH' : (Hm + n • H₀).IsHermitian := hHm.add (by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_nsmul, hAH.1.eq])
  obtain ⟨M₁, u₁, χ₁, hM₁, hex₁, h₁⟩ := (GlobalTheory.T.appellHumbert_exists_lineBundle_posDef_hermitian) g A hA L₀ u₀ H₀ χ₀ hL₀ hAH (Hm + n • H₀) hH' hn hint'
  obtain ⟨M, u, χ, hM, hex, h⟩ := GlobalTheory.AHBundle.exists_lb_of_factor_chain L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
    _ M₁ u₁ χ₁ hM₁ hex₁ (isFactorAH_of_isAH h₁) n
  refine ⟨M, u, χ, hM, hex, ?_⟩
  simpa using h
end
end
