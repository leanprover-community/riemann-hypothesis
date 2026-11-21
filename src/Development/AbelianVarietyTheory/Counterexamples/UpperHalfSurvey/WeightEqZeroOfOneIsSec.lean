import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open ReciprocityTheory.ChartRestriction.G.FD NumberField

namespace GlobalTheory.FlagSecProbe

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dom_nonempty (X : Data E r) : X.dom.Nonempty := by
  classical
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    have hm : mat (Ψ := X.Ψ) (fun τ => P τ) τ = P τ := rfl
    unfold dmin lminor
    rw [hm, hG τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 ?_
  unfold psgn
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem dmin_ne_zero (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  simp [h] at this


theorem chi_zero (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h0 : X.χ 0 γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := X.χ_add 0 0 γ hγ
  rw [add_zero] at h1
  exact (mul_right_eq_self₀.1 h1.symm).resolve_right h0




end GlobalTheory.FlagSecProbe
