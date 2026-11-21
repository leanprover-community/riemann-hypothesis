import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

noncomputable section

open Finset

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem sum_units_addChar_mul {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (c : k) (hc : c ≠ 0) : ∑ b : kˣ, ψ (c * (b : k)) = -1 := by
  have h1 : ∑ b : kˣ, ψ (c * (b : k)) = ∑ b : kˣ, ψ (b : k) := by
    exact Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 c hc)) _ _ (fun b => by simp)
  rw [h1]
  have h2 : ∑ x : k, ψ x = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have h3 : ∑ x : k, ψ x = ψ 0 + ∑ b : kˣ, ψ (b : k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
    congr 1
    refine Finset.sum_bij' (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx)) (fun b _ => (b : k)) ?_ ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro b _; simp
    · intro x hx; simp
    · intro b _; simp
    · intro x hx; simp
  rw [h3, AddChar.map_zero_eq_one] at h2
  linear_combination h2

theorem sum_units_gauss_coeff {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (c : kˣ) : ∑ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) =
      (Fintype.card k : ℂ) * (if c = 1 then 1 else 0) - 1 := by
  have e : ∀ b : kˣ, ψ ((c : k) * (b : k)) * ψ (-(b : k)) = ψ (((c : k) - 1) * (b : k)) := by
    intro b; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp only [e]
  by_cases hc : c = 1
  · subst hc
    simp only [Units.val_one, sub_self, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_units, if_true, mul_one, nsmul_eq_mul]
    have : 1 ≤ Fintype.card k := Fintype.card_pos
    push_cast [Nat.cast_sub this]
    ring
  · have hc' : (c : k) - 1 ≠ 0 := by
      intro h; apply hc; ext; simpa [sub_eq_zero] using h
    rw [sum_units_addChar_mul ψ hψ _ hc', if_neg hc]; ring

variable (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)

theorem gs_gsD_of_diaMul (h : Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
      Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v φ := by
  intro i hi v φ hφ
  obtain ⟨h1, hm⟩ := h i hi v φ hφ
  set ψ := (D.mem u).A.psiT v with hψdef
  have hψ : ψ ≠ 1 := (D.mem u).A.psiT_ne v
  have step1 : Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v (Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v φ) =
      ∑ a : ((D.mem u).A.Fv v)ˣ, ∑ b : ((D.mem u).A.Fv v)ˣ,
        (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ := by
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Gs, Formalism.MainNotions.product_first_zeroth_parts.GsD, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hm a b⁻¹, mul_comm]
  have step2 : ∀ b : ((D.mem u).A.Fv v)ˣ,
      ∑ a : ((D.mem u).A.Fv v)ˣ, (ψ (a : (D.mem u).A.Fv v) * ψ (-(b : (D.mem u).A.Fv v))) •
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b⁻¹) φ =
      ∑ c : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) *
        ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ := by
    intro b
    refine (Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun c => ?_)).symm
    simp [mul_assoc]
  have step3 : ∀ c : ((D.mem u).A.Fv v)ˣ,
      ∑ b : ((D.mem u).A.Fv v)ˣ, (ψ ((c : (D.mem u).A.Fv v) * (b : (D.mem u).A.Fv v)) *
        ψ (-(b : (D.mem u).A.Fv v))) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ =
      (((Fintype.card ((D.mem u).A.Fv v) : ℂ) * (if c = 1 then 1 else 0)) • Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ -
        Formalism.MainNotions.product_first_zeroth_parts.dia D u i v c φ) := by
    intro c
    rw [← Finset.sum_smul, sum_units_gauss_coeff ψ hψ, sub_smul, one_smul]
  rw [step1, Finset.sum_comm, Finset.sum_congr rfl (fun b _ => step2 b), Finset.sum_comm,
    Finset.sum_congr rfl (fun c _ => step3 c), Finset.sum_sub_distrib,
    Fintype.sum_eq_single 1 (fun c hc => by simp [hc])]
  simp only [if_true, mul_one, h1, (D.mem u).A.card_Fv v, Formalism.MainNotions.product_first_zeroth_parts.Nm, LinearMap.sum_apply]



end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
