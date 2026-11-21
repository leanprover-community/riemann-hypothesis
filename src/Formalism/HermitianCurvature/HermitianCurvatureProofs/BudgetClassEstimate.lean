import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma fc_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (N : ℕ) :
    CkOn N (GV k r) (C6.cutAll D χ₀ de L F) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted N W → ∀ g ∈ GV k r,
      ‖Dw W (C6.cutAll D χ₀ de L F) g‖ ≤ C * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) := by
  obtain ⟨⟨Cχ, hCχ0, hCχ⟩, hlχ⟩ := ubl_chi D hχ de L N
  set Lid : ℂ →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))).restrictScalars ℝ
  set a : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun g => Lid ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)
  have hGG : GV k r ⊆ GV k r := le_rfl
  have hua := ub_clm Lid hGG hlχ hCχ
  have hla := lss_clm Lid hlχ
  obtain ⟨c, hc⟩ := hF N
  have hcov : ∀ g ∈ GV k r, g ∈ (∅ : Set (Mat k r)) ∨ g ∈ GV k r := fun g hg => Or.inr hg
  have hP : Pr (∅ : Set (Mat k r)) (GV k r) N a F :=
    ⟨sCkOn_mono le_top (ckOn_of_lss hla ⊤), hc.1, fun _ _ h => absurd h (notMem_empty _)⟩
  have eq : C6.cutAll D χ₀ de L F = ap a F := by
    funext g; simp [C6.cutAll, ap, a, Lid]
  rw [eq]
  refine ⟨hP.ck isOpen_empty hcov, 2 ^ N * (‖Lid‖ * Cχ * max c 0), by positivity, fun W hW g hg => ?_⟩
  have hgp := gN_pos hg
  have hg1 := gN_ge_one hg
  set M := ‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)) with hM
  have hb := leib_bound isOpen_empty hcov g hg M W a F (admissible_word_mem_lie hW)
    (hP.mono (by exact_mod_cast admissible_word_length_le hW)) (by
      intro w₁ w₂ h₁ h₂ hl
      have b1 := hua w₁ (Adm_sub h₁ hW) g hg
      have b2 : ‖Dw w₂ F g‖ ≤ max c 0 * gN g ^ (-A₀) := by
        obtain ⟨u, v, hu, hv, hl', hw2⟩ := Adm_sub h₂ hW
        rw [hw2, ← dLR_eq]
        have := hc.2 u v hu hv hl' g hg
        rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgp _), mul_comm]
        exact this.trans (le_max_left _ _)
      have hex : (((2 * r + 2) * w₁.length : ℕ) : ℝ) + (-A₀) ≤ -A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ) := by
        have : (2 * r + 2) * w₁.length ≤ (2 * r + 2) * W.length :=
          Nat.mul_le_mul_left _ (by omega)
        have : (((2 * r + 2) * w₁.length : ℕ) : ℝ) ≤ (((2 * r + 2) * W.length : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      calc ‖Dw w₁ a g‖ * ‖Dw w₂ F g‖
          ≤ (‖Lid‖ * Cχ * gN g ^ (0 + (2 * r + 2) * w₁.length)) * (max c 0 * gN g ^ (-A₀)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
        _ = ‖Lid‖ * Cχ * max c 0 * gN g ^ ((((2 * r + 2) * w₁.length : ℕ) : ℝ) + (-A₀)) := by
            rw [Real.rpow_add hgp, Real.rpow_natCast, zero_add]; ring
        _ ≤ M := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hg1 hex) (by positivity))
  refine hb.trans ?_
  have h2 : (2 : ℝ) ^ W.length ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hW)
  rw [hM]
  calc 2 ^ W.length * (‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ)))
      ≤ 2 ^ N * (‖Lid‖ * Cχ * max c 0 * gN g ^ (-A₀ + (((2 * r + 2) * W.length : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring

lemma phi_bound (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    {A₀ : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ∀ mm : ℕ, InCC A₀ mm F) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (mm : ℕ) :
    CkOn mm (GV k r) (Rw w (C6.cutAll D χ₀ de L F)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ W, admitted mm W → ∀ g ∈ GV k r,
      ‖Dw W (Rw w (C6.cutAll D χ₀ de L F)) g‖ ≤
        C * gN g ^ (-A₀ + (((2 * r + 2) * (W.length + w.length) : ℕ) : ℝ)) := by
  obtain ⟨hck, C, hC0, hC⟩ := fc_bound D hχ de L hF (mm + w.length)
  have hwR : ∀ x ∈ wR w, inLie k r x.2 := fun x hx => by
    simp only [wR, List.mem_map] at hx; obtain ⟨X, hX, rfl⟩ := hx; exact hw X hX
  constructor
  · rw [← Dw_wR]
    apply CkOn_Dw hwR
    have : ((mm : ℕ∞) + ((wR w).length : ℕ∞)) = ((mm + w.length : ℕ) : ℕ∞) := by simp [wR]
    rw [this]; exact hck
  · set cw : ℝ := (w.map nz).prod with hcw
    have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (nz_pos X).le
    refine ⟨cw * C, mul_nonneg hcw0 hC0, fun W hW g hg => ?_⟩
    obtain ⟨u, v, hu, hv, hl, rfl⟩ := hW
    have hvn : ∀ X ∈ w.map nrm, unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact nrm_unit (hw Y hY)
    have e1 : Dw (wL u ++ wR v) (Rw w (C6.cutAll D χ₀ de L F)) g =
        ((cw : ℝ) : ℂ) • Dw (wL u ++ wR (v ++ w.map nrm)) (C6.cutAll D χ₀ de L F) g := by
      rw [Rw_scale, Dw_smul]
      simp only [hcw]
      congr 1
      rw [← Dw_wR, ← Dw_append]
      simp [wR, List.append_assoc]
    have hA : admitted (mm + w.length) (wL u ++ wR (v ++ w.map nrm)) :=
      ⟨u, v ++ w.map nrm, hu, fun X hX => (List.mem_append.1 hX).elim (hv X) (hvn X), by simp; omega, rfl⟩
    rw [e1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hlen' : (wL u ++ wR (v ++ w.map nrm)).length = (wL u ++ wR v).length + w.length := by
      simp [wL, wR]; ring
    rw [← hlen']
    exact hC _ hA g hg

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end Formalism.FourierDecayAlt.P
