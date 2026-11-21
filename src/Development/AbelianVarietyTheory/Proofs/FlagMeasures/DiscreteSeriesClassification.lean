import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesSUIff
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescent
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermute

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CentralChar

variable {n : ℕ}

theorem smul_one_mem (ε : Fin n → Bool) {z : ℂ} (hz : ‖z‖ = 1) :
    (z • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  unfold Formalism.REAL.inUJ
  rw [conjTranspose_smul, conjTranspose_one, smul_mul_assoc, Matrix.one_mul, mul_smul_comm,
    Matrix.mul_one, smul_smul]
  have : z * star z = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hz]; simp
  rw [this, one_smul]

theorem inv_facts (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    (Jm ε * gᴴ * Jm ε) * g = 1 ∧ g * (Jm ε * gᴴ * Jm ε) = 1 ∧ (Jm ε * gᴴ * Jm ε) ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', Jm_mul_self]
  have hr : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨hl, hr, ?_⟩
  show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε
  rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose]
  calc Jm ε * (g * Jm ε) * Jm ε * (Jm ε * gᴴ * Jm ε)
      = Jm ε * (g * (Jm ε * Jm ε) * (Jm ε * gᴴ * Jm ε)) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (g * (Jm ε * gᴴ * Jm ε)) := by rw [Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [hr, Matrix.mul_one]

theorem central_char : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), CompleteSpace H →
    Nontrivial H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∃ m : ℤ, Ext ε m σ σ := by
  intro n _ ε H _ _ σ hc hnt hrep hirr
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hrep
  have hstar : ∀ g ∈ UJset ε, star (σ g) = σ (Jm ε * gᴴ * Jm ε) := by
    intro g hg
    obtain ⟨-, hr, hm⟩ := inv_facts ε hg
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hiso g hg⟩
    have hx : σ g (σ (Jm ε * gᴴ * Jm ε) x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul g hg _ hm, hr, h1]; rfl
    calc ⟪σ (Jm ε * gᴴ * Jm ε) x, y⟫_ℂ = ⟪L (σ (Jm ε * gᴴ * Jm ε) x), L y⟫_ℂ :=
          (L.inner_map_map _ _).symm
      _ = ⟪x, σ g y⟫_ℂ := by
          show ⟪σ g (σ (Jm ε * gᴴ * Jm ε) x), σ g y⟫_ℂ = _
          rw [hx]
  have hscal : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℂ, σ (z • 1) = c • (1 : H →L[ℂ] H) := by
    intro z hz
    apply Formalism.MainNotions.BridgeCSchur.schur_bounded (σ '' UJset ε)
    · rintro _ ⟨g, hg, rfl⟩; exact ⟨_, (inv_facts ε hg).2.2, (hstar g hg).symm⟩
    · intro S hS hst; exact hirr S hS (fun g hg v hv => hst _ ⟨g, hg, rfl⟩ v hv)
    · rintro _ ⟨g, hg, rfl⟩
      have hz1 := smul_one_mem ε hz
      show σ (z • 1) * σ g = σ g * σ (z • 1)
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ← hmul _ hz1 _ hg,
        ← hmul _ hg _ hz1, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]
  obtain ⟨v0, hv0⟩ := exists_ne (0 : H)
  let χ : ℂ → ℂ := fun z => ⟪v0, σ (z • 1) v0⟫_ℂ / ⟪v0, v0⟫_ℂ
  have hvv : ⟪v0, v0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv0
  have hχ : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) = χ z • (1 : H →L[ℂ] H) := by
    intro z hz
    obtain ⟨c, hc'⟩ := hscal z hz
    have : χ z = c := by
      simp only [χ, hc', ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        inner_smul_right]
      field_simp
    rw [this, hc']
  have hχv : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) v0 = χ z • v0 := by
    intro z hz; rw [hχ z hz]; rfl
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖χ z‖ = 1 := by
    intro z hz
    have h := hiso _ (smul_one_mem ε hz) v0
    rw [hχv z hz, norm_smul] at h
    have hp : 0 < ‖v0‖ := norm_pos_iff.mpr hv0
    nlinarith [h]
  have hne : ∀ w : Circle, χ w ≠ 0 := by
    intro w h0
    have := hnorm w (Circle.norm_coe _)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hcontχ : Continuous fun w : Circle => χ w := by
    have hc1 : Continuous fun w : Circle => σ ((w : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 :=
      (hcont v0).comp_continuous (by fun_prop) (fun w => smul_one_mem ε (Circle.norm_coe _))
    exact (continuous_const.inner hc1).div_const _
  let χU : Circle →ₜ* ℂˣ :=
    { toFun := fun w => Units.mk0 (χ w) (hne w)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one, Circle.coe_one, χ, one_smul, h1,
          ContinuousLinearMap.one_apply]
        exact div_self hvv
      map_mul' := by
        intro a b
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have ha := smul_one_mem ε (z := (a : ℂ)) (Circle.norm_coe _)
        have hb := smul_one_mem ε (z := (b : ℂ)) (Circle.norm_coe _)
        have hab : σ (((a * b : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0
            = (χ a * χ b) • v0 := by
          rw [Circle.coe_mul, show ((a : ℂ) * b) • (1 : Matrix (Fin n) (Fin n) ℂ) =
            ((a : ℂ) • 1) * ((b : ℂ) • 1) by rw [smul_mul_smul_comm, Matrix.one_mul], hmul _ ha _ hb,
            ContinuousLinearMap.comp_apply, hχv _ (Circle.norm_coe b), map_smul, hχv _ (Circle.norm_coe a),
            smul_smul, mul_comm]
        rw [hχv _ (Circle.norm_coe (a * b))] at hab
        exact smul_left_injective ℂ hv0 hab
      continuous_toFun := by
        rw [Units.continuous_iff]
        refine ⟨hcontχ, ?_⟩
        simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact hcontχ.inv₀ hne }
  obtain ⟨m, hm, -⟩ := GroundTheory.Global.existsUnique_circle_zpow χU
  refine ⟨m, fun z hz g hg => ?_⟩
  have hz1 := smul_one_mem ε hz
  have hw : ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z := by
    rw [Circle.coe_exp]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this; simpa using this
  have hχz : χ z = z ^ m := by
    have : χ ((Circle.exp (Complex.arg z) : Circle) : ℂ) = ((Circle.exp (Complex.arg z) : Circle) : ℂ) ^ m :=
      hm (Circle.exp (Complex.arg z))
    rwa [hw] at this
  rw [show z • g = (z • (1 : Matrix (Fin n) (Fin n) ℂ)) * g by rw [smul_mul_assoc, Matrix.one_mul],
    hmul _ hz1 _ hg.1, hχ z hz, hχz]
  ext v
  rfl

end GlobalTheory.CentralChar
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_parameter_descent : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsParU lam → ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ IsParS (fun a => lam a - (m : ℝ) / n) ∧ (IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsHCU ε lam π) := by
  first | exact @GlobalTheory.SUtoU.extension_main | exact GlobalTheory.SUtoU.extension_main | (intros; apply GlobalTheory.SUtoU.extension_main <;> assumption)
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SuVPar

open GlobalTheory.DSSU

theorem diag_mem {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ SUset ε := by
  refine ⟨?_, ?_⟩
  · show Formalism.REAL.inUJ ε _
    unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : star (Complex.exp ((θ a : ℂ) * Complex.I)) * Complex.exp ((θ a : ℂ) * Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp [Complex.conj_ofReal]
    calc star (Complex.exp ((θ a : ℂ) * Complex.I)) * (if ε a = true then 1 else -1) *
          Complex.exp ((θ a : ℂ) * Complex.I)
        = (star (Complex.exp ((θ a : ℂ) * Complex.I)) * Complex.exp ((θ a : ℂ) * Complex.I)) *
            (if ε a = true then 1 else -1) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul]
    have : (∑ a, (θ a : ℂ)) = 0 := by exact_mod_cast hθ
    rw [this, zero_mul, Complex.exp_zero]

theorem one_mem {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  have h := diag_mem ε (fun _ => 0) (by simp)
  simpa using h

theorem rho_diff {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (hinj : Function.Injective lam) (a : Fin n) :
    ∃ k : ℤ, rhoNh ε lam a - rhoCh ε lam a = ((n : ℝ) - 1) / 2 - k := by
  set A := (univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card
  set B := (univ.filter fun b => lam a < lam b ∧ ε b ≠ ε a).card
  set C := (univ.filter fun b => lam b < lam a ∧ ε b = ε a).card
  set D := (univ.filter fun b => lam a < lam b ∧ ε b = ε a).card
  have key : (A : ℝ) + B + C + D = n - 1 := by
    simp only [A, B, C, D, Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hpt : ∀ b : Fin n, ((if lam b < lam a ∧ ε b ≠ ε a then (1:ℝ) else 0) +
        (if lam a < lam b ∧ ε b ≠ ε a then (1:ℝ) else 0) +
        (if lam b < lam a ∧ ε b = ε a then (1:ℝ) else 0) +
        (if lam a < lam b ∧ ε b = ε a then (1:ℝ) else 0)) = 1 - (if a = b then 1 else 0) := by
      intro b
      by_cases hab : a = b
      · subst hab; simp
      · have hne : lam b ≠ lam a := fun h => hab (hinj h).symm
        rcases lt_or_gt_of_ne hne with h | h <;> by_cases he : ε b = ε a <;>
          simp [h, he, hab, not_lt_of_gt h]
    rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  refine ⟨(B + C : ℕ), ?_⟩
  simp only [rhoNh, rhoCh]
  change ((A : ℝ) - B) / 2 - ((C : ℝ) - D) / 2 = _
  push_cast
  linarith

theorem wt_int {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hE : Ext ε m π' π)
    (Λ : Fin n → ℝ) (hΛ : ∑ a, Λ a = 0) (v : H) (hv : v ≠ 0) (hw : IsWtS π' Λ v) (a : Fin n) :
    ∃ k : ℤ, Λ a + (m : ℝ) / n = k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)

  have h1 : π' 1 v = v := by
    have := hw (fun _ => 0) (by simp)
    simpa using this
  have hπ1 : π 1 = π' 1 := by
    have := hE 1 (by simp) 1 (one_mem ε)
    simpa using this
  set θ : Fin n → ℝ := fun b => (if b = a then 2 * Real.pi else 0) - 2 * Real.pi / n with hθdef
  have hθ : ∑ b, θ b = 0 := by
    simp only [hθdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  set z : ℂ := Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) with hz
  have hz1 : ‖z‖ = 1 := by rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hzg : z • Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, smul_eq_mul, hz]
      rw [← Complex.exp_add]
      rw [Complex.exp_eq_one_iff]
      by_cases hia : i = a
      · refine ⟨1, ?_⟩
        simp only [hθdef, hia, if_true]
        push_cast
        ring
      · refine ⟨0, ?_⟩
        simp only [hθdef, hia, if_false]
        push_cast
        ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hmain := hE z hz1 _ (diag_mem ε θ hθ)
  rw [hzg, hπ1] at hmain
  have hv2 := congrArg (fun T : H →L[ℂ] H => T v) hmain
  simp only [h1, ContinuousLinearMap.smul_apply, hw θ hθ, smul_smul] at hv2

  have hsum : (∑ b, Λ b * θ b) = 2 * Real.pi * Λ a := by
    simp only [hθdef, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← Finset.sum_mul, hΛ, zero_mul, sub_zero]
    ring
  rw [hsum] at hv2
  have hc : z ^ m * Complex.exp (((2 * Real.pi * Λ a : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    have : (z ^ m * Complex.exp (((2 * Real.pi * Λ a : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hv2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hv h
  rw [hz, ← Complex.exp_int_mul, ← Complex.exp_add, Complex.exp_eq_one_iff] at hc
  obtain ⟨k, hk⟩ := hc
  refine ⟨k, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((Λ a + (m : ℝ) / n : ℝ) : ℂ) = (k : ℂ) := by
    apply mul_right_cancel₀ hpi
    rw [← hk]
    push_cast
    field_simp
    ring
  exact_mod_cast this

end GlobalTheory.SuVPar

namespace GlobalTheory.SuVPar

theorem parS_lifts : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ lam' : Fin n → ℝ, IsParS lam' → (∃ S : Submodule ℂ H, IsKTypeS ε lam' π' (lowCh ε lam') S) → IsParU (fun a => lam' a + (m : ℝ) / n) ∧ ∑ a, (lam' a + (m : ℝ) / n) = (m : ℝ) := by
  intro n hn ε H _ _ m π' π hE lam' hP hS
  obtain ⟨hsum0, hinj, -⟩ := hP
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b h
    exact hinj (add_right_cancel h)
  · intro a
    obtain ⟨S, hΛ, -, -, -, ⟨v, -, hv, hw⟩, -⟩ := hS
    obtain ⟨k1, hk1⟩ := wt_int hn ε m π' π hE _ hΛ v hv hw a
    obtain ⟨k2, hk2⟩ := rho_diff ε lam' hinj a
    refine ⟨k1 + k2 - n + 1, ?_⟩
    have hl : lowCh ε lam' a = lam' a + rhoNh ε lam' a - rhoCh ε lam' a := rfl
    push_cast
    linarith
  · rw [Finset.sum_add_distrib, hsum0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

end GlobalTheory.SuVPar
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_type_parameter_ascent : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ lam' : Fin n → ℝ, IsParS lam' → (∃ S : Submodule ℂ H, IsKTypeS ε lam' π' (lowCh ε lam') S) → IsParU (fun a => lam' a + (m : ℝ) / n) ∧ ∑ a, (lam' a + (m : ℝ) / n) = (m : ℝ) := by
  atlas_forward_decl GlobalTheory.SuVPar.parS_lifts
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SUtoU

variable {n : ℕ}

theorem equivOn_of_ext (hn : 1 ≤ n) (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (m : ℤ)
    {σ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (h : Ext ε m σ π) (h' : Ext ε m σ' π') (hT : EquivOn (SUset ε) σ σ') : EquivOn (UJset ε) π π' := by
  obtain ⟨T, hT⟩ := hT
  refine ⟨T, fun g hg v => ?_⟩
  obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := (GlobalTheory.T.unitary_to_special_unitary_local n hn ε).1 g hg
  rw [h z hz g₀ hg₀, h' z hz g₀ hg₀, _root_.smul_apply, _root_.smul_apply,
    LinearIsometryEquiv.map_smul, hT g₀ hg₀ v]

def meanFree (lam : Fin n → ℝ) : Fin n → ℝ := fun a => lam a - (∑ b, lam b) / n

def ExtProp (ε : Fin n → Bool) (F : Fam n) (lam : Fin n → ℝ)
    (π : Matrix (Fin n) (Fin n) ℂ → (F.H (meanFree lam) →L[ℂ] F.H (meanFree lam))) : Prop :=
  ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ Ext ε m (F.π (meanFree lam)) π ∧ IsHCU ε lam π

def famU (ε : Fin n → Bool) (F : Fam n) : Fam n where
  H lam := F.H (meanFree lam)
  nacg _ := inferInstance
  ips _ := inferInstance
  π lam := Classical.epsilon (ExtProp ε F lam)

theorem parS_meanFree (hn : 1 ≤ n) {lam : Fin n → ℝ} (hlam : IsParU lam) : IsParS (meanFree lam) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [meanFree, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hn0, sub_self]
  · intro a b h
    exact hlam.1 (by simpa [meanFree] using h)
  · intro a b
    obtain ⟨p, hp⟩ := hlam.2 a
    obtain ⟨q, hq⟩ := hlam.2 b
    exact ⟨p - q, by simp only [meanFree]; push_cast; linarith⟩

theorem exists_ext (hn : 1 ≤ n) (ε : Fin n → Bool) (F : Fam n) (hF : ParamS ε F) (lam : Fin n → ℝ)
    (hlam : IsParU lam) : ∃ π, ExtProp ε F lam π := by
  obtain ⟨m, hsum, -, hext⟩ := GlobalTheory.T.harish_chandra_parameter_descent n hn ε (F.H (meanFree lam)) (F.π (meanFree lam)) lam hlam
  have hμ : meanFree lam = fun a => lam a - (m : ℝ) / n := by funext a; simp [meanFree, hsum]
  have key : ∀ ν, ν = meanFree lam → IsHCS ε ν (F.π (meanFree lam)) := by
    rintro ν rfl; exact hF.1 _ (parS_meanFree hn hlam)
  obtain ⟨π, hπ1, hπ2⟩ := hext (key _ hμ.symm)
  exact ⟨π, m, hsum, hπ1, hπ2⟩

theorem famU_spec (hn : 1 ≤ n) (ε : Fin n → Bool) (F : Fam n) (hF : ParamS ε F) (lam : Fin n → ℝ)
    (hlam : IsParU lam) : ExtProp ε F lam ((famU ε F).π lam) :=
  Classical.epsilon_spec (exists_ext hn ε F hF lam hlam)

theorem classF_of_classS : ∀ (n : ℕ), 1 ≤ n → ∀ ε : Fin n → Bool, ClassS ε → ClassF ε := by
  intro n hn ε hS
  obtain ⟨F, hP, hE⟩ := hS
  refine ⟨famU ε F, fun lam hlam => ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, h⟩ := famU_spec hn ε F hP lam hlam
    exact h
  · rintro lam lam' hlam ⟨w, hw, rfl⟩
    have hlam' : IsParU (lam ∘ w) := ⟨hlam.1.comp w.injective, fun a => hlam.2 (w a)⟩
    obtain ⟨m, hs, he, -⟩ := famU_spec hn ε F hP lam hlam
    obtain ⟨m', hs', he', -⟩ := famU_spec hn ε F hP _ hlam'
    have hsum : ∑ a, lam (w a) = ∑ a, lam a := Equiv.sum_comp w lam
    have hmm : m' = m := by exact_mod_cast (hs'.symm.trans ((show ∑ a, (lam ∘ w) a = ∑ a, lam a from hsum).trans hs))
    subst hmm
    refine equivOn_of_ext hn ε _ he he' ?_
    have hc : ConjK ε (meanFree lam) (meanFree (lam ∘ w)) := ⟨w, hw, by funext a; simp [meanFree, Function.comp_apply, hsum]⟩
    exact (hP.2 _ _ (parS_meanFree hn hlam) (parS_meanFree hn hlam')).2 hc
  · intro H' _ _ σ hσ
    obtain ⟨hc, hnt, hu, hirr, hsq⟩ := hσ
    obtain ⟨m, hm⟩ := GlobalTheory.CentralChar.central_char n hn ε H' σ hc hnt hu hirr
    obtain ⟨huS, hirrS, -, -⟩ := GlobalTheory.T.extension_preserves_properties n hn ε H' m σ σ hm
    have hsqS := (GlobalTheory.T.square_integrable_iff_extension n hn ε H' m σ σ hm hu).1 hsq
    obtain ⟨lam', hpar', T, hT⟩ := hE H' σ ⟨hc, hnt, huS hu, hirrS.1 hirr, hsqS⟩
    let ρ : Matrix (Fin n) (Fin n) ℂ → (F.H lam' →L[ℂ] F.H lam') := fun g =>
      (T.toContinuousLinearEquiv : H' →L[ℂ] F.H lam').comp
        ((σ g).comp (T.symm.toContinuousLinearEquiv : F.H lam' →L[ℂ] H'))
    have hρ : Ext ε m (F.π lam') ρ := by
      intro z hz g hg
      ext v
      have h1 : ρ (z • g) v = T (σ (z • g) (T.symm v)) := rfl
      rw [h1, hm z hz g hg, _root_.smul_apply, _root_.smul_apply,
        LinearIsometryEquiv.map_smul, hT g hg, LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨S, hS, -⟩ := (hP.1 lam' hpar').2.2.1
    obtain ⟨hparU, hsumU⟩ := GlobalTheory.T.lowest_type_parameter_ascent n hn ε (F.H lam') m (F.π lam') ρ hρ lam' hpar' ⟨S, hS⟩
    refine ⟨fun a => lam' a + (m : ℝ) / n, hparU, ?_⟩
    obtain ⟨m₁, hs₁, he₁, -⟩ := famU_spec hn ε F hP _ hparU
    have hm₁ : m₁ = m := by exact_mod_cast hs₁.symm.trans hsumU
    subst hm₁
    have hμ : meanFree (fun a => lam' a + (m₁ : ℝ) / n) = lam' := by
      funext a; simp only [meanFree]; rw [hsumU]; ring
    have key : ∀ ν, ν = lam' → EquivOn (SUset ε) σ (F.π ν) := by rintro ν rfl; exact ⟨T, hT⟩
    exact equivOn_of_ext hn ε _ hm he₁ (key _ hμ)

end GlobalTheory.SUtoU
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_of_special_unitary : ∀ (n : ℕ), 1 ≤ n → ∀ ε : Fin n → Bool, ClassS ε → ClassF ε := by
  atlas_forward_decl GlobalTheory.SUtoU.classF_of_classS
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_permute : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (s : Equiv.Perm (Fin n)), (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → StrictAnti (lam ∘ s) → IsHCU ε lam σ → IsHCDS (ε ∘ s) (lam ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) := by
  first | exact @GlobalTheory.DSSU.Chamber.vChamber | exact GlobalTheory.DSSU.Chamber.vChamber | (intros; apply GlobalTheory.DSSU.Chamber.vChamber <;> assumption)
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SignRenumber

def signKey {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℕ := (if ε a = true then 0 else n) + a.val

lemma signKey_injective {n : ℕ} (ε : Fin n → Bool) : Function.Injective (signKey ε) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold signKey at h
  split_ifs at h <;> omega

lemma signKey_lt_iff_of_eq {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    signKey ε a < signKey ε b ↔ a < b := by
  unfold signKey
  rw [h, Fin.lt_iff_val_lt_val]
  split_ifs <;> omega

lemma signKey_lt_n_iff {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : signKey ε a < n ↔ ε a = true := by
  have ha := a.isLt
  unfold signKey
  cases h : ε a <;> simp <;> omega

lemma signKey_true_lt_false {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (ha : ε a = true)
    (hb : ε b = false) : signKey ε a < signKey ε b := by
  have h1 := (signKey_lt_n_iff ε a).mpr ha
  have h2 : ¬ signKey ε b < n := by rw [signKey_lt_n_iff, hb]; simp
  omega

lemma val_eq_rank {n : ℕ} (κ : Fin n → ℕ) (hκ : Function.Injective κ) (f : Equiv.Perm (Fin n))
    (hf : ∀ a b, κ a < κ b → f a < f b) (a : Fin n) :
    (f a).val = (univ.filter (fun b => κ b < κ a)).card := by
  have hiff : ∀ b, f b < f a ↔ κ b < κ a := by
    intro b
    constructor
    · intro h
      rcases lt_trichotomy (κ b) (κ a) with h' | h' | h'
      · exact h'
      · exact absurd (congrArg f (hκ h')) (ne_of_lt h)
      · exact absurd (hf a b h') (not_lt.mpr h.le)
    · exact hf b a
  rw [← Fin.card_Iio (f a)]
  refine Finset.card_nbij' (fun i => f.symm i) (fun b => f b) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_Iio, Set.mem_Iio, Finset.mem_Iio] at hi
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [← hiff]
    simpa using hi
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hb
    simp only [Finset.coe_Iio, Set.mem_Iio, Finset.mem_Iio]
    exact (hiff b).mpr hb
  · intro i _
    simp
  · intro b _
    simp

def signCount {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter (fun a => ε a = true)).card

def stdSign {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : Bool := decide (i.val < signCount ε)

def renumber {n : ℕ} (ε : Fin n → Bool) : Equiv.Perm (Fin n) := (Tuple.sort (signKey ε))⁻¹

lemma renumber_compat {n : ℕ} (ε : Fin n → Bool) (a b : Fin n)
    (h : signKey ε a < signKey ε b) : renumber ε a < renumber ε b := by
  by_contra h'
  have hm := Tuple.monotone_sort (signKey ε) (not_lt.mp h')
  simp only [Function.comp_apply, renumber, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hm
  exact absurd hm (not_le.mpr h)

lemma renumber_val {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (renumber ε a).val = (univ.filter (fun b => signKey ε b < signKey ε a)).card :=
  val_eq_rank (signKey ε) (signKey_injective ε) (renumber ε) (renumber_compat ε) a

lemma renumber_lt_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) : renumber ε a < renumber ε b :=
  renumber_compat ε a b ((signKey_lt_iff_of_eq ε he).mpr hab)

lemma stdSign_renumber {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    stdSign ε (renumber ε a) = ε a := by
  unfold stdSign
  rw [renumber_val]
  cases h : ε a
  · have : signCount ε ≤ (univ.filter (fun b => signKey ε b < signKey ε a)).card := by
      apply Finset.card_le_card
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact signKey_true_lt_false ε hb h
    simpa using this
  · have : (univ.filter (fun b => signKey ε b < signKey ε a)).card < signCount ε := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨a, by simp [h], by simp⟩
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact (signKey_lt_n_iff ε b).mp (lt_trans hb ((signKey_lt_n_iff ε a).mpr h))
    simpa using this

lemma signCount_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) :
    signCount (ε ∘ s) = signCount ε := by
  unfold signCount
  refine Finset.card_nbij' (fun a => s a) (fun b => s.symm b) ?_ ?_ ?_ ?_ <;> intro x hx <;> simp_all

lemma stdSign_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) :
    stdSign (ε ∘ s) = stdSign ε := by
  funext i
  unfold stdSign
  rw [signCount_comp]

lemma renumber_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (a : Fin n) :
    renumber (ε ∘ s) a = renumber ε (s a) := by
  have hc : ∀ x y, signKey (ε ∘ s) x < signKey (ε ∘ s) y →
      (s.trans (renumber ε)) x < (s.trans (renumber ε)) y := by
    intro x y hxy
    simp only [Equiv.trans_apply]
    apply renumber_compat
    by_cases he : ε (s x) = ε (s y)
    · have hxy' := (signKey_lt_iff_of_eq (ε ∘ s) (a := x) (b := y) he).mp hxy
      exact (signKey_lt_iff_of_eq ε he).mpr (hs x y hxy' he)
    · cases hx : ε (s x) <;> cases hy : ε (s y)
      · rw [hx, hy] at he; exact absurd rfl he
      · have h1 : ¬ signKey (ε ∘ s) x < n := by
          rw [signKey_lt_n_iff]; simpa using hx
        have h2 : signKey (ε ∘ s) y < n := by
          rw [signKey_lt_n_iff]; simpa using hy
        omega
      · exact signKey_true_lt_false ε hx hy
      · rw [hx, hy] at he; exact absurd rfl he
  exact Fin.ext ((val_eq_rank _ (signKey_injective _) (renumber (ε ∘ s)) (renumber_compat _) a).trans
    (val_eq_rank _ (signKey_injective _) (s.trans (renumber ε)) hc a).symm)

theorem block_renumbering :
    ∀ n : ℕ, ∃ (std : (Fin n → Bool) → (Fin n → Bool)) (t : (Fin n → Bool) → Equiv.Perm (Fin n)),
      (∀ ε, std ε ∘ t ε = ε ∧ ∀ a b, a < b → ε a = ε b → t ε a < t ε b) ∧
      (∀ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), std (ε ∘ s) = std ε ∧
        ((∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → ∀ a, t (ε ∘ s) a = t ε (s a))) ∧
      ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Function.Injective lam →
        ∃ (w s : Equiv.Perm (Fin n)), (∀ a, ε (w a) = ε a) ∧ StrictAnti ((lam ∘ w) ∘ s) ∧
          ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b := by
  intro n
  refine ⟨stdSign, renumber, ?_, ?_, ?_⟩
  · intro ε
    exact ⟨funext fun a => stdSign_renumber ε a, fun a b hab he => renumber_lt_of_lt ε hab he⟩
  · intro ε s
    exact ⟨stdSign_comp ε s, fun hs a => renumber_comp ε s hs a⟩
  · intro ε lam hlam
    obtain ⟨u, hu⟩ : ∃ u : Equiv.Perm (Fin n), StrictAnti (lam ∘ u) := by
      refine ⟨Tuple.sort (fun a => -lam a), ?_⟩
      have hinj : Function.Injective ((fun a => -lam a) ∘ Tuple.sort (fun a => -lam a)) :=
        (neg_injective.comp hlam).comp (Tuple.sort (fun a => -lam a)).injective
      have hmono := (Tuple.monotone_sort (fun a => -lam a)).strictMono_of_injective hinj
      intro a b hab
      have := hmono hab
      simp only [Function.comp_apply, neg_lt_neg_iff] at this
      simpa using this
    let s : Equiv.Perm (Fin n) := (renumber (ε ∘ u)).trans (renumber ε).symm
    have hs_ren : ∀ x, renumber ε (s x) = renumber (ε ∘ u) x := by
      intro x; simp [s]
    have hsx : ∀ x, ε (s x) = ε (u x) := by
      intro x
      have h := stdSign_renumber (ε ∘ u) x
      rw [stdSign_comp] at h
      rw [← stdSign_renumber ε (s x), hs_ren]
      exact h
    refine ⟨s.symm.trans u, s, ?_, ?_, ?_⟩
    · intro a
      simp only [Equiv.trans_apply]
      rw [← hsx, Equiv.apply_symm_apply]
    · have : (lam ∘ ⇑(s.symm.trans u)) ∘ ⇑s = lam ∘ u := by
        funext a; simp
      rw [this]; exact hu
    · intro a b hab he
      rcases lt_trichotomy (s a) (s b) with h | h | h
      · exact h
      · exact absurd (s.injective h) (ne_of_lt hab)
      · have h1 := renumber_lt_of_lt ε h he.symm
        rw [hs_ren, hs_ren] at h1
        have he' : (ε ∘ u) a = (ε ∘ u) b := by
          show ε (u a) = ε (u b)
          rw [← hsx, ← hsx]; exact he
        have h2 := renumber_lt_of_lt (ε ∘ u) hab he'
        exact absurd h1 (not_lt.mpr h2.le)

end GlobalTheory.SignRenumber
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.DSSU

theorem classU_of_classF : ∀ n : ℕ, (∀ ε : Fin n → Bool, ClassF ε) → ClassU n := by
  intro n hF
  unfold ClassF at hF
  choose F hP hC hE using hF
  obtain ⟨std, t, ht, hst, hren⟩ := GlobalTheory.SignRenumber.block_renumbering n
  have e1a : ∀ (ε : Fin n → Bool) (x : Fin n), std ε (t ε x) = ε x := fun ε x => congrFun (ht ε).1 x
  have hmono : ∀ (ε : Fin n → Bool) (a b : Fin n), a < b → std ε (t ε a) = std ε (t ε b) → t ε a < t ε b := by
    intro ε a b hab h
    rw [e1a, e1a] at h
    exact (ht ε).2 a b hab h
  refine ⟨fun ε lam => (F (std ε)).H (lam ∘ (t ε).symm), fun ε lam => inferInstance, fun ε lam => inferInstance,
    fun ε lam g => (F (std ε)).π (lam ∘ (t ε).symm) (g.submatrix (t ε).symm (t ε).symm), ?_, ?_⟩
  · intro ε lam hlam
    have hpar : IsParU (lam ∘ (t ε).symm) :=
      ⟨hlam.1.injective.comp (t ε).symm.injective, fun a => hlam.2 _⟩
    have e2 : (lam ∘ (t ε).symm) ∘ (t ε) = lam := by funext a; simp
    have h1 := GlobalTheory.T.harish_chandra_permute n (std ε) _ ((F (std ε)).π (lam ∘ (t ε).symm)) (lam ∘ (t ε).symm) (t ε)
      (hmono ε) (by rw [e2]; exact hlam.1) (hP _ _ hpar)
    rw [(ht ε).1, e2] at h1
    exact h1
  · intro ε H' _ _ σ' hσ
    let σ₀ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H') := fun g => σ' (g.submatrix (t ε) (t ε))
    have hσ₀ : IsSqIntIrr (std ε) σ₀ := by
      rw [(GlobalTheory.DSId.PermK.permKType n (std ε) (t ε) H' σ₀ (hmono ε)).2.2.2.1]
      have e3 : (fun g : Matrix (Fin n) (Fin n) ℂ => σ₀ (g.submatrix (t ε).symm (t ε).symm)) = σ' := by
        funext g
        simp only [σ₀, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
      rw [(ht ε).1, e3]
      exact hσ
    obtain ⟨lam₀, hpar₀, T, hT⟩ := hE (std ε) H' σ₀ hσ₀
    obtain ⟨w, s, hw, hanti, hs⟩ := hren ε (lam₀ ∘ t ε) (hpar₀.1.comp (t ε).injective)
    refine ⟨s, ((lam₀ ∘ t ε) ∘ w) ∘ s, ⟨hanti, fun a => hpar₀.2 _⟩, hs, ?_⟩
    have hstd : std (ε ∘ s) = std ε := (hst ε s).1
    have htt : t (ε ∘ s) = s.trans (t ε) := Equiv.ext ((hst ε s).2 hs)
    show UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm))
      (fun g => (F (std (ε ∘ s))).π ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (t (ε ∘ s)).symm)
        (g.submatrix (t (ε ∘ s)).symm (t (ε ∘ s)).symm))
    rw [htt, hstd]
    have hconj : ConjK (std ε) lam₀ ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (s.trans (t ε)).symm) := by
      refine ⟨(t ε).symm.trans (w.trans (t ε)), ?_, ?_⟩
      · intro a
        simp only [Equiv.trans_apply]
        rw [e1a, hw, ← e1a ε ((t ε).symm a), Equiv.apply_symm_apply]
      · funext a
        simp [Equiv.symm_trans_apply]
    obtain ⟨T2, hT2⟩ := hC (std ε) lam₀ _ hpar₀ hconj
    refine ⟨T.trans T2, ?_⟩
    intro g hg v
    have hcomp : std ε ∘ (s.trans (t ε)) = ε ∘ s := by
      funext a; simp [Equiv.trans_apply, e1a]
    have hh : g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm ∈ UJset (std ε) :=
      (((GlobalTheory.Dec.PermGroup.permGroup n (std ε) (s.trans (t ε))).1 g).1).mp (by rw [hcomp]; exact hg)
    have hσh : σ₀ (g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm) = σ' (g.submatrix s.symm s.symm) := by
      show σ' ((g.submatrix _ _).submatrix (t ε) (t ε)) = _
      rw [Matrix.submatrix_submatrix]
      congr 2 <;> funext a <;> simp [Equiv.symm_trans_apply]
    simp only [LinearIsometryEquiv.trans_apply]
    rw [← hσh, hT _ hh, hT2 _ hh]

end GlobalTheory.DSSU
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_unitary_of_full : ∀ n : ℕ, (∀ ε : Fin n → Bool, ClassF ε) → ClassU n := by
  atlas_forward_decl GlobalTheory.DSSU.classU_of_classF
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Triv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_iso_of_irred {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [Nontrivial H']
    (h : ∀ S : Submodule ℂ H', IsClosed (S : Set H') → S = ⊥ ∨ S = ⊤) : Nonempty (H' ≃ₗᵢ[ℂ] ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H')
  have hu : ‖((‖v‖⁻¹ : ℂ) • v)‖ = 1 := norm_smul_inv_norm hv
  set u := ((‖v‖⁻¹ : ℂ) • v)
  have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
  have hS : (ℂ ∙ u) = ⊤ := by
    rcases h (ℂ ∙ u) (Submodule.closed_of_finiteDimensional _) with h0 | h1
    · exact absurd (Submodule.span_singleton_eq_bot.1 h0) hu0
    · exact h1
  have hsurj : Function.Surjective (LinearIsometry.toSpanSingleton ℂ H' hu) := by
    intro x
    have hx : x ∈ (ℂ ∙ u) := by rw [hS]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨a, by simpa using ha⟩
  exact ⟨(LinearIsometryEquiv.ofSurjective _ hsurj).symm⟩

theorem det_eq_one_fin_one (g : Matrix (Fin 1) (Fin 1) ℂ) (h : g.det = 1) : g = 1 := by
  ext i j
  fin_cases i; fin_cases j
  rw [Matrix.det_unique] at h
  simpa using h

instance subsingleton_SUJ (ε : Fin 1 → Bool) : Subsingleton (SUJ ε) :=
  ⟨fun a b => Subtype.ext (Subtype.ext (Units.ext
    ((det_eq_one_fin_one _ a.2).trans (det_eq_one_fin_one _ b.2).symm)))⟩

theorem E0_fin_one (a b : Fin 1) : E0 a b = 0 := by
  fin_cases a; fin_cases b
  ext i j
  fin_cases i; fin_cases j
  simp [E0]

theorem Ec_zero_fin_one (ε : Fin 1 → Bool) (G : Matrix (Fin 1) (Fin 1) ℂ → ℂ) : Ec ε 0 G = 0 := by
  funext g
  simp [Ec, Rd, cpart1, cpart2]

theorem eq_zero_of_sum_fin_one (μ : Fin 1 → ℝ) (h : ∑ a, μ a = 0) : μ = 0 := by
  funext a; fin_cases a; simpa using h

theorem above_self {n : ℕ} (P : Fin n → Fin n → Prop) (μ : Fin n → ℝ) : Above P μ μ :=
  ⟨0, fun a b h => absurd rfl h, by simp⟩

theorem lowCh_fin_one_zero (ε : Fin 1 → Bool) : lowCh ε 0 = 0 := by
  funext a; fin_cases a; simp [lowCh, rhoNh, rhoCh]

theorem gelfVal_fin_one_zero (k : ℕ) : gelfVal (fun a : Fin 1 => ((0 : Fin 1 → ℝ) a : ℂ)) (k + 1) = 0 := by
  have hA : Formalism.REAL.Amat (fun c : Fin 1 => ((0 : Fin 1 → ℝ) c : ℂ) + (((1 : ℕ) : ℂ) - 1) / 2) = 0 := by
    ext i j; fin_cases i; fin_cases j; simp [Formalism.REAL.Amat]
  rw [gelfVal, hA]; simp

abbrev famOne : Fam 1 := ⟨fun _ => ℂ, fun _ => inferInstance, fun _ => inferInstance, fun _ _ => 1⟩

theorem classS_one (ε : Fin 1 → Bool) : ClassS ε := by
  have hSU : ∀ g ∈ SUset ε, g = 1 := fun g hg => det_eq_one_fin_one g hg.2
  have hpar : ∀ lam : Fin 1 → ℝ, IsParS lam → lam = 0 := fun lam h => eq_zero_of_sum_fin_one lam h.1
  have hpar0 : IsParS (0 : Fin 1 → ℝ) :=
    ⟨by simp, fun a b _ => Subsingleton.elim a b, fun a b => ⟨0, by simp⟩⟩
  refine ⟨famOne, ⟨?_, ?_⟩, ?_⟩
  · intro lam hlam
    obtain rfl := hpar lam hlam
    have hK : IsKTypeS ε 0 (famOne.π 0) (lowCh ε 0) ⊤ := by
      rw [lowCh_fin_one_zero]
      refine ⟨by simp, inferInstance, fun g _ v _ => Submodule.mem_top, fun S' _ _ => eq_bot_or_eq_top S',
        ⟨(1 : ℂ), Submodule.mem_top, one_ne_zero, fun θ _ => by simp [famOne]⟩, ?_⟩
      intro μ v hμ _ _ _
      rw [eq_zero_of_sum_fin_one μ hμ]
      exact above_self _ _
    refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun a _ b _ => by ext; simp [famOne]⟩,
      fun g _ v => by simp [famOne], fun v => continuousOn_const⟩, fun S _ _ => eq_bot_or_eq_top S, ?_⟩, ?_, ?_, ?_⟩
    · intro μ hμ v w
      haveI := hμ
      exact (continuous_const : Continuous fun _ : SUJ ε => ⟪w, v⟫_ℂ).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · intro v w _ _
      refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => ⟪w, v⟫_ℂ, isOpen_univ, trivial, contDiffOn_const,
        fun g _ _ => by simp [famOne]⟩, ?_⟩
      intro m g _
      rw [gelfVal_fin_one_zero, zero_mul]
      simp [gelfS, EwordS, cycWord, List.ofFn_succ, E0_fin_one, Ec_zero_fin_one]
    · refine ⟨⊤, hK, fun S hS => ?_⟩
      obtain ⟨v, hvS, hv0, _⟩ := hS.2.2.2.2.1
      rcases eq_bot_or_eq_top S with h | h
      · rw [h, Submodule.mem_bot] at hvS; exact absurd hvS hv0
      · exact h
    · intro μ S hS
      rw [eq_zero_of_sum_fin_one μ hS.1, lowCh_fin_one_zero]
      exact above_self _ _
  · intro lam lam' h h'
    obtain rfl := hpar lam h
    obtain rfl := hpar lam' h'
    exact ⟨fun _ => ⟨Equiv.refl _, fun _ => rfl, rfl⟩, fun _ => ⟨LinearIsometryEquiv.refl ℂ ℂ, fun _ _ _ => rfl⟩⟩
  · intro H' _ _ σ hσ
    obtain ⟨_, hnt, hu, hirr, _⟩ := hσ
    have h1 : ∀ g ∈ SUset ε, σ g = 1 := fun g hg => by rw [hSU g hg]; exact hu.1.1
    obtain ⟨T⟩ := exists_iso_of_irred (fun S hS => hirr S hS (fun g hg v hv => by rw [h1 g hg]; exact hv))
    refine ⟨0, hpar0, T, fun g hg v => ?_⟩
    rw [h1 g hg]
    simp [famOne]

theorem classU_zero : ClassU 0 := by
  refine ⟨fun _ _ => ℂ, fun _ _ => inferInstance, fun _ _ => inferInstance, fun _ _ _ => 1, ?_, ?_⟩
  · intro ε lam _
    have hK : ∀ μ : Fin 0 → ℝ, IsKTypeOf ε (fun _ => (1 : ℂ →L[ℂ] ℂ)) μ ⊤ := by
      intro μ
      exact ⟨inferInstance, fun g _ v _ => Submodule.mem_top, fun S' _ _ => eq_bot_or_eq_top S',
        ⟨(1 : ℂ), Submodule.mem_top, one_ne_zero, fun θ _ => by simp⟩,
        fun μ' v _ _ _ => ⟨0, by simp, Subsingleton.elim _ _⟩⟩
    refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun a _ b _ => by ext; simp⟩,
      fun g _ v => by simp, fun v => continuousOn_const⟩, fun S _ _ => eq_bot_or_eq_top S, ?_⟩, ?_, ?_, ?_⟩
    · intro v w
      exact continuous_const.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro v w _ _
      refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => ⟪w, v⟫_ℂ, isOpen_univ, trivial, contDiffOn_const,
        fun g _ _ => by simp⟩, ?_⟩
      intro m g _
      simp [gelf, gelfVal]
    · refine ⟨⊤, hK _, fun S hS => ?_⟩
      obtain ⟨v, hvS, hv0, _⟩ := hS.2.2.2.1
      rcases eq_bot_or_eq_top S with h | h
      · rw [h, Submodule.mem_bot] at hvS; exact absurd hvS hv0
      · exact h
    · intro μ S _
      exact ⟨0, by simp, Subsingleton.elim _ _⟩
  · intro ε H' _ _ σ hσ
    obtain ⟨_, hnt, hu, hirr, _⟩ := hσ
    have h1 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, σ g = 1 := fun g => by
      rw [Subsingleton.elim g 1]; exact hu.1.1
    obtain ⟨T⟩ := exists_iso_of_irred (fun S hS => hirr S hS (fun g _ v hv => by rw [h1 g]; exact hv))
    refine ⟨1, 0, ⟨fun a => a.elim0, fun a => a.elim0⟩, fun a => a.elim0, T, fun g _ v => ?_⟩
    simp [h1]

theorem classS_one_classU_zero : (∀ ε : Fin 1 → Bool, ClassS ε) ∧ ClassU 0 :=
  ⟨classS_one, classU_zero⟩

end GlobalTheory.DSSU.Triv
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_rank_one : (∀ ε : Fin 1 → Bool, ClassS ε) ∧ ClassU 0 := by
  atlas_forward_decl GlobalTheory.DSSU.Triv.classS_one_classU_zero
end

section
open GlobalTheory.DSSU

namespace GlobalTheory.DSSU.FromSU

theorem classS_of_discreteSeriesSU (h : GlobalTheory.Published.DiscreteSeriesSU) (n : ℕ) (hn : 1 ≤ n) (ε : Fin n → Bool) : ClassS ε := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    exact GlobalTheory.T.classification_rank_one.1 ε
  · exact (GlobalTheory.Published.discreteSeriesSU_iff.mp h) n h2 ε

theorem discreteSeriesClassification_of_SU :
    GlobalTheory.Published.DiscreteSeriesSU → GlobalTheory.Published.DiscreteSeriesClassification := by
  intro h
  rw [GlobalTheory.Published.discreteSeriesClassification_iff, dsClass_iff]
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.T.classification_rank_one.2
  · exact GlobalTheory.T.classification_unitary_of_full n (fun ε => GlobalTheory.T.classification_of_special_unitary n hn ε (classS_of_discreteSeriesSU h n hn ε))

end GlobalTheory.DSSU.FromSU
end
