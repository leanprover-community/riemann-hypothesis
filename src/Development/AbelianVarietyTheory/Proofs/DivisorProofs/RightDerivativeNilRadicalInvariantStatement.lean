import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad

section
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section
namespace GlobalTheory.TorFin.NilAdj

theorem exists_smul_of_ker {n : ℕ} (ψ φ : Fin n → ℂ) (h : ∀ w, φ ⬝ᵥ w = 0 → ψ ⬝ᵥ w = 0) :
    ∃ b : ℂ, ψ = b • φ := by
  classical
  by_cases hφ : φ = 0
  · refine ⟨0, ?_⟩
    funext i
    have := h (Pi.single i 1) (by simp [hφ])
    simpa using this
  · obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hφ (funext hc)
    refine ⟨ψ ⬝ᵥ Pi.single i (φ i)⁻¹, ?_⟩
    funext j
    have hw := h (Pi.single j 1 - φ j • Pi.single i (φ i)⁻¹) (by
      simp [dotProduct_sub, dotProduct_smul, hi])
    simp [dotProduct_sub, dotProduct_smul] at hw
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct_single] at hw ⊢
    linear_combination hw

theorem cube_eq_zero {n : ℕ} {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} (hY : Y ∈ nilRad J x) :
    Y * Y * Y = 0 := by
  obtain ⟨h1, h2, h3⟩ := hY
  apply Matrix.mulVec_injective
  funext v
  have hv : (star x ᵥ* J) ⬝ᵥ (Y *ᵥ v) = 0 := by rw [dotProduct_mulVec, h2, zero_dotProduct]
  obtain ⟨a, ha⟩ := h3 _ hv
  rw [← mulVec_mulVec, ← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_mulVec]

theorem sq_mem {n : ℕ} {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} (hY : Y ∈ nilRad J x) :
    Y * Y ∈ nilRad J x := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨by rw [← mulVec_mulVec, h1, mulVec_zero], by rw [← vecMul_vecMul, h2, zero_vecMul], fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := h3 v hv
  exact ⟨0, by rw [← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_smul]⟩

theorem adj_mem {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det) {x : Fin n → ℂ}
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ nilRad J x) : J⁻¹ * Yᴴ * J ∈ nilRad J x := by
  obtain ⟨h1, h2, h3⟩ := hY
  have hsφ : star (star x ᵥ* J) = J *ᵥ x := by rw [star_vecMul, star_star, hJ]
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← hsφ, ← star_vecMul, h2, star_zero, mulVec_zero]
  · rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_vecMul (star x) J, mul_nonsing_inv J hdet, vecMul_one,
      ← star_mulVec, h1, star_zero, zero_vecMul]
  · have hker : ∀ w, (star x ᵥ* J) ⬝ᵥ w = 0 → (star (J *ᵥ v) ᵥ* Y) ⬝ᵥ w = 0 := by
      intro w hw
      obtain ⟨a, ha⟩ := h3 w hw
      rw [← dotProduct_mulVec, ha, dotProduct_smul]
      have : star (J *ᵥ v) ⬝ᵥ x = 0 := by
        have e := star_dotProduct_star (star x) (J *ᵥ v)
        rw [star_star] at e
        rw [dotProduct_comm, e, dotProduct_comm, dotProduct_mulVec, hv, star_zero]
      rw [this, smul_zero]
    obtain ⟨b, hb⟩ := exists_smul_of_ker _ _ hker
    refine ⟨star b, ?_⟩
    have e : Yᴴ *ᵥ (J *ᵥ v) = star b • (J *ᵥ x) := by
      have := congrArg star hb
      rw [star_vecMul, star_star, star_smul, hsφ] at this
      exact this
    rw [← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_smul, mulVec_mulVec, nonsing_inv_mul J hdet, one_mulVec]

theorem exp_sub_one_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y * Y * Y = 0) :
    NormedSpace.exp Y - 1 = Y + (1 / 2 : ℂ) • (Y * Y) := by
  have h3 : ∀ k, 3 ≤ k → Y ^ k = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, pow_three, ← mul_assoc, h, zero_mul]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, pow_two]
    abel
  · intro k hk
    simp at hk
    rw [h3 k hk, smul_zero]

theorem nilRad_adj_exp : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  intro n J hJ hdet x Y hY
  refine ⟨adj_mem hJ hdet hY, ?_⟩
  rw [exp_sub_one_eq (cube_eq_zero hY)]
  exact (nilRad J x).add_mem hY ((nilRad J x).smul_mem _ (sq_mem hY))

end GlobalTheory.TorFin.NilAdj
end
end

open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_adjoint_exp_stable : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  atlas_forward_decl GlobalTheory.TorFin.NilAdj.nilRad_adj_exp
end

section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section

namespace GlobalTheory.TorFinKill

variable {n : ℕ} {G : Type} [Group G]

theorem isUni_exp {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : IsSkew J X) :
    IsUni J (NormedSpace.exp X) := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  unfold IsUni
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isSkew_real_smul {J Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) : IsSkew J (t • Z) := by
  unfold IsSkew at *
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]

theorem map_one_of_isMulOn {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s) :
    s 1 = 1 := by
  have h1 : IsUni J 1 := by simp [IsUni]
  have := hs 1 1 h1 h1
  rw [one_mul] at this
  exact mul_eq_left.mp this.symm

theorem lineOf_zero {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  simp [lineOf, map_one_of_isMulOn hs]

theorem rho_apply_eq_deriv {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (f : smLoc J s) (g : G) :
    (ρ Z f).1 g = deriv (fun τ : ℝ => f.1 (g * lineOf s Z τ)) 0 := by
  have h := hρ Z hZ f g 0
  rw [lineOf_zero hs, mul_one] at h
  exact h.deriv.symm

theorem decomp {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsSkew J ((1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J)) ∧ IsSkew J ((-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J)) ∧
      Y = (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) + Complex.I • ((-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J)) := by
  have hA : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hJh,
      mul_assoc, mul_assoc, nonsing_inv_mul _ hJ, mul_one]
  have hB : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J := by
    rw [← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hJ, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold IsSkew
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_sub, sub_mul, mul_sub, hA, hB]
    have : star (1/2 : ℂ) = 1/2 := by simp
    rw [this]
    module
  · unfold IsSkew
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, conjTranspose_add, add_mul, mul_add, hA, hB]
    have : star (-Complex.I/2 : ℂ) = Complex.I/2 := by simp
    rw [this]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I/2) = 1/2 by linear_combination (-1/2 : ℂ) * Complex.I_sq]
    module

end GlobalTheory.TorFinKill

namespace GlobalTheory.TorFinKill

variable {n : ℕ} {G : Type} [Group G]

def IsLeftInv {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (N : Subgroup G) (f : smLoc J s) : Prop :=
  ∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g

theorem isLeftInv_rho_skew {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) {f : smLoc J s} (hf : IsLeftInv N f) : IsLeftInv N (ρ Z f) := by
  intro ν hν g
  rw [rho_apply_eq_deriv hs hρ hZ, rho_apply_eq_deriv hs hρ hZ]
  congr 1
  funext τ
  rw [mul_assoc, hf ν hν]

theorem rho_apply_add_I {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) {Y : Matrix (Fin n) (Fin n) ℂ}
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) ℂ) (hY : Y = Z₁ + Complex.I • Z₂) (f : smLoc J s) (g : G) :
    (ρ Y f).1 g = (ρ Z₁ f).1 g + Complex.I * (ρ Z₂ f).1 g := by
  subst hY
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem isLeftInv_rho {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    (Y : Matrix (Fin n) (Fin n) ℂ) {f : smLoc J s} (hf : IsLeftInv N f) : IsLeftInv N (ρ Y f) := by
  obtain ⟨h1, h2, hY⟩ := decomp hJh hJ Y
  have e1 := isLeftInv_rho_skew hs hρ h1 hf
  have e2 := isLeftInv_rho_skew hs hρ h2 hf
  intro ν hν g
  rw [rho_apply_add_I ρ _ _ hY, rho_apply_add_I ρ _ _ hY, e1 ν hν, e2 ν hν]

theorem isLeftInv_adjoin {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {N : Subgroup G}
    {w : Module.End ℂ (smLoc J s)} (hw : w ∈ Algebra.adjoin ℂ (Set.range ρ)) :
    ∀ f : smLoc J s, IsLeftInv N f → IsLeftInv N (w f) := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨Y, rfl⟩ := hx
    exact fun f hf => isLeftInv_rho hJh hJ hs hρ Y hf
  | algebraMap r =>
    intro f hf ν hν g
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hf ν hν]
  | add a b _ _ ha hb =>
    intro f hf ν hν g
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [ha f hf ν hν, hb f hf ν hν]
  | mul a b _ _ ha hb =>
    intro f hf
    exact ha _ (hb f hf)

theorem rho_kill_skew {J : Matrix (Fin n) (Fin n) ℂ} (hJh : Jᴴ = J) (hJ : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s)
    {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)} (hρ : IsRightDer J s ρ) {x : Fin n → ℂ}
    {N : Subgroup G} (hN : ∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (hZn : Z ∈ nilRad J x) {f : smLoc J s} (hf : IsLeftInv N f) :
    (ρ Z f).1 1 = 0 := by
  rw [rho_apply_eq_deriv hs hρ hZ]
  have hc : (fun τ : ℝ => f.1 (1 * lineOf s Z τ)) = fun _ => f.1 1 := by
    funext τ
    have hmem : lineOf s Z τ ∈ N := by
      refine hN _ (isUni_exp hJ (isSkew_real_smul hZ τ)) ?_
      exact (GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x _ (Submodule.smul_of_tower_mem _ τ hZn)).2
    rw [one_mul, ← mul_one (lineOf s Z τ), hf _ hmem]
  rw [hc, deriv_const]

end GlobalTheory.TorFinKill

namespace GlobalTheory.TorFin

theorem leftIdl_apply_one_eq_zero : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (x : Fin n → ℂ) (N : Subgroup G), (∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N) → ∀ f : smLoc J s, (∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g) → ∀ T ∈ leftIdl ρ (nilRad J x : Set (Matrix (Fin n) (Fin n) ℂ)), (T f).1 1 = 0 := by
  intro n G _ J s hJh hJ hs ρ hρ x N hN f hf T hT
  induction hT using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    have hwf : GlobalTheory.TorFinKill.IsLeftInv N (w f) := GlobalTheory.TorFinKill.isLeftInv_adjoin hJh hJ hs hρ hw f hf
    obtain ⟨h1, h2, hYe⟩ := GlobalTheory.TorFinKill.decomp hJh hJ Y
    have hs' := (GlobalTheory.T.nilradical_adjoint_exp_stable n J hJh hJ x Y hY).1
    have m1 : (1/2 : ℂ) • (Y - J⁻¹ * Yᴴ * J) ∈ nilRad J x := Submodule.smul_mem _ _ (Submodule.sub_mem _ hY hs')
    have m2 : (-Complex.I/2) • (Y + J⁻¹ * Yᴴ * J) ∈ nilRad J x := Submodule.smul_mem _ _ (Submodule.add_mem _ hY hs')
    rw [Module.End.mul_apply, GlobalTheory.TorFinKill.rho_apply_add_I ρ _ _ hYe,
      GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h1 m1 hwf,
      GlobalTheory.TorFinKill.rho_kill_skew hJh hJ hs hρ hN h2 m2 hwf, mul_zero, add_zero]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

end GlobalTheory.TorFin
end
end

section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_nil_radical_invariant : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (x : Fin n → ℂ) (N : Subgroup G), (∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N) → ∀ f : smLoc J s, (∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g) → ∀ T ∈ leftIdl ρ (nilRad J x : Set (Matrix (Fin n) (Fin n) ℂ)), (T f).1 1 = 0 := by
  first | exact @GlobalTheory.TorFin.leftIdl_apply_one_eq_zero | exact GlobalTheory.TorFin.leftIdl_apply_one_eq_zero | (intros; apply GlobalTheory.TorFin.leftIdl_apply_one_eq_zero <;> assumption)
end
