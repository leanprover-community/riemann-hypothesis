import Mathlib
import Formalism.UnipotentAdelicQuotients.SmComplete
import BuildAid.ForwardExisting
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm

section
section
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.SmTangent

section Abstract

variable {A : Type*} [NormedRing A]

theorem norm_pow_le_pow_of_le (h1 : ‖(1 : A)‖ ≤ 1) {b : A} {C : ℝ} (hC : 1 ≤ C) (hb : ‖b‖ ≤ C) (k : ℕ) :
    ‖b ^ k‖ ≤ C ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖b ^ k * b‖ ≤ ‖b ^ k‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ C ^ k * C := by
        gcongr

theorem norm_pow_sub_pow_le (h1 : ‖(1 : A)‖ ≤ 1) {a b : A} {C : ℝ} (hC : 1 ≤ C) (ha : ‖a‖ ≤ C)
    (hb : ‖b‖ ≤ C) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ k * C ^ k * ‖a - b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hC0 : 0 ≤ C := by linarith
    have hCk : 1 ≤ C ^ k := one_le_pow₀ hC
    have hd : 0 ≤ ‖a - b‖ := norm_nonneg _
    have t1 : ‖a * (a ^ k - b ^ k)‖ ≤ C * (k * C ^ k * ‖a - b‖) :=
      (norm_mul_le _ _).trans (by gcongr)
    have t2 : ‖(a - b) * b ^ k‖ ≤ ‖a - b‖ * C ^ k :=
      (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le_pow_of_le h1 hC hb k)
    have t3 : ‖a - b‖ * C ^ k ≤ ‖a - b‖ * C ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (Nat.le_succ k)) hd
    rw [e]
    calc ‖a * (a ^ k - b ^ k) + (a - b) * b ^ k‖
        ≤ ‖a * (a ^ k - b ^ k)‖ + ‖(a - b) * b ^ k‖ := norm_add_le _ _
      _ ≤ C * (k * C ^ k * ‖a - b‖) + ‖a - b‖ * C ^ (k + 1) := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * C ^ (k + 1) * ‖a - b‖ := by
        push_cast; ring

variable [NormedAlgebra ℝ A] [CompleteSpace A]

theorem tendsto_pow_of_hasDerivAt (h1 : ‖(1 : A)‖ ≤ 1) (γ : ℝ → A) (Y : A) (h0 : γ 0 = 1)
    (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp (t • Y))) := by
  set E : ℝ → A := fun s => NormedSpace.exp (s • Y) with hE
  have hE0 : E 0 = 1 := by simp [hE]
  have hEd : HasDerivAt E Y 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
    simpa using this
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  obtain ⟨M1, hM1⟩ := hd.isBigO_sub.bound
  obtain ⟨M2, hM2⟩ := hEd.isBigO_sub.bound
  set M : ℝ := max (max M1 M2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  set c : ℝ := M * |t| with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ (f : ℝ → A) (M' : ℝ), M' ≤ M → f 0 = 1 →
      (∀ᶠ s in 𝓝 (0 : ℝ), ‖f s - f 0‖ ≤ M' * ‖s - 0‖) →
      ∀ᶠ k : ℕ in atTop, ‖f (t / k)‖ ≤ 1 + c / k := by
    intro f M' hM' hf hb
    filter_upwards [hs.eventually hb, eventually_gt_atTop 0] with k hk hk0
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [hf] at hk
    have e : f (t / k) = 1 + (f (t / k) - 1) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add h1 (hk.trans ?_))
    have : ‖t / (k : ℝ) - 0‖ = |t| / k := by
      simp [abs_div]
    rw [this, hc, mul_div_assoc]
    gcongr
  have ha := hbound γ M1 ((le_max_left _ _).trans (le_max_left _ _)) h0 hM1
  have hb := hbound E M2 ((le_max_right _ _).trans (le_max_left _ _)) hE0 hM2
  have hpow : ∀ k : ℕ, 0 < k → (1 + c / k) ^ k ≤ Real.exp c := by
    intro k hk
    have hk' : (k : ℝ) ≠ 0 := by positivity
    calc (1 + c / k) ^ k ≤ (Real.exp (c / k)) ^ k := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp c := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hD : HasDerivAt (fun s => γ s - E s) 0 0 := by
    have := hd.sub hEd
    rw [sub_self] at this
    exact this
  have hlo : (fun s => γ s - E s) =o[𝓝 0] (fun s : ℝ => s) := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hD
    simpa [h0, hE0] using this
  have hK : Tendsto (fun k : ℕ => Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (k : ℝ) * ‖γ (t / k) - E (t / k)‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hp : 0 < |t| + 1 := by positivity
      have hcε : 0 < ε / (|t| + 1) := by positivity
      filter_upwards [(hlo.comp_tendsto hs).def hcε, eventually_gt_atTop 0] with k hk hk0
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
      simp only [Function.comp] at hk
      have e : ‖t / (k : ℝ)‖ = |t| / k := by simp [abs_div]
      rw [e] at hk
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      calc (k : ℝ) * ‖γ (t / k) - E (t / k)‖ ≤ k * (ε / (|t| + 1) * (|t| / k)) := by gcongr
        _ = ε * (|t| / (|t| + 1)) := by field_simp
        _ < ε * 1 := by
          gcongr
          rw [div_lt_one hp]
          linarith
        _ = ε := mul_one _
    simpa using this.const_mul (Real.exp c)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [ha, hb, eventually_gt_atTop 0] with k hak hbk hk0
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hC : 1 ≤ 1 + c / k := by
    have : 0 ≤ c / k := by positivity
    linarith
  have hEk : NormedSpace.exp (t • Y) = E (t / k) ^ k := by
    simp only [hE]
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  rw [hEk]
  refine (norm_pow_sub_pow_le h1 hC hak hbk k).trans ?_
  have := hpow k hk0
  have hn : 0 ≤ ‖γ (t / k) - E (t / k)‖ := norm_nonneg _
  calc (k : ℝ) * (1 + c / k) ^ k * ‖γ (t / k) - E (t / k)‖
      ≤ k * Real.exp c * ‖γ (t / k) - E (t / k)‖ := by gcongr
    _ = Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖) := by ring

end Abstract

theorem matrix_tendsto (n : ℕ) (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : γ 0 = 1) (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp ((t : ℂ) • Y))) := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  letI R : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI Al : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hd' : HasDerivAt γ Y 0 := hasDerivAt_iff_tendsto_slope.2 hs
  have key := @tendsto_pow_of_hasDerivAt _ R Al this h1 γ Y h0 hd' t
  have e : (t : ℂ) • Y = t • Y := by
    ext i j
    simp
  rw [e]
  exact key

theorem tangent_mem_lieAlg : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
    ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  intro n G hG γ Y h0 hev hd t
  obtain ⟨hcl, h1G, hmul, -⟩ := hG
  have hpowG : ∀ g ∈ G, ∀ k : ℕ, g ^ k ∈ G := by
    intro g hg k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hg
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  refine hcl.mem_of_tendsto (matrix_tendsto n γ Y h0 hd t) ?_
  filter_upwards [hs.eventually hev] with k hk
  exact hpowG _ hk k

end GlobalTheory.CompanionTheory.SmTangent
end

open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_of_tangent_curve : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G → ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg
end

section
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.MatrixLie

theorem hasDerivAt_exp_mul_exp_of_finiteDimensional {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y)) (X + Y) 0 := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  have hX := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hY := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  have hXY := hX.mul hY
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hXY
  exact hXY

private theorem hasDerivAt_zero_linear_exp_smul_mul_exp_smul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) (ℓ : A →ₗ[ℝ] ℂ) :
    HasDerivAt (fun t : ℝ => ℓ (NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))) (ℓ (X + Y)) 0 :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_mul_exp_of_finiteDimensional X Y)

theorem entry_hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y)) i j) ((X + Y) i j) 0 := by
  have hs : ∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t : ℂ) • Z) = t • Z := by
    intro t Z
    ext a b
    simp [Complex.real_smul]
  simp only [hs]
  exact @hasDerivAt_zero_linear_exp_smul_mul_exp_smul (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra inferInstance X Y
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_exp_mul_exp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y))
      (X + Y) 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => entry_hasDerivAt_exp_mul_exp X Y i j

theorem exists_submodule_eq_lieAlg :
    ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
      ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
        (S : Set (Matrix (Fin n) (Fin n) ℂ)) = lieAlg G := by
  intro n G hG
  refine ⟨{ carrier := lieAlg G, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    have ha' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • a) ∈ G := ha
    have hb' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • b) ∈ G := hb
    refine GlobalTheory.T.lie_algebra_of_tangent_curve n G hG
      (fun t : ℝ => NormedSpace.exp ((t : ℂ) • a) * NormedSpace.exp ((t : ℂ) • b)) (a + b) ?_ ?_
      (hasDerivAt_exp_mul_exp a b)
    · simp
    · exact Filter.Eventually.of_forall (fun t => hG.2.2.1 _ (ha' t) _ (hb' t))
  · show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ G
    intro t
    simpa using hG.2.1
  · intro c X hX
    have hX' : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G := hX
    show ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (c • X)) ∈ G
    intro t
    have he : ((t : ℂ) • (c • X)) = ((t * c : ℝ) : ℂ) • X := by
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [he]
    exact hX' (t * c)

end GlobalTheory.CompanionTheory.MatrixLie
end
end

section
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SmoothLog


def OpMat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

instance (n : ℕ) : NormedRing (OpMat n) := Matrix.linftyOpNormedRing
instance (n : ℕ) : NormedAlgebra ℝ (OpMat n) := Matrix.linftyOpNormedAlgebra
instance (n : ℕ) : FiniteDimensional ℝ (OpMat n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
instance (n : ℕ) : CompleteSpace (OpMat n) := FiniteDimensional.complete ℝ _

def toOp (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] OpMat n :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ))


end GlobalTheory.CompanionTheory.SmoothLog
end
end

section
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem pow_mem_of_mul_closed {G : Set A} (h1 : (1 : A) ∈ G) (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {g : A} (hg : g ∈ G) (m : ℕ) : g ^ m ∈ G := by
  induction m with
  | zero => simpa using h1
  | succ m ih => rw [pow_succ]; exact hmul _ ih _ hg

theorem exp_neg_mem {G : Set A} (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1) {x : A}
    (hx : NormedSpace.exp x ∈ G) : NormedSpace.exp (-x) ∈ G := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨h, hh, hhg, -⟩ := hinv _ hx
  have hone : NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl x)), add_neg_cancel,
      NormedSpace.exp_zero]
  have heq : h = NormedSpace.exp (-x) := by
    calc h = h * (NormedSpace.exp x * NormedSpace.exp (-x)) := by rw [hone, mul_one]
      _ = NormedSpace.exp (-x) := by rw [← mul_assoc, hhg, one_mul]
  exact heq ▸ hh

theorem exp_smul_limit_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) {ε : ℕ → ℝ} {a : ℕ → A} {Y : A}
    (hε0 : ∀ k, 0 < ε k) (hε : Tendsto ε atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 Y))
    (hG : ∀ k, NormedSpace.exp (ε k • a k) ∈ G) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp (t • Y) ∈ G := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hm : Tendsto (fun k => (⌊t / ε k⌋₊ : ℝ) * ε k) atTop (𝓝 t) := by
    have hlo : ∀ k, t - ε k ≤ (⌊t / ε k⌋₊ : ℝ) * ε k := by
      intro k
      have h3 := Nat.lt_floor_add_one (t / ε k)
      have h2 : t / ε k * ε k = t := div_mul_cancel₀ _ (hε0 k).ne'
      nlinarith [hε0 k]
    have hhi : ∀ k, (⌊t / ε k⌋₊ : ℝ) * ε k ≤ t := by
      intro k
      have h3 := Nat.floor_le (div_nonneg ht (hε0 k).le)
      have h2 : t / ε k * ε k = t := div_mul_cancel₀ _ (hε0 k).ne'
      nlinarith [hε0 k]
    have hl : Tendsto (fun k => t - ε k) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hhi
  have hlim : Tendsto (fun k => NormedSpace.exp (((⌊t / ε k⌋₊ : ℝ) * ε k) • a k)) atTop
      (𝓝 (NormedSpace.exp (t • Y))) :=
    (NormedSpace.exp_continuous.tendsto _).comp (hm.smul ha)
  refine hc.mem_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  have hk : ((⌊t / ε k⌋₊ : ℝ) * ε k) • a k = ⌊t / ε k⌋₊ • (ε k • a k) := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  rw [hk, NormedSpace.exp_nsmul]
  exact pow_mem_of_mul_closed h1 hmul (hG k) _

theorem exists_nhds_kernel_eq_zero {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (p : A →L[ℝ] A) (hp : ∀ Z ∈ S, p Z = Z) :
    ∃ W₀ ∈ 𝓝 (0 : A), ∀ Y ∈ W₀, NormedSpace.exp Y ∈ G → p Y = 0 → Y = 0 := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ Y : A, ‖Y‖ < 1 / ((k : ℝ) + 1) ∧ NormedSpace.exp Y ∈ G ∧ p Y = 0 ∧ Y ≠ 0 := by
    intro k
    obtain ⟨Y, hY, hYG, hYp, hY0⟩ :=
      hcon (Metric.ball 0 (1 / ((k : ℝ) + 1))) (Metric.ball_mem_nhds _ (by positivity))
    exact ⟨Y, by simpa using hY, hYG, hYp, hY0⟩
  choose Y hYn hYG hYp hY0 using hseq
  have hpos : ∀ k, 0 < ‖Y k‖ := fun k => norm_pos_iff.2 (hY0 k)
  have hsph : ∀ k, (‖Y k‖)⁻¹ • Y k ∈ Metric.sphere (0 : A) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos k).ne']
  haveI : ProperSpace A := FiniteDimensional.proper ℝ A
  obtain ⟨b, hb, φ, hφ, hlim⟩ := (isCompact_sphere (0 : A) 1).tendsto_subseq hsph
  have hε : Tendsto (fun k => ‖Y k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun k => (hYn k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hεφ : Tendsto (fun k => ‖Y (φ k)‖) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  have hmem : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • b) ∈ G := by
    intro t ht
    refine exp_smul_limit_mem hc h1 hmul (ε := fun k => ‖Y (φ k)‖)
      (a := fun k => (‖Y (φ k)‖)⁻¹ • Y (φ k)) (fun k => hpos _) hεφ hlim (fun k => ?_) ht
    have : ‖Y (φ k)‖ • (‖Y (φ k)‖)⁻¹ • Y (φ k) = Y (φ k) := by
      rw [smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]
    simpa only [this] using hYG (φ k)
  have hbS : b ∈ S := by
    refine (hS b).2 fun t => ?_
    rcases le_total 0 t with ht | ht
    · exact hmem t ht
    · have := exp_neg_mem hinv (hmem (-t) (by linarith))
      simpa using this
  have hpb : p b = 0 := by
    have h2 : Tendsto (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) atTop (𝓝 (p b)) :=
      (p.continuous.tendsto b).comp hlim
    have h3 : (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) = fun _ => 0 := by
      funext k
      rw [map_smul, hYp, smul_zero]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  have hb0 : b = 0 := by rw [← hp b hbS, hpb]
  have hb1 : ‖b‖ = 1 := mem_sphere_zero_iff_norm.1 hb
  rw [hb0, norm_zero] at hb1
  exact zero_ne_one hb1

theorem eventually_exp_of_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {W : Set A} (hW : W ∈ 𝓝 (0 : A)) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ S, X ∈ W ∧ NormedSpace.exp X = g := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨f, hf⟩ := S.subtype.exists_leftInverse_of_injective (by simp)
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap (S.subtype ∘ₗ f)
  have hpS : ∀ Z, p Z ∈ S := fun Z => (f Z).2
  have hp : ∀ Z ∈ S, p Z = Z := by
    intro Z hZ
    have h2 := LinearMap.congr_fun hf ⟨Z, hZ⟩
    have h3 : f Z = ⟨Z, hZ⟩ := h2
    change ((f Z : S) : A) = Z
    rw [h3]
  obtain ⟨W₀, hW₀, hker⟩ := exists_nhds_kernel_eq_zero hc h1 hmul hinv hS p hp
  let q : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p
  have hq : ∀ Z, q Z = Z - p Z := fun Z => rfl
  let Φ : A → A := fun Z => NormedSpace.exp (p Z) * NormedSpace.exp (q Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEp : HasStrictFDerivAt (fun Z => NormedSpace.exp (p Z)) p (0 : A) := by
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (p 0) := by
      simpa using hE
    exact (h2.comp (0 : A) p.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hEq : HasStrictFDerivAt (fun Z => NormedSpace.exp (q Z)) q (0 : A) := by
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (q 0) := by
      simpa using hE
    exact (h2.comp (0 : A) q.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := hEp.mul' hEq
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hq]
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : p ⁻¹' W ∩ q ⁻¹' W₀ ∈ 𝓝 (0 : A) := by
    refine inter_mem (p.continuous.continuousAt.preimage_mem_nhds ?_)
      (q.continuous.continuousAt.preimage_mem_nhds ?_)
    · simpa using hW
    · simpa using hW₀
  have himg : Φ '' (p ⁻¹' W ∩ q ⁻¹' W₀) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  filter_upwards [himg]
  rintro g ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩ hg
  have hpG : NormedSpace.exp (p Z) ∈ G := by
    simpa using (hS _).1 (hpS Z) 1
  have hnG : NormedSpace.exp (-(p Z)) ∈ G := exp_neg_mem hinv hpG
  have hone : NormedSpace.exp (-(p Z)) * NormedSpace.exp (p Z) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl (p Z))), neg_add_cancel,
      NormedSpace.exp_zero]
  have hqG : NormedSpace.exp (q Z) ∈ G := by
    have h2 := hmul _ hnG _ hg
    simpa only [Φ, ← mul_assoc, hone, one_mul] using h2
  have hpq : p (q Z) = 0 := by
    rw [hq, map_sub, hp _ (hpS Z), sub_self]
  have hq0 : q Z = 0 := hker _ hZ2 hqG hpq
  refine ⟨p Z, hpS Z, hZ1, ?_⟩
  simp [Φ, hq0]

end Banach

end GlobalTheory.CompanionTheory.ClosedSubgroup
end
end
