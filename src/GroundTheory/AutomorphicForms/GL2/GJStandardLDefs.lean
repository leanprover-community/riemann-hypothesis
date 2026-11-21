import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalTheta
import GroundTheory.AutomorphicForms.GL2.GJStandardLUnramified
import GroundTheory.AutomorphicForms.GL2.GJLocalFEGamma
import GroundTheory.AutomorphicForms.GL2.GJFEInduced
import GroundTheory.AutomorphicForms.GL2.GJFELeviMulti
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.AutomorphicForms.RestrictedHaarProduct

section
open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem integrableOn_rpow_mul_ite {A B a b σ : ℝ} (ha : -σ < a) (hb : b < -σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * (if t < 1 then A * t ^ a else B * t ^ b)) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro ht
      by_cases h : t < 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (not_lt.1 h)
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => A * t ^ (σ - 1 + a)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)).const_mul A
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioo
    simp only [if_pos ht.2]
    rw [Real.rpow_add ht.1]
    ring
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h1 : IntegrableOn (fun t : ℝ => B * t ^ (σ - 1 + b)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff one_pos).2 (by linarith)).const_mul B
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : ¬ t < 1 := not_lt.2 (le_of_lt ht)
    simp only [if_neg ht']
    rw [Real.rpow_add (lt_trans one_pos ht)]
    ring

theorem tsum_norm_GL_le {Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (a b : Matrix (Fin n) (Fin n) 𝔸[K])
    (hs : Summable fun ξ : Matrix (Fin n) (Fin n) K => ‖Ψ (a * ratMat ξ * b)‖) :
    Summable (fun γ : GL (Fin n) K => ‖Ψ (a * ratMat (γ : Matrix (Fin n) (Fin n) K) * b)‖) ∧
      ∑' γ : GL (Fin n) K, ‖Ψ (a * ratMat (γ : Matrix (Fin n) (Fin n) K) * b)‖ ≤
        ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Ψ (a * ratMat ξ * b)‖ := by
  have hs' := hs.comp_injective (Units.val_injective (α := Matrix (Fin n) (Fin n) K))
  exact ⟨hs', Summable.tsum_le_tsum_of_inj _ Units.val_injective (fun _ _ => norm_nonneg _)
    (fun _ => le_rfl) hs' hs⟩

theorem tsum_norm_inv_eq (Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (t : {r : ℝ // 0 < r})
    (x y : AdelicGLn.AdelicGL K n) :
    ∑' γ : GL (Fin n) K, ‖Ψ (((centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ =
    ∑' γ : GL (Fin n) K, ‖Ψ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  congr 2
  simp only [Equiv.inv_apply]
  have e : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * y)⁻¹ =
      centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ * x := by
    rw [map_inv (AdelicGLn.diagonal K n)]
    have e1 : (centralSection K n t * x⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * y)⁻¹ =
        (y⁻¹ * AdelicGLn.diagonal K n γ * x) * (centralSection K n t)⁻¹ := by group
    rw [e1, ← map_inv, ← centralSection_mul_comm t⁻¹ (y⁻¹ * AdelicGLn.diagonal K n γ * x)]
    simp only [mul_assoc]
  rw [e, Units.val_mul, Units.val_mul, coe_diagonal]

theorem inv_centralSection_mul (t : {r : ℝ // 0 < r}) (x y : AdelicGLn.AdelicGL K n)
    (γ : GL (Fin n) K) :
    (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ =
      centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * x := by
  rw [map_inv (AdelicGLn.diagonal K n)]
  have e1 : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ =
      (y⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * x) * (centralSection K n t)⁻¹ := by group
  rw [e1, ← map_inv (centralSection K n) t,
    ← centralSection_mul_comm t⁻¹ (y⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * x)]
  simp only [mul_assoc]

theorem rpow_le_of_one_lt {s M : ℝ} (hs : 1 ≤ s) : s ^ M ≤ s ^ max M 0 :=
  Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)

theorem exists_bound_GL (hn0 : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n) (N : ℝ) :
    ∃ C M D : ℝ, ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      Summable (fun γ : GL (Fin n) K => ‖Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖) ∧
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ∑' γ : GL (Fin n) K, ‖Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
        (if (t : ℝ) < 1 then C * (t : ℝ) ^ (-max M 0) else D * (t : ℝ) ^ (-N)) := by
  obtain ⟨C₁, M₁, hC₁0, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨D, -, hD⟩ := exists_decay_tsum hn0 hΦ h₁ h₂ N
  refine ⟨C₁, M₁, D, fun t x y => ?_⟩
  obtain ⟨hs, hb⟩ := hC₁ x x.2 y y.2 t
  have hGL := tsum_norm_GL_le _ _ hs
  have e : ∀ γ : GL (Fin n) K, ‖Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
      AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K])‖ =
      ‖Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := fun γ => by
    rw [coe_mul_diagonal_mul]
  simp_rw [e]
  refine ⟨hGL.1, ?_⟩
  split_ifs with ht
  · have ht0 : (0 : ℝ) < t := t.2
    have h1 : 1 ≤ (t : ℝ)⁻¹ := (one_le_inv₀ ht0).2 ht.le
    have hmax : max 1 (t : ℝ)⁻¹ = (t : ℝ)⁻¹ := max_eq_right h1
    calc _ ≤ ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φ (((centralSection K n t *
            (x : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ :=
          mul_le_mul_of_nonneg_left hGL.2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ := hb
      _ ≤ C₁ * (t : ℝ) ^ (-max M₁ 0) := by
          rw [hmax, Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le]
          exact mul_le_mul_of_nonneg_left (rpow_le_of_one_lt h1) hC₁0
  · have := (hD x x.2 y y.2 t (not_lt.1 ht)).2
    simp_rw [e] at this
    exact this

theorem exists_bound_GL_inv (hn0 : 0 < n) {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n) (N : ℝ) :
    ∃ C M D : ℝ, ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      Summable (fun γ : GL (Fin n) K => ‖adelicMatrixFourier K Φ
        (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
          (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K])‖) ∧
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ∑' γ : GL (Fin n) K, ‖adelicMatrixFourier K Φ
          (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤
        (if (t : ℝ) < 1 then D * (t : ℝ) ^ N else C * (t : ℝ) ^ max M 0) := by
  have hΦh := adelicMatrixFourier_mem hΦ
  obtain ⟨C₂, M₂, hC₂0, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁
  obtain ⟨D, -, hD⟩ := exists_decay_tsum hn0 hΦh h₂ h₁ N
  refine ⟨C₂, M₂, D, fun t x y => ?_⟩
  set Φh := adelicMatrixFourier K Φ
  obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
  have hGL := tsum_norm_GL_le _ _ hs
  have e : ∀ γ : GL (Fin n) K, ‖Φh (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
      AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K])‖ =
      (fun δ : GL (Fin n) K => ‖Φh (((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
          ratMat (δ : Matrix (Fin n) (Fin n) K) *
            ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖) γ⁻¹ := fun γ => by
    simp only
    rw [inv_centralSection_mul, coe_mul_diagonal_mul]
  have hsum : Summable (fun γ : GL (Fin n) K => ‖Φh (((centralSection K n t *
      (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
        (y : AdelicGLn.AdelicGL K n))⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖) := by
    simp_rw [e]
    exact (Equiv.inv (GL (Fin n) K)).summable_iff.2 hGL.1
  refine ⟨hsum, ?_⟩
  rw [tsum_norm_inv_eq]
  have ht0 : (0 : ℝ) < t := t.2
  have hti : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := Positive.coe_inv t
  split_ifs with ht
  · have h1 : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
      rw [hti]
      exact (one_le_inv₀ ht0).2 ht.le
    have := (hD y y.2 x x.2 t⁻¹ h1).2
    have e2 : ∀ γ : GL (Fin n) K, ‖Φh ((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])‖ =
        ‖Φh (((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
            ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := fun γ => by
      rw [coe_mul_diagonal_mul]
    simp_rw [e2] at this
    rw [mul_comm ‖φ₂ _‖]
    calc _ ≤ D * ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) ^ (-N) := this
      _ = D * (t : ℝ) ^ N := by
          rw [hti, Real.inv_rpow ht0.le, Real.rpow_neg ht0.le, inv_inv]
  · have h1 : 1 ≤ (t : ℝ) := not_lt.1 ht
    rw [mul_comm ‖φ₂ _‖]
    calc _ ≤ ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φh (((centralSection K n t⁻¹ *
            (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ :=
          mul_le_mul_of_nonneg_left hGL.2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂ := hb
      _ ≤ C₂ * (t : ℝ) ^ max M₂ 0 := by
          rw [hti, inv_inv, max_eq_right h1]
          exact mul_le_mul_of_nonneg_left (rpow_le_of_one_lt h1) hC₂0

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

theorem norm_thetaPairing_le {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ} (t : {r : ℝ // 0 < r}) {b : ℝ}
    (hb : ∀ x y : normOneGL K n,
      Summable (fun γ : GL (Fin n) K => ‖Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖) ∧
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ∑' γ : GL (Fin n) K, ‖Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ b) :
    ‖thetaPairing μ φ₁ φ₂ Ξ t‖ ≤ (μ (fundamentalDomain Γ₁)).toReal ^ 2 * b := by
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  have hT : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K,
        Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ b := by
    intro x y
    obtain ⟨hs, hle⟩ := hb x y
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact le_trans (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hle
  unfold thetaPairing
  have hin : ∀ x : normOneGL K n, ‖∫ y in fundamentalDomain Γ₁,
      conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ‖ ≤
        b * (μ (fundamentalDomain Γ₁)).toReal := fun x =>
    norm_setIntegral_le_of_norm_le_const hF fun y _ => hT x y
  calc _ ≤ (b * (μ (fundamentalDomain Γ₁)).toReal) * (μ (fundamentalDomain Γ₁)).toReal :=
        norm_setIntegral_le_of_norm_le_const hF fun x _ => hin x
    _ = _ := by ring

end GJGlobal

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

variable {J J' : ℝ → ℂ}

theorem locallyIntegrableOn_indicator_Ici (hJ : ContinuousOn J (Ioi 0)) :
    LocallyIntegrableOn ((Ici (1 : ℝ)).indicator J) (Ioi 0) := by
  rw [locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]
  intro k hk hkc
  exact ((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ici

theorem locallyIntegrableOn_indicator_Ioi (hJ : ContinuousOn J (Ioi 0)) :
    LocallyIntegrableOn ((Ioi (1 : ℝ)).indicator J) (Ioi 0) := by
  rw [locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]
  intro k hk hkc
  exact ((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ioi

theorem isBigO_indicator_atTop {A : Set ℝ} (hA : A ∈ atTop) {a : ℝ}
    (h : J =O[atTop] (· ^ (-a))) : A.indicator J =O[atTop] (· ^ (-a)) := by
  refine EventuallyEq.trans_isBigO ?_ h
  filter_upwards [hA] with t ht
  exact indicator_of_mem ht J

theorem isBigO_indicator_nhdsGT {A : Set ℝ} (hA : A ⊆ Ici 1) (b : ℝ) :
    A.indicator J =O[𝓝[>] 0] (· ^ (-b)) := by
  refine EventuallyEq.trans_isBigO (f₂ := fun _ => (0 : ℂ)) ?_ (isBigO_zero _ _)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact indicator_of_notMem (fun h => absurd (hA h) (not_le.2 ht.2)) J

theorem differentiable_mellin_indicator {A : Set ℝ} (hA : A ⊆ Ici 1) (hAt : A ∈ atTop)
    (hloc : LocallyIntegrableOn (A.indicator J) (Ioi 0))
    (hd : ∀ a : ℝ, J =O[atTop] (· ^ (-a))) : Differentiable ℂ (mellin (A.indicator J)) := by
  intro w
  exact mellin_differentiableAt_of_isBigO_rpow hloc (isBigO_indicator_atTop hAt (hd (w.re + 1)))
    (lt_add_one _) (isBigO_indicator_nhdsGT hA (w.re - 1)) (sub_one_lt _)

theorem mellinConvergent_indicator {A : Set ℝ} (hA : MeasurableSet A) {w : ℂ}
    (hc : MellinConvergent J w) : MellinConvergent (A.indicator J) w := by
  have : (fun t : ℝ => (t : ℂ) ^ (w - 1) • A.indicator J t) =
      A.indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) := by
    funext t
    by_cases ht : t ∈ A <;> simp [ht]
  unfold MellinConvergent
  rw [this]
  exact hc.indicator hA

theorem mellin_eq_add_of_convergent {w : ℂ} (hc : MellinConvergent J w) :
    mellin J w = mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Iio (1 : ℝ)).indicator J) w := by
  have h1 := mellinConvergent_indicator (J := J) (A := Ici 1) measurableSet_Ici hc
  have h2 := mellinConvergent_indicator (J := J) (A := Iio 1) measurableSet_Iio hc
  unfold mellin
  rw [← integral_add h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← smul_add]
  congr 1
  have := Set.indicator_self_add_compl (Ici (1 : ℝ)) J
  rw [compl_Ici] at this
  exact (congrFun this t).symm

theorem mellin_indicator_Iio_eq {κ : ℝ} (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹)
    (w : ℂ) :
    mellin ((Iio (1 : ℝ)).indicator J) w = mellin ((Ioi (1 : ℝ)).indicator J') (κ - w) := by
  have e : mellin ((Iio (1 : ℝ)).indicator J) w =
      mellin (fun t : ℝ => (t : ℂ) ^ (-(κ : ℂ)) • (fun u : ℝ => (Ioi (1 : ℝ)).indicator J' u⁻¹) t) w := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [smul_eq_mul]
    congr 1
    by_cases h1 : t < 1
    · have : 1 < t⁻¹ := one_lt_inv₀ ht |>.2 h1
      rw [indicator_of_mem (show t ∈ Iio 1 from h1), indicator_of_mem (show t⁻¹ ∈ Ioi 1 from this),
        hsym t ht]
    · have : ¬ 1 < t⁻¹ := fun h => h1 ((one_lt_inv₀ ht).1 h)
      rw [indicator_of_notMem (show t ∉ Iio 1 from h1),
        indicator_of_notMem (show t⁻¹ ∉ Ioi 1 from this), mul_zero]
  rw [e, mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

theorem mellin_indicator_Ici_eq_Ioi (f : ℝ → ℂ) (w : ℂ) :
    mellin ((Ici (1 : ℝ)).indicator f) w = mellin ((Ioi (1 : ℝ)).indicator f) w := by
  unfold mellin
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  have h : ∀ᵐ t : ℝ, t ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h] with t ht _
  congr 1
  by_cases h1 : 1 < t
  · rw [indicator_of_mem (show t ∈ Ici 1 from h1.le), indicator_of_mem (show t ∈ Ioi 1 from h1)]
  · have h2 : ¬ 1 ≤ t := fun h => h1 (lt_of_le_of_ne h (Ne.symm ht))
    rw [indicator_of_notMem (show t ∉ Ici 1 from h2), indicator_of_notMem (show t ∉ Ioi 1 from h1)]

theorem symm_of_symm {κ : ℝ} (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹) :
    ∀ t : ℝ, 0 < t → J' t = (t : ℂ) ^ (-(κ : ℂ)) * J t⁻¹ := by
  intro t ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [hsym t⁻¹ (inv_pos.2 ht), inv_inv, ← mul_assoc, ofReal_inv, inv_cpow _ _ harg,
    mul_inv_cancel₀ (cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 ht.ne'))), one_mul]

theorem exists_entire_of_symm {κ : ℝ} (hJ : ContinuousOn J (Ioi 0)) (hJ' : ContinuousOn J' (Ioi 0))
    (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹)
    (hdJ : ∀ a : ℝ, J =O[atTop] (· ^ (-a))) (hdJ' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a))) :
    ∃ Λ Λ' : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ w, MellinConvergent J w → Λ w = mellin J w) ∧
      (∀ w, MellinConvergent J' w → Λ' w = mellin J' w) ∧ ∀ w, Λ w = Λ' (κ - w) := by
  have hsym' := symm_of_symm hsym
  have hIoi : Ioi (1 : ℝ) ∈ atTop := Ioi_mem_atTop 1
  have hIci : Ici (1 : ℝ) ∈ atTop := Ici_mem_atTop 1
  have d1 := differentiable_mellin_indicator (subset_refl _) hIci
    (locallyIntegrableOn_indicator_Ici hJ) hdJ
  have d2 := differentiable_mellin_indicator Ioi_subset_Ici_self hIoi
    (locallyIntegrableOn_indicator_Ioi hJ') hdJ'
  have d1' := differentiable_mellin_indicator (subset_refl _) hIci
    (locallyIntegrableOn_indicator_Ici hJ') hdJ'
  have d2' := differentiable_mellin_indicator Ioi_subset_Ici_self hIoi
    (locallyIntegrableOn_indicator_Ioi hJ) hdJ
  refine ⟨fun w => mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Ioi (1 : ℝ)).indicator J') (κ - w),
    fun w => mellin ((Ici (1 : ℝ)).indicator J') w + mellin ((Ioi (1 : ℝ)).indicator J) (κ - w),
    d1.add (d2.comp ((differentiable_const _).sub differentiable_id)),
    d1'.add (d2'.comp ((differentiable_const _).sub differentiable_id)), ?_, ?_, ?_⟩
  · intro w hc
    rw [mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym]
  · intro w hc
    rw [mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym']
  · intro w
    simp only [sub_sub_cancel]
    rw [add_comm, mellin_indicator_Ici_eq_Ioi J, mellin_indicator_Ici_eq_Ioi J']

end GJGlobal

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Set Filter NumberField ComplexConjugate Asymptotics
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem continuousOn_dite {f : {r : ℝ // 0 < r} → ℂ} (hf : Continuous f) :
    ContinuousOn (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Ioi (0 : ℝ)).domRestrict (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) =
      fun t : Ioi (0 : ℝ) => f ⟨t.1, t.2⟩ := by
    funext t
    rw [Set.domRestrict_apply, dif_pos (show (0 : ℝ) < t.1 from t.2)]
  rw [e]
  exact hf.comp (continuous_subtype_val.subtype_mk _)

theorem mellinConvergent_of_bound {J : ℝ → ℂ} (hJ : ContinuousOn J (Ioi 0)) {B : ℝ → ℝ} {V : ℝ}
    (hB : ∀ t : ℝ, 0 < t → ‖J t‖ ≤ V * B t) {w : ℂ}
    (hint : IntegrableOn (fun t : ℝ => t ^ (w.re - 1) * B t) (Ioi 0)) :
    MellinConvergent J w := by
  unfold MellinConvergent
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) (Ioi 0) := by
    refine ContinuousOn.smul (f := fun t : ℝ => (t : ℂ) ^ (w - 1)) (g := J) (fun t ht => ?_) hJ
    exact (Complex.continuousAt_ofReal_cpow_const t (w - 1)
      (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
  refine Integrable.mono' (hint.const_mul V) (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  calc t ^ (w.re - 1) * ‖J t‖ ≤ t ^ (w.re - 1) * (V * B t) :=
        mul_le_mul_of_nonneg_left (hB t ht) (Real.rpow_nonneg ht.le _)
    _ = V * (t ^ (w.re - 1) * B t) := by ring

theorem continuous_posInv : Continuous fun s : {r : ℝ // 0 < r} => s⁻¹ := by
  have h : Continuous fun s : {r : ℝ // 0 < r} => ((s : ℝ))⁻¹ :=
    continuous_subtype_val.inv₀ fun s => s.2.ne'
  exact h.subtype_mk _

theorem continuous_tsum_inv {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Φ (((centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  have hc := continuous_tsum_GL hΦ
  have hm : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      (p.1⁻¹, p.2.2⁻¹, p.2.1⁻¹) :=
    (continuous_posInv.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_snd).inv.prodMk (continuous_fst.comp continuous_snd).inv)
  have h := hc.comp hm
  refine h.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  have e := inv_centralSection_mul p.1 p.2.1⁻¹ p.2.2 γ
  rw [inv_inv] at e
  simp only [Equiv.inv_apply]
  rw [e]

set_option maxHeartbeats 1600000 in

theorem globalZeta_entire_functionalEquation (hn : 2 ≤ n) (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n)
    (hA : ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (centralSection K n s * x) = φ₁ x)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    ∃ σ₀ : ℝ, ∃ Λ Λ' : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand Φ (matrixCoeff μ φ₁ φ₂) s) ν ∧
        globalZeta ν Φ (matrixCoeff μ φ₁ φ₂) s = Λ s) ∧
      (∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand (adelicMatrixFourier K Φ)
          (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s) ν ∧
        globalZeta ν (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s = Λ' s) ∧
      ∀ s : ℂ, Λ s = Λ' (1 - s) := by
  have hn0 : 0 < n := by omega
  have hΦh := adelicMatrixFourier_mem hΦ
  have hΦc : Continuous Φ := continuous_of_mem_matrixSchwartzBruhat hΦ
  have hΦhc : Continuous (adelicMatrixFourier K Φ) := continuous_of_mem_matrixSchwartzBruhat hΦh
  have h₁c : Continuous φ₁ := h₁.1.continuous
  have h₂c : Continuous φ₂ := h₂.1.continuous
  set V : ℝ := (μ (fundamentalDomain (rationalGLOne K n))).toReal ^ 2 with hV

  set Ξ₁ : AdelicGLn.AdelicGL K n → ℂ := fun g => Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₁
  set Ξ₂ : AdelicGLn.AdelicGL K n → ℂ := fun g => adelicMatrixFourier K Φ
    ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₂
  have hΞ₁c : Continuous Ξ₁ := hΦc.comp Units.continuous_val
  have hΞ₂c : Continuous Ξ₂ := hΦhc.comp (Units.continuous_val.comp continuous_inv)
  set J₁ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₁ ⟨t, h⟩ else 0 with hJ₁
  set J₂ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₂ ⟨t, h⟩ else 0 with hJ₂
  set J' : ℝ → ℂ := fun u => J₂ u⁻¹ with hJ'

  obtain ⟨C₁, M₁, -, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨C₂, M₂, -, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁
  obtain ⟨_, _, _, hsum₂⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ 0
  have hB₁ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤
        C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ := by
    intro t x y
    obtain ⟨hs, hb⟩ := hC₁ x x.2 y y.2 t
    have hGL := tsum_norm_GL_le _ _ hs
    refine le_trans ?_ hb
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [hΞ₁, coe_mul_diagonal_mul]
    exact (norm_tsum_le_tsum_norm hGL.1).trans hGL.2
  have hB₂ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤
        C₂ * (max 1 (t : ℝ)) ^ M₂ := by
    intro t x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    have hGL := tsum_norm_GL_le _ _ hs
    have hsm := (hsum₂ t x y).1
    rw [mul_comm ‖φ₂ _‖]
    have e : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹ = (t : ℝ) := inv_inv (t : ℝ)
    rw [e] at hb
    refine le_trans ?_ hb
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (norm_tsum_le_tsum_norm hsm).trans ?_
    rw [tsum_norm_inv_eq]
    exact hGL.2
  have hB₁c : Continuous fun t : {r : ℝ // 0 < r} => C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ :=
    continuous_const.mul ((continuous_const.max (continuous_subtype_val.inv₀ fun t => t.2.ne')).rpow_const
      fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))
  have hB₂c : Continuous fun t : {r : ℝ // 0 < r} => C₂ * (max 1 (t : ℝ)) ^ M₂ :=
    continuous_const.mul ((continuous_const.max continuous_subtype_val).rpow_const
      fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))
  have hTP₁c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₁) :=
    continuous_thetaPairing μ h₁c h₂c (continuous_tsum_GL hΦ) hB₁c hB₁
  have hTP₂c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₂) :=
    continuous_thetaPairing μ h₁c h₂c (continuous_tsum_inv hΦh) hB₂c hB₂
  have hJ₁c : ContinuousOn J₁ (Ioi 0) := continuousOn_dite hTP₁c
  have hJ₂c : ContinuousOn J₂ (Ioi 0) := continuousOn_dite hTP₂c
  have hJ'c : ContinuousOn J' (Ioi 0) :=
    hJ₂c.comp (continuousOn_inv₀.mono fun t (ht : 0 < t) => ht.ne') fun t (ht : 0 < t) =>
      (show (0 : ℝ) < t⁻¹ from inv_pos.2 ht)

  have hsym : ∀ t : ℝ, 0 < t → J₁ t = (t : ℂ) ^ (-((n : ℝ) : ℂ)) * J' t⁻¹ := by
    intro t ht
    have hti : (0 : ℝ) < t⁻¹⁻¹ := by rw [inv_inv]; exact ht
    simp only [hJ₁, hJ', hJ₂, dif_pos ht, dif_pos hti]
    have e : (⟨t⁻¹⁻¹, hti⟩ : {r : ℝ // 0 < r}) = ⟨t, ht⟩ := Subtype.ext (inv_inv t)
    rw [e, thetaPairing_eq μ hn h₁ h₂ hΦ ⟨t, ht⟩]
    congr 1
    rw [Complex.ofReal_natCast, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rfl

  have hdec₁ : ∀ a : ℝ, J₁ =O[atTop] (· ^ (-a)) := by
    intro a
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL hn0 hΦ h₁ h₂ a
    refine IsBigO.of_bound (V * D) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    simp only [hJ₁, dif_pos ht0]
    have h := norm_thetaPairing_le μ (Ξ := Ξ₁) (φ₁ := φ₁) (φ₂ := φ₂) ⟨t, ht0⟩
      (b := D * t ^ (-a)) fun x y => by
        have := hb ⟨t, ht0⟩ x y
        rw [if_neg (not_lt.2 ht)] at this
        exact this
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc _ ≤ V * (D * t ^ (-a)) := h
      _ = V * D * t ^ (-a) := by ring
  have hdec' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a)) := by
    intro a
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ a
    refine IsBigO.of_bound (V * D) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    have hi0 : 0 < u⁻¹ := inv_pos.2 hu0
    have hi1 : u⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu
    simp only [hJ', hJ₂, dif_pos hi0]
    have h := norm_thetaPairing_le μ (Ξ := Ξ₂) (φ₁ := φ₁) (φ₂ := φ₂) ⟨u⁻¹, hi0⟩
      (b := D * (u⁻¹) ^ a) fun x y => by
        have := hb ⟨u⁻¹, hi0⟩ x y
        rw [if_pos hi1] at this
        exact this
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
    calc _ ≤ V * (D * (u⁻¹) ^ a) := h
      _ = V * D * u ^ (-a) := by rw [Real.inv_rpow hu0.le, Real.rpow_neg hu0.le]; ring
  obtain ⟨Λw, Λw', hΛ, hΛ', hΛeq, hΛ'eq, hfe⟩ :=
    exists_entire_of_symm (κ := (n : ℝ)) hJ₁c hJ'c hsym hdec₁ hdec'

  obtain ⟨c, -, hK⟩ := exists_integral_eq_mellin_thetaPairing μ hn0 ν
  obtain ⟨C₁', M₁', D₀, hb₁₀⟩ := exists_bound_GL hn0 hΦ h₁ h₂ 0
  obtain ⟨C₂', M₂', D₀', hb₂₀⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ 0
  set w₀ : ℂ := ((n : ℂ) - 1) / 2 with hw₀
  refine ⟨max (max M₁' 0) (max M₂' 0) - ((n : ℝ) - 1) / 2,
    fun s => (c : ℂ) * Λw (s + w₀), fun s => (c : ℂ) * Λw' (s + w₀),
    (hΛ.comp (differentiable_id.add_const _)).const_mul _,
    (hΛ'.comp (differentiable_id.add_const _)).const_mul _, ?_, ?_, ?_⟩
  ·
    intro s hs
    set σ : ℝ := (s + w₀).re with hσ
    have hσre : σ = s.re + ((n : ℝ) - 1) / 2 := by
      rw [hσ, Complex.add_re, hw₀]
      simp
    have hσM : max M₁' 0 < σ := by
      have := le_max_left (max M₁' 0) (max M₂' 0)
      linarith
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL hn0 hΦ h₁ h₂ (σ + 1)
    set B : ℝ → ℝ := fun t => if t < 1 then C₁' * t ^ (-max M₁' 0) else D * t ^ (-(σ + 1))
      with hBdef
    have hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
        Summable (fun γ : GL (Fin n) K => ‖Ξ₁ (centralSection K n t *
          (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))‖) ∧
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' γ : GL (Fin n) K, ‖Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t := by
      intro t x y
      refine ⟨(hb t x y).1, ?_⟩
      by_cases ht : (t : ℝ) < 1
      · have := (hb₁₀ t x y).2
        rw [if_pos ht] at this
        simp only [hBdef, if_pos ht]
        exact this
      · have := (hb t x y).2
        rw [if_neg ht] at this
        simp only [hBdef, if_neg ht]
        exact this
    have hint : IntegrableOn (fun t : ℝ => t ^ ((s + w₀).re - 1) * B t) (Ioi 0) :=
      integrableOn_rpow_mul_ite (by linarith) (by linarith)
    obtain ⟨hI, hEq⟩ := hK φ₁ φ₂ Ξ₁ (s + w₀) B h₁c h₂c hΞ₁c h₁.1.isLeftInvariant hA
      (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint
    refine ⟨hI, ?_⟩
    have hconv : MellinConvergent J₁ (s + w₀) := by
      refine mellinConvergent_of_bound hJ₁c (V := V) (fun t ht => ?_) hint
      simp only [hJ₁, dif_pos ht]
      exact norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y
    show ∫ g, Ξ₁ g * matrixCoeff μ φ₁ φ₂ g * detPow g (s + w₀) ∂ν = (c : ℂ) * Λw (s + w₀)
    rw [hEq]
    show (c : ℂ) * mellin J₁ (s + w₀) = (c : ℂ) * Λw (s + w₀)
    rw [hΛeq _ hconv]
  ·
    intro s hs
    set σ : ℝ := (s + w₀).re with hσ
    have hσre : σ = s.re + ((n : ℝ) - 1) / 2 := by
      rw [hσ, Complex.add_re, hw₀]
      simp
    have hσM : max M₂' 0 < σ := by
      have := le_max_right (max M₁' 0) (max M₂' 0)
      linarith
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ (σ + 1)
    set B : ℝ → ℝ := fun t => if t < 1 then D * t ^ (σ + 1) else C₂' * t ^ max M₂' 0
      with hBdef
    have hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
        Summable (fun γ : GL (Fin n) K => ‖Ξ₂ (centralSection K n t *
          (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))‖) ∧
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' γ : GL (Fin n) K, ‖Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t := by
      intro t x y
      refine ⟨(hb t x y).1, ?_⟩
      by_cases ht : (t : ℝ) < 1
      · have := (hb t x y).2
        rw [if_pos ht] at this
        simp only [hBdef, if_pos ht]
        exact this
      · have := (hb₂₀ t x y).2
        rw [if_neg ht] at this
        simp only [hBdef, if_neg ht]
        exact this
    have hint : IntegrableOn (fun t : ℝ => t ^ ((-(s + w₀)).re - 1) * B t) (Ioi 0) := by
      rw [Complex.neg_re]
      exact integrableOn_rpow_mul_ite (by linarith) (by linarith)
    obtain ⟨hI, hEq⟩ := hK φ₁ φ₂ Ξ₂ (-(s + w₀)) B h₁c h₂c hΞ₂c h₁.1.isLeftInvariant hA
      (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint
    have := isInvInvariant_haar ν hn0
    have hfun : zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s =
        fun g => (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))) g⁻¹ := by
      funext g
      simp only [zetaIntegrand, hΞ₂, inv_inv, detPow_inv, neg_neg, ← hw₀]
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hI.comp_inv
    · have hconv2 : MellinConvergent J₂ (-(s + w₀)) := by
        refine mellinConvergent_of_bound hJ₂c (V := V) (fun t ht => ?_) hint
        simp only [hJ₂, dif_pos ht]
        exact norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y
      have hconv : MellinConvergent J' (s + w₀) := by
        have h := (MellinConvergent.comp_rpow (f := J₂) (s := s + w₀) (a := -1)
          (by norm_num)).2 (by
            rw [show (s + w₀) / ((-1 : ℝ) : ℂ) = -(s + w₀) by push_cast; ring]
            exact hconv2)
        unfold MellinConvergent at h ⊢
        refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp only [hJ', Real.rpow_neg_one]
      show ∫ g, zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s g ∂ν =
        (c : ℂ) * Λw' (s + w₀)
      rw [hfun, integral_comp_inv ν hn0 (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))), hEq]
      show (c : ℂ) * mellin J₂ (-(s + w₀)) = (c : ℂ) * Λw' (s + w₀)
      rw [hΛ'eq _ hconv, hJ', mellin_comp_inv]
  · intro s
    simp only
    rw [hfe]
    congr 2
    rw [hw₀]
    push_cast
    ring

end GJGlobal

end

end GroundTheory.Automorphic
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure Parabolic
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

section Twist

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def nnrealCharC (χ : G →* ℝ≥0) : G →* ℂ :=
  (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom.comp χ

@[simp]
theorem nnrealCharC_apply (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g = ((χ g : ℝ) : ℂ) := rfl

theorem nnrealCharC_ne_zero (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g ≠ 0 := by
  rw [nnrealCharC_apply]
  have h := map_mul_eq_one χ (mul_inv_cancel g)
  exact_mod_cast (left_ne_zero_of_mul_eq_one h)

theorem exists_compact_open_char_eq_one (χ : G →* ℝ≥0) (hχ : Continuous χ) {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      ∀ k ∈ (K : Set G), χ k = 1 := by
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  exact ⟨K, hKc, hKU, fun k hk => eq_one_of_mem_compact χ hχ hKc hk⟩

variable (χ : G →* ℝ≥0) (hχ : Continuous χ) (ρ : Representation ℂ G W)
include hχ

theorem fixedVectors_twist {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    fixedVectors (twist (nnrealCharC χ) ρ) K = fixedVectors ρ K := by
  ext v
  simp only [mem_fixedVectors, twist_apply, nnrealCharC_apply]
  refine forall₂_congr fun k hk => ?_
  rw [eq_one_of_mem_compact χ hχ hKc hk]
  simp

theorem isSmooth_twist (hρ : IsSmooth ρ) : IsSmooth (twist (nnrealCharC χ) ρ) := by
  intro v
  obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
    ((hρ v).mem_nhds (one_mem (stabilizerOf ρ v)))
  refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
  rw [mem_stabilizerOf, twist_apply, nnrealCharC_apply, hK1 k hk, mem_stabilizerOf.1 (hKU hk)]
  simp

theorem isAdmissible_twist (hρ : IsAdmissible ρ) : IsAdmissible (twist (nnrealCharC χ) ρ) :=
  ⟨isSmooth_twist χ hχ ρ hρ.1, fun K hKc hKo => by
    rw [fixedVectors_twist χ hχ ρ hKc]
    exact hρ.2 K hKc hKo⟩

omit hχ in

def subrepresentationTwistOrderIso :
    Subrepresentation (twist (nnrealCharC χ) ρ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.apply_mem_toSubmodule g hv
    rw [twist_apply] at h
    have := S.toSubmodule.smul_mem (nnrealCharC χ g)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (nnrealCharC_ne_zero χ g), one_smul] at this⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

omit hχ in
theorem isIrreducible_twist [ρ.IsIrreducible] :
    (twist (nnrealCharC χ) ρ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (subrepresentationTwistOrderIso χ ρ)).2 inferInstance

theorem mem_smoothVectors_dual_twist_iff {ℓ : Module.Dual ℂ W} :
    ℓ ∈ smoothVectors (Representation.dual (twist (nnrealCharC χ) ρ)) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := by
  have key : ∀ (ρ₁ ρ₂ : Representation ℂ G W), (∀ g, ∀ x, χ g = 1 → ρ₁ g x = ρ₂ g x) →
      ℓ ∈ smoothVectors (Representation.dual ρ₁) → ℓ ∈ smoothVectors (Representation.dual ρ₂) := by
    intro ρ₁ ρ₂ h12 hℓ
    obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
      (hℓ.mem_nhds (one_mem (stabilizerOf (Representation.dual ρ₁) ℓ)))
    refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
    have h1 := mem_stabilizerOf.1 (hKU hk)
    rw [mem_stabilizerOf]
    ext x
    have := LinearMap.congr_fun h1 x
    rw [dual_apply_apply] at this ⊢
    rw [← h12 k⁻¹ x (by rw [map_inv, hK1 k hk, inv_one]), this]
  constructor
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp

end Twist

section PUnitProd

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def prodPUnitEquiv : (G × PUnit) ≃ₜ* G where
  toFun p := p.1
  invFun g := (g, 1)
  left_inv p := by ext1 <;> rfl
  right_inv g := rfl
  map_mul' p q := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

end PUnitProd

section LeviBlocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem leviEquivPi_symm_apply_entry (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F)
    (a : Set.range β) (k l : Fin (blockSize β a)) :
    (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) (fiberFin β a k).1
      (fiberFin β a l).1 = ((x a : GL (Fin (blockSize β a)) F) : Matrix _ _ F) k l := by
  rw [← leviEquivPi_apply, ContinuousMulEquiv.apply_symm_apply]

theorem det_leviEquivPi (m : levi F n β) (a : Set.range β) :
    Matrix.det ((leviEquivPi F β m a : GL (Fin (blockSize β a)) F) :
      Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) =
      Matrix.det ((leviBlock F m a : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F) := by
  show (Matrix.reindex _ _ ((leviBlock F m a : GL (Fiber β a) F) :
    Matrix (Fiber β a) (Fiber β a) F)).det = _
  exact Matrix.det_reindex_self _ _

theorem ordDet_leviEquivPi (m : levi F n β) (a : Set.range β) :
    ordDet (leviEquivPi F β m a) = blockOrd F a m := by
  rw [ordDet, det_leviEquivPi]
  rfl

theorem detPow_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) (s : ℂ) :
    detPow (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) s =
      ∏ a, detPow (x a) s := by
  rw [detPow_eq_qs_zpow, ordDet_eq_sum_blockOrd]
  have : ∀ a, blockOrd F a ((leviEquivPi F β).symm x) = ordDet (x a) := fun a => by
    rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]
  simp_rw [this, detPow_eq_qs_zpow]
  classical
  induction (Finset.univ : Finset (Set.range β)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (qs_ne_zero s), ih]

theorem leviModulus_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviModulus β ((leviEquivPi F β).symm x) = ∏ a, detModulusPow (x a) := by
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [detModulusPow, ← det_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]

theorem leviEquivPi_symm_mulSingle (a : Set.range β) :
    (leviEquivPi F β).symm (Pi.mulSingle a (centralUnif F (blockSize β a))) = blockUnif F a := by
  classical
  apply (leviEquivPi F β).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  funext b
  ext k l
  rw [leviEquivPi_apply]
  simp only [blockUnif, Cartan.diagPow, Matrix.diagonal_apply]
  have hk : blockOf β (fiberFin β b k).1 = b := (fiberFin β b k).2
  have hkl : (fiberFin β b k).1 = (fiberFin β b l).1 ↔ k = l := by
    rw [← Subtype.ext_iff, (fiberFin β b).injective.eq_iff]
  by_cases hb : b = a
  · subst hb
    rw [Pi.mulSingle_eq_same, coe_centralUnif]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, blockIndicator, hk, if_true,
      zpow_one, hkl]
    split_ifs <;> simp
  · rw [Pi.mulSingle_eq_of_ne hb]
    simp only [Units.val_one, Matrix.one_apply, blockIndicator, hk, if_neg hb, zpow_zero, hkl]

variable (β) in

def leviIdx (a : Set.range β) (k l : Fin (blockSize β a)) : LeviIndex n β :=
  ⟨((fiberFin β a k).1, (fiberFin β a l).1), by
    have hk := congrArg Subtype.val (fiberFin β a k).2
    have hl := congrArg Subtype.val (fiberFin β a l).2
    exact hk.trans hl.symm⟩

theorem leviIdx_bijective :
    Function.Bijective fun p : (Σ a : Set.range β, Fin (blockSize β a) × Fin (blockSize β a)) =>
      leviIdx β p.1 p.2.1 p.2.2 := by
  constructor
  · rintro ⟨a, k, l⟩ ⟨a', k', l'⟩ h
    have h1 : (fiberFin β a k).1 = (fiberFin β a' k').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.1) h
    have h2 : (fiberFin β a l).1 = (fiberFin β a' l').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.2) h
    have ha : a = a' := (fiberFin β a k).2.symm.trans (by rw [h1]; exact (fiberFin β a' k').2)
    subst ha
    have hk : k = k' := (fiberFin β a).injective (Subtype.ext h1)
    have hl : l = l' := (fiberFin β a).injective (Subtype.ext h2)
    subst hk hl
    rfl
  · rintro ⟨⟨i, j⟩, hij⟩
    have hj : blockOf β j = blockOf β i := Subtype.ext hij.symm
    refine ⟨⟨blockOf β i, ((fiberFin β (blockOf β i)).symm ⟨i, rfl⟩,
      (fiberFin β (blockOf β i)).symm ⟨j, hj⟩)⟩, ?_⟩
    simp only [leviIdx, Equiv.apply_symm_apply]

theorem prod_leviIndex {M : Type*} [CommMonoid M] (f : LeviIndex n β → M) :
    ∏ ij, f ij = ∏ a : Set.range β, ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
      f (leviIdx β a p.1 p.2) := by
  rw [← Fintype.prod_equiv (Equiv.ofBijective _ leviIdx_bijective) (fun p => f (leviIdx β p.1 p.2.1 p.2.2)) f
    (fun p => rfl), Fintype.prod_sigma]

variable (β) in

def blockTensor (φ : LeviIndex n β → F → ℂ) (a : Set.range β)
    (X : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) : ℂ :=
  ∏ p : Fin (blockSize β a) × Fin (blockSize β a), φ (leviIdx β a p.1 p.2) (X p.1 p.2)

theorem leviTensor_leviEquivPi_symm (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensor β φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, blockTensor β φ a (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensor, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

theorem isSchwartzBruhat_blockTensor {φ : LeviIndex n β → F → ℂ}
    (hφ : ∀ ij, φ ij ∈ LocalField.schwartzBruhat F) (a : Set.range β) :
    IsSchwartzBruhat (blockTensor β φ a) := by
  rw [GJMatrix.isSchwartzBruhat_iff_comp_symm]
  have : blockTensor β φ a ∘ (GJMatrix.matrixCoordHomeomorph (Fin (blockSize β a)) F).symm =
      GJMatrix.localTensor fun p : Fin (blockSize β a) × Fin (blockSize β a) =>
        φ (leviIdx β a p.1 p.2) := by
    funext z
    rfl
  rw [this]
  exact GJMatrix.localTensor_mem fun p => hφ _

variable [MeasurableSpace F] [BorelSpace F]

theorem localMatrixFourier_entryTensor (ψ : AddChar F Circle) {m : ℕ}
    (g : Fin m × Fin m → F → ℂ) (Y : Matrix (Fin m) (Fin m) F) :
    GJMatrix.localMatrixFourier ψ (fun X => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) Y =
      ∏ p : Fin m × Fin m,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g p) (Y p.2 p.1) := by
  rw [GJMatrix.localMatrixFourier_eq]
  have : (fun X : Matrix (Fin m) (Fin m) F => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) ∘
      (GJMatrix.matrixCoordHomeomorph (Fin m) F).symm = GJMatrix.localTensor g := by
    funext z
    rfl
  rw [this, GJMatrix.localFourierPi_localTensor]
  rfl

theorem leviTensorHat_leviEquivPi_symm (ψ : AddChar F Circle) (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensorHat β ψ φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, GJMatrix.localMatrixFourier ψ (blockTensor β φ a)
        (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensorHat, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show blockTensor β φ a = fun X => ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
    φ (leviIdx β a p.1 p.2) (X p.1 p.2) from rfl, localMatrixFourier_entryTensor]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

end LeviBlocks

section Main

universe uF u w

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type u} [LinearOrder α] {β : Fin n → α}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem nontrivial_of_isIrreducible {G : Type*} [Group G] (ρ : Representation ℂ G W)
    [ρ.IsIrreducible] : Nontrivial W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Subrepresentation ρ) := ⟨fun S T => by
    cases S; cases T; congr 1; exact Subsingleton.elim _ _⟩
  exact bot_ne_top (Subsingleton.elim (⊥ : Subrepresentation ρ) ⊤)

theorem detPow_add (g : GL (Fin n) F) (a b : ℂ) : detPow g (a + b) = detPow g a * detPow g b := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, detPow_eq_qs_zpow, qs_add, mul_zpow]

theorem borelSpace_GL_units (m : ℕ) : BorelSpace (GL (Fin m) F) := by
  refine ⟨?_⟩
  have hM : (GJMatrix.measurableSpace_matrix : MeasurableSpace (Matrix (Fin m) (Fin m) F)) =
      _root_.borel (Matrix (Fin m) (Fin m) F) := BorelSpace.measurable_eq
  show MeasurableSpace.comap Units.val _ = _
  rw [hM, ← borel_comap, ← (Measures.isOpenEmbedding_val F m).isEmbedding.eq_induced]

theorem exists_leviFE (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ γ : RatFunc ℂ, LeviFE F σ κ μM ψ γ := by
  classical
  have _ : ∀ m : ℕ, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  set e := leviEquivPi F β with he

  set κ' : (∀ a : Set.range β, GL (Fin (blockSize β a)) F) →* ℝ≥0 :=
    κ.comp e.symm.toMonoidHom with hκ'def
  have hκ' : Continuous κ' := hκ.comp e.symm.continuous
  set σ' : Representation ℂ (∀ a : Set.range β, GL (Fin (blockSize β a)) F) W :=
    σ.comp e.symm.toMonoidHom with hσ'def
  set ρ₀ := twist (nnrealCharC κ') σ' with hρ₀def
  set ρ : Representation ℂ ((∀ a : Set.range β, GL (Fin (blockSize β a)) F) × PUnit.{max u uF + 1}) W :=
    ρ₀.comp (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)).toMulEquiv.toMonoidHom
    with hρdef
  have hρ : ∀ x (h : PUnit.{max u uF + 1}) v, ρ (x, h) v = ((κ (e.symm x) : ℝ) : ℂ) • σ (e.symm x) v :=
    fun x h v => rfl
  have hσ' : IsAdmissible σ' := (isAdmissible_comp_iff e.symm σ).2 hσ
  have hadm : IsAdmissible ρ := (isAdmissible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isAdmissible_twist κ' hκ' σ' hσ')
  have hirr' : σ'.IsIrreducible := (isIrreducible_comp_iff e.symm σ).2 inferInstance
  have hirr : ρ.IsIrreducible := (isIrreducible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isIrreducible_twist κ' σ')
  have hsm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ) ↔
      ℓ ∈ smoothVectors (Representation.dual σ) := fun ℓ => by
    rw [mem_smoothVectors_dual_comp_iff
      (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀,
      mem_smoothVectors_dual_twist_iff κ' hκ' σ', mem_smoothVectors_dual_comp_iff e.symm σ]

  obtain ⟨ω, hω⟩ := exists_blockChar hσ.1 (σ := σ)
  have hW : Nontrivial W := nontrivial_of_isIrreducible σ
  have hω0 : ∀ a, ω a ≠ 0 := by
    intro a h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : σ (blockUnif F a)⁻¹ (σ (blockUnif F a) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  set αc : Set.range β → ℂ := fun a => ((κ (blockUnif F a) : ℝ) : ℂ) * ω a with hαc
  have hα0 : ∀ a, αc a ≠ 0 := fun a =>
    mul_ne_zero (by simpa using nnrealCharC_ne_zero κ (blockUnif F a)) (hω0 a)
  have hα : ∀ a v, ρ (Pi.mulSingle a (centralUnif F (blockSize β a)), 1) v = αc a • v := by
    intro a v
    rw [hρ, leviEquivPi_symm_mulSingle, hω, smul_smul]

  have hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
      ∃ C : Set (∀ a : Set.range β, GL (Fin (blockSize β a)) F), IsCompact C ∧
        ∀ x, ℓ (ρ (x, 1) v) ≠ 0 →
          ∃ j : Set.range β → ℤ, (fun a => centralUnif F (blockSize β a) ^ j a) * x ∈ C := by
    intro v ℓ hℓ
    have hℓσ := (hsm ℓ).1 hℓ
    obtain ⟨CM, hCM, hCMs⟩ := exists_compact_of_coeff hσ.1 hc v hℓσ (fun _ => 0)
      (fun b => (blockSize β b : ℤ) - 1)
    refine ⟨e '' CM, hCM.image e.continuous, fun x hx => ?_⟩
    have hpos : ∀ b, (0 : ℤ) < blockSize β b := fun b => by exact_mod_cast blockSize_pos β b
    set j : Set.range β → ℤ := fun b => -(ordDet (x b) / blockSize β b) with hj
    refine ⟨j, e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x), ?_, by simp⟩
    refine hCMs _ ?_ fun b => ?_
    · have hmul := apply_centralPow ρ hα0 hα j (ρ (x, 1) v)
      have h2 : ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v =
          (∏ a, αc a ^ j a) • ρ (x, 1) v := by
        rw [← hmul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      have h3 := hρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x) 1 v
      intro h0
      apply hx
      have hprod0 : (∏ a, αc a ^ j a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (hα0 a)
      have hκ0 := nnrealCharC_ne_zero κ (e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x))
      rw [nnrealCharC_apply] at hκ0
      have : ℓ (ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v) = 0 := by
        rw [h3, map_smul, smul_eq_mul, h0, mul_zero]
      rw [h2, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hprod0
    · rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply,
        ordDet_centralUnif_zpow_mul]
      have h1 := Int.emod_nonneg (ordDet (x b)) (hpos b).ne'
      have h2 := Int.emod_lt_of_pos (ordDet (x b)) (hpos b)
      have h3 := Int.emod_def (ordDet (x b)) (blockSize β b)
      simp only [hj]
      constructor <;> nlinarith

  have _ : ∀ a : Set.range β, NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  set μb : ∀ a : Set.range β, Measure (GL (Fin (blockSize β a)) F) := fun a => Measure.haar
    with hμb
  obtain ⟨γ, hmain⟩ := multiFEStatement_all.{uF, u, w} hψ hψ1
    (Fintype.card (Set.range β)) (Set.range β) rfl (fun a => blockSize β a) μb
    PUnit.{max u uF + 1} ρ hadm hirr αc hα0 hα hsupp
  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μb

  set em := e.toHomeomorph.toMeasurableEquiv with hem
  have hν : (Measure.map em μM).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μM e.toMulEquiv e.continuous e.symm.continuous
  set c := haarScalarFactor (Measure.map em μM) (Measure.pi μb) with hcdef
  have hc : Measure.map em μM = c • Measure.pi μb :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map em μM) (Measure.pi μb)
  have hemx : ∀ m, e.symm (em m) = m := fun m => e.symm_apply_apply m
  have hint_eq : ∀ f : levi F n β → ℂ,
      ∫ m, f m ∂μM = ((c : ℝ) : ℂ) * ∫ x, f (e.symm x) ∂Measure.pi μb := by
    intro f
    have h1 : ∫ x, f (e.symm x) ∂(Measure.map em μM) = ∫ m, f m ∂μM := by
      rw [integral_map_equiv em]
      simp only [hemx]
    rw [← h1, hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl,
      integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  have hint_of : ∀ f : levi F n β → ℂ,
      Integrable (fun x => f (e.symm x)) (Measure.pi μb) → Integrable f μM := by
    intro f hf
    have h1 : Integrable (fun x => f (e.symm x)) (Measure.map em μM) := by
      rw [hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl]
      exact hf.smul_measure ENNReal.coe_ne_top
    rw [integrable_map_equiv] at h1
    exact h1.congr (Filter.Eventually.of_forall fun m => by simp only [Function.comp_apply, hemx])
  refine ⟨γ, fun φ hφ w ℓ hℓ => ?_⟩
  set Ψ : ∀ a : Set.range β, Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ :=
    fun a => blockTensor β φ a with hΨdef
  have hΨ : ∀ a, IsSchwartzBruhat (Ψ a) := fun a => isSchwartzBruhat_blockTensor hφ a
  have hℓρ : ℓ ∈ smoothVectors (Representation.dual ρ) := (hsm ℓ).2 hℓ
  have hA_eq : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) =
      multiA ρ Ψ w ℓ s x := by
    intro s x
    simp only [leviIntegrand, multiA]
    rw [leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρ, map_smul, smul_eq_mul,
      Finset.prod_mul_distrib]
    ring
  have hB_eq : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
      multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
    intro s x
    simp only [leviIntegrandB, multiB]
    rw [leviTensorHat_leviEquivPi_symm, leviModulus_leviEquivPi_symm, detPow_leviEquivPi_symm,
      hρ, map_smul, smul_eq_mul, map_inv e.symm x, map_inv κ]
    have hdet : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) =
        ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) := fun a => by
      rw [sub_eq_add_neg, detPow_add, detPow_natCast]
    simp_rw [hdet]
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  refine ⟨⟨s₀, fun s hs => hint_of _ (((hconv Ψ hΨ w ℓ hℓρ).1 s hs).congr
      (Filter.Eventually.of_forall fun x => (hA_eq s x).symm))⟩,
    ⟨-s₀, fun s hs => hint_of _ (((hconv (fun a => GJMatrix.localMatrixFourier ψ (Ψ a))
      (fun a => (hΨ a).localMatrixFourier hψ hψ1) w ℓ hℓρ).2 s hs).congr
      (Filter.Eventually.of_forall fun x => (hB_eq s x).symm))⟩, ?_⟩
  refine ((hmain Ψ hΨ w ℓ hℓρ).const_mul ((c : ℝ) : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hA_eq s x)
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hB_eq s x)

end Main

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance measurableSpace_infiniteAdelicGL : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _

instance borelSpace_infiniteAdelicGL : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩

variable (K n) in

def archComp : AdelicGLn.AdelicGL K n →* AdelicGLn.InfiniteAdelicGL K n :=
  (MonoidHom.fst _ _).comp (AdelicGLn.prodEquiv K n).toMonoidHom

variable (K n) in

def finComp : AdelicGLn.AdelicGL K n →* AdelicGLn.FiniteAdelicGL K n :=
  (MonoidHom.snd _ _).comp (AdelicGLn.prodEquiv K n).toMonoidHom

variable (n) in

def localComp (v : HeightOneSpectrum (𝓞 K)) :
    AdelicGLn.AdelicGL K n →* GL (Fin n) (v.adicCompletion K) where
  toFun g := AdelicGLn.finiteRestrictedEquiv K n (finComp K n g) v
  map_one' := by rw [map_one, map_one, RestrictedProduct.one_apply]
  map_mul' g h := by rw [map_mul, map_mul, RestrictedProduct.mul_apply]

def archMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) :=
  x.map Prod.fst

def localMat (v : HeightOneSpectrum (𝓞 K)) (x : Matrix (Fin n) (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) (v.adicCompletion K) :=
  x.map fun a ↦ a.2 v

theorem coe_archComp (g : AdelicGLn.AdelicGL K n) :
    ((archComp K n g : AdelicGLn.InfiniteAdelicGL K n) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
      archMat (g : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  ext i j
  exact AdelicGLn.prodEquiv_apply_fst K n g i j

theorem coe_localComp (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    ((localComp n v g : GL (Fin n) (v.adicCompletion K)) : Matrix (Fin n) (Fin n) (v.adicCompletion K)) =
      localMat v (g : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  ext i j
  rfl

theorem eventually_localComp_mem (g : AdelicGLn.AdelicGL K n) :
    ∀ᶠ v in cofinite, localComp n v g ∈ integralGL (v.adicCompletion K) n :=
  AdelicGLn.eventually_mem_integralGL K n g

def archSchwartz (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) : ℂ :=
  φ fun ij ↦ GroundTheory.Global.homeomorphMixedSpace K (x ij.1 ij.2)

def matrixTensor (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (x : Matrix (Fin n) (Fin n) 𝔸[K]) : ℂ :=
  archSchwartz φ (archMat x) * ∏ᶠ v, Φ v (localMat v x)

def archAbsDet (x : AdelicGLn.InfiniteAdelicGL K n) : ℝ :=
  ∏ w : InfinitePlace K, ‖((x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det) w‖ ^ w.mult

def archDetPow (x : AdelicGLn.InfiniteAdelicGL K n) (s : ℂ) : ℂ :=
  (archAbsDet x : ℂ) ^ s

def archIntegrand (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (f : AdelicGLn.InfiniteAdelicGL K n → ℂ) (s : ℂ) (x : AdelicGLn.InfiniteAdelicGL K n) : ℂ :=
  archSchwartz φ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) * f x *
    archDetPow x (s + ((n : ℂ) - 1) / 2)

def archZeta (μ : Measure (AdelicGLn.InfiniteAdelicGL K n))
    (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ)) (f : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (s : ℂ) : ℂ :=
  ∫ x, archIntegrand φ f s x ∂μ

variable (n) in

def integralGLPositiveCompacts (v : HeightOneSpectrum (𝓞 K)) :
    TopologicalSpace.PositiveCompacts (GL (Fin n) (v.adicCompletion K)) where
  carrier := integralGL (v.adicCompletion K) n
  isCompact' := isCompact_integralGL _ n
  interior_nonempty' := by
    rw [(isOpen_integralGL _ n).interior_eq]
    exact ⟨1, (integralGL _ n).one_mem⟩

variable (n) in

def localHaar (v : HeightOneSpectrum (𝓞 K)) : Measure (GL (Fin n) (v.adicCompletion K)) :=
  Measure.haarMeasure (integralGLPositiveCompacts n v)

instance isHaarMeasure_localHaar (v : HeightOneSpectrum (𝓞 K)) : (localHaar n v).IsHaarMeasure := by
  unfold localHaar
  infer_instance

theorem localHaar_integralGL (v : HeightOneSpectrum (𝓞 K)) :
    localHaar n v (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
  Measure.haarMeasure_self

def partialL (S : Finset (HeightOneSpectrum (𝓞 K))) {V : HeightOneSpectrum (𝓞 K) → Type*}
    [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, LFunction (π v) s

end GJStandardL

end

end GroundTheory.Automorphic
end
