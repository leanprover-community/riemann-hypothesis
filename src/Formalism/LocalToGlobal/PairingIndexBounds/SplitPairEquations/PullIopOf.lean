import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SemiCharImg

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7}

def gM {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  γ.map (TaylorLogMetric.embT D τ)

theorem embT_star' (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.embT D τ (letI := D.host.cmStar; star x) = star (TaylorLogMetric.embT D τ x) := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
  rfl

theorem gM_conjTranspose {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (gM γ τ)ᴴ = gM (letI := D.host.cmStar; star γ) τ := by
  letI := D.host.cmStar
  ext i j
  simp only [gM, conjTranspose_apply, map_apply, star_apply]
  rw [embT_star']

theorem gM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A * B) τ = gM A τ * gM B τ := by
  simp [gM, Matrix.map_mul]

theorem gM_one {n : ℕ} (τ : D.what₂.Tau) : gM (1 : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp [gM, Matrix.map_one]

theorem gM_unit {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; star γ * γ) = 1)
    (τ : D.what₂.Tau) : (gM γ τ)ᴴ * gM γ τ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

theorem gM_unit' {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; γ * star γ) = 1)
    (τ : D.what₂.Tau) : gM γ τ * (gM γ τ)ᴴ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

variable {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)

def phiL (h1 : (letI := D.host.cmStar; star γ * γ) = 1) (h2 : (letI := D.host.cmStar; γ * star γ) = 1)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) (h2' : (letI := D.host.cmStar; γ' * star γ') = 1) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ => (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ : Matrix _ _ ℂ)
  invFun z := fun τ => (Matrix.conjTranspose (γ'.map (TaylorLogMetric.embT D τ)) * (Matrix.of (z τ)) * γ.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  map_add' x y := by
    funext τ
    show gM γ' τ * (Matrix.of (x τ) + Matrix.of (y τ)) * (gM γ τ)ᴴ = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c x := by
    funext τ
    show gM γ' τ * (c • Matrix.of (x τ)) * (gM γ τ)ᴴ = c • (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv z := by
    funext τ
    show (gM γ' τ)ᴴ * (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ) * gM γ τ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit γ h1, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit γ' h1',
      Matrix.one_mul]
  right_inv z := by
    funext τ
    show gM γ' τ * ((gM γ' τ)ᴴ * Matrix.of (z τ) * gM γ τ) * (gM γ τ)ᴴ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit' γ h2, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit' γ' h2',
      Matrix.one_mul]

theorem sum_trace {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ) :
    ∑ i, ∑ j, X i j * (starRingEnd ℂ) (Y i j) = Matrix.trace (X * Yᴴ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem trace_unit {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) (Z W : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (P * Z * Q * (P * W * Q)ᴴ) = Matrix.trace (Z * Wᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc Matrix.trace (P * Z * Q * (Qᴴ * (Wᴴ * Pᴴ))) = Matrix.trace (P * (Z * Wᴴ * Pᴴ)) := by
        rw [show P * Z * Q * (Qᴴ * (Wᴴ * Pᴴ)) = P * Z * (Q * Qᴴ) * (Wᴴ * Pᴴ) by simp only [Matrix.mul_assoc], hQ]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Matrix.trace (Z * Wᴴ * Pᴴ * P) := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = Matrix.trace (Z * Wᴴ) := by rw [Matrix.mul_assoc, hP, Matrix.mul_one]

theorem phiL_isom (h1 h2 h1' h2') (A : ℝ) :
    IsIsom (Ker.formV A D.what₂.Tau N N') (Ker.formV A D.what₂.Tau N N')
      ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') := by
  intro x y
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_trace (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ) (gM γ' τ * Matrix.of (y τ) * (gM γ τ)ᴴ)
  have e2 := sum_trace (Matrix.of (x τ)) (Matrix.of (y τ))
  rw [trace_unit _ _ (gM_unit γ' h1' τ) (by rw [Matrix.conjTranspose_conjTranspose]; exact gM_unit γ h1 τ)] at e
  exact e.trans e2.symm

end Formalism.L2.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7}

theorem mem_smulLat {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (x : Fin n → D.host.E) : x ∈ SDLat.smulLat γ L ↔ ∃ w ∈ L, γ *ᵥ w = x := by
  simp [SDLat.smulLat, Submodule.mem_map, Matrix.toLin'_apply]

theorem homL_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 : (letI := D.host.cmStar; star γ * γ) = 1) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.homL D L L') :
    (letI := D.host.cmStar; γ' * A * star γ) ∈ TaylorLogMetric.homL D (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  letI := D.host.cmStar
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := (mem_smulLat γ L y).1 hy
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← mulVec_mulVec]
    exact (mem_smulLat γ' L' _).2 ⟨_, hA x hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ r hx

theorem yy_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 : (letI := D.host.cmStar; star γ * γ) = 1) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.YYl D L L') :
    (letI := D.host.cmStar; γ' * A * star γ) ∈ TaylorLogMetric.YYl D (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  letI := D.host.cmStar
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hB
    refine Submodule.subset_span ⟨a, ha, _, homL_conj γ γ' h1 hA₀, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ r hx

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem embV_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (A : Matrix (Fin N') (Fin N) D.host.E) :
    TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (letI := D.host.cmStar; γ' * A * star γ) =
      phiL γ γ' h1 h2 h1' h2' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) := by
  letI := D.host.cmStar
  funext τ
  have e : ((γ' * A * star γ).map (TaylorLogMetric.embT D τ)) = gM γ' τ * A.map (TaylorLogMetric.embT D τ) * (gM γ τ)ᴴ := by
    rw [gM_conjTranspose]
    unfold gM
    rw [Matrix.map_mul, Matrix.map_mul]
  exact e

theorem la_img {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    imgLat ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  letI := D.host.cmStar
  unfold imgLat TaylorLogMetric.La
  rw [AddMonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨w, hw, A, hA, rfl⟩, rfl⟩
    refine ⟨w, hw, _, yy_conj γ γ' h1 hA, ?_⟩
    show phiL γ γ' h1 h2 h1' h2' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) = _
    rw [map_smul, embV_conj γ γ' h1 h2 h1' h2']
  · rintro ⟨w, hw, B, hB, rfl⟩
    have hs : star (star γ) * star γ = 1 := by rw [star_star]; exact h2
    have hA := yy_conj (star γ) (star γ') hs hB
    rw [← Formalism.BasicNotions.Examples₂.smulLat_mul, ← Formalism.BasicNotions.Examples₂.smulLat_mul, h1, h1', Formalism.BasicNotions.Examples₂.smulLat_one,
      Formalism.BasicNotions.Examples₂.smulLat_one, star_star] at hA
    refine ⟨_, ⟨w, hw, _, hA, rfl⟩, ?_⟩
    show phiL γ γ' h1 h2 h1' h2' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) _) = _
    rw [map_smul, ← embV_conj γ γ' h1 h2 h1' h2']
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2', Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem Hf_eq' (T : TaylorLogMetric.Tor D) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Hf D T z w = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z w := rfl

theorem pull_eq {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (F : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' F = pullInv (phiL γ γ' h1 h2 h1' h2') F := rfl

theorem al_phi {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (x : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (phiL γ γ' h1 h2 h1' h2' x) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x := by
  unfold TaylorLogMetric.al
  rw [Hf_eq', Hf_eq']
  have e := phiL_isom γ γ' h1 h2 h1' h2' (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) x x
  simp only [LinearEquiv.coe_coe] at e
  rw [e]

theorem pull_core {B : Ker.Base D cc δ} (hL : B.LatAll) {N N' : ℕ} (φ : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N')
    (hI : IsIsom (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N'))
    (hα : ∀ x, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (φ x) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x)
    {L L₁ M M₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' M' M₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L L') (a2 : TaylorLogMetric.admitted D N N' L₁ L₁')
    (i1 : imgLat (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M')
    (i2 : imgLat (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M₁ M₁')
    (G : TaylorLogMetric.VC D N N' → ℂ) (hG : G ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) L L') :
    pullInv φ G ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) M M' ∧
      pullInv φ (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') G) =
        TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M₁ M₁') (pullInv φ G) := by
  have hH := formV_herm' (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N'
  have hF : G ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') := fun x hx z => hG.2 x hx z
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hG.1.comp (φ.symm.toContinuousLinearEquiv.differentiable)
  · have hf := fixed_img _ _ φ hI hα hF
    rw [i1] at hf
    exact fun x hx z => hf x hx z
  · have := inter_pull _ _ φ hH hI hα _ _ (hL.1 N N' L₁ L₁' a2).2 (hL.2 N N' L L' L₁ L₁' a1 a2).1 hF
    rw [i1, i2] at this
    exact this

theorem pullIop_of {B : Ker.Base D cc δ} (hL : B.LatAll) : PullIop D B.tor := by
  letI := D.host.cmStar
  intro N N' L L₁ L' L₁' γ γ' hN hN' s1 s2 s3 s4 G hG
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  have hc := pull_core hL (phiL _ _ h1 h2 h1' h2') (phiL_isom _ _ h1 h2 h1' h2' _) (al_phi _ _ h1 h2 h1' h2')
    (⟨hN, hN', s1, s3⟩ : TaylorLogMetric.admitted D N N' L L') (⟨hN, hN', s2, s4⟩ : TaylorLogMetric.admitted D N N' L₁ L₁')
    (la_img _ _ h1 h2 h1' h2' L L') (la_img _ _ h1 h2 h1' h2' L₁ L₁') G hG
  rw [pull_eq _ _ h1 h2 h1' h2']
  exact hc

end Formalism.L2.PairingIndexBounds.Eq
end
end
