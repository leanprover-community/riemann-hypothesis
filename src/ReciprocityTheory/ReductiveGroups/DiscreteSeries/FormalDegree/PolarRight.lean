import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarAct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detPaCj (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun W := P * W * Q
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

def detPaRow (t : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun j => (t j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j))

def detPaHad (s : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi (fun i => (detPaRow (s i)).comp (LinearMap.proj i))

theorem detPaRow_det (t : Fin n → ℂ) : LinearMap.det (detPaRow t) = ∏ j, t j := by
  unfold detPaRow
  rw [LinearMap.det_pi]
  simp

theorem detPaHad_det (s : Fin n → Fin n → ℂ) : LinearMap.det (detPaHad s) = ∏ i, ∏ j, s i j := by
  unfold detPaHad
  rw [LinearMap.det_pi]
  simp [detPaRow_det]

theorem detPa {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      ∏ i, ∏ j, shc (pev y i - pev y j) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ((pmat_isHermitian y).eigenvectorUnitary).2
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hmem
  set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := detPaHad s
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))
  have hT : ∀ W, T W = shcAd y W := by
    intro W
    simp only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]
    congr 2
  have hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) := by
    funext W; exact (hT W).symm
  rw [hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]
  have hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1 := by
    rw [← LinearMap.det_comp]
    have : (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id := by
      ext W : 1
      simp only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [this, LinearMap.det_id]
  have hdet : LinearMap.det T = ∏ i, ∏ j, s i j := by
    simp only [T]
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hH : LinearMap.det H = ∏ i, ∏ j, s i j := detPaHad_det s
    rw [hH, mul_left_comm, hAB, mul_one]
  rw [hdet, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem dpb_sylv (f : W →ₗ[ℝ] V) (g : V →ₗ[ℝ] W) :
    LinearMap.det (1 + f ∘ₗ g : V →ₗ[ℝ] V) = LinearMap.det (1 + g ∘ₗ f : W →ₗ[ℝ] W) := by
  classical
  let bV := Module.finBasis ℝ V
  let bW := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix bV, ← LinearMap.det_toMatrix bW, map_add, map_add,
    LinearMap.toMatrix_comp bV bW bV, LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_one,
    LinearMap.toMatrix_one]
  exact Matrix.det_one_add_mul_comm _ _

theorem dpb_ring {R : Type*} [Ring R] (a p q : R) (h0 : p * q = 0) (hc : p * a = a * p) :
    (1 + a * p) * (1 + a * q) = 1 + a * (p + q) := by
  have h : a * p * (a * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p a q, hc, mul_assoc, h0, mul_zero, mul_zero]
  calc (1 + a * p) * (1 + a * q) = 1 + a * p + a * q + a * p * (a * q) := by noncomm_ring
    _ = 1 + a * (p + q) := by rw [h, add_zero, mul_add, add_assoc]

theorem det_one_add_compression (a p q r s ι κ N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hpq : p + q = 1) (hpq0 : p * q = 0) (hpa : p * a = a * p)
    (hNC : N * C = a) (hCN : C * N = a) (hpN : p * N = N * q)
    (hrs : r + s = q) (hrs0 : r * s = 0) (hra : r * a = a * r)
    (hι : ι * κ = 1) (hιa : ι * a = a * ι) (hιr : ι * r = s * ι)
    (hEP : E ∘ₗ P = r) :
    LinearMap.det (1 + a) = LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have hsy : ∀ X Y : Module.End ℝ V, LinearMap.det (1 + X * Y) = LinearMap.det (1 + Y * X) :=
    fun X Y => dpb_sylv X Y
  have hA : 1 + a = (1 + a * p) * (1 + a * q) := by rw [dpb_ring a p q hpq0 hpa, hpq, mul_one]
  have hq : q = 1 - p := eq_sub_of_add_eq' hpq
  have hqa : q * a = a * q := by rw [hq, sub_mul, mul_sub, one_mul, mul_one, hpa]
  have hB1 : a * p = N * (q * C) := by rw [← hpa, ← hNC, ← mul_assoc, hpN, mul_assoc]
  have hB2 : q * C * N = a * q := by rw [mul_assoc, hCN, hqa]
  have hB : LinearMap.det (1 + a * p) = LinearMap.det (1 + a * q) := by
    rw [hB1, hsy N (q * C), hB2]
  have hC : 1 + a * q = (1 + a * r) * (1 + a * s) := by rw [dpb_ring a r s hrs0 hra, hrs]
  have hs : s = ι * r * κ := by rw [hιr, mul_assoc, hι, mul_one]
  have hD1 : 1 + a * s = ι * (1 + a * r) * κ := by
    rw [hs, mul_add, add_mul, mul_one, hι, ← mul_assoc ι a r, hιa]
    simp only [mul_assoc]
  have hdet : LinearMap.det ι * LinearMap.det κ = 1 := by rw [← map_mul, hι, map_one]
  have hD : LinearMap.det (1 + a * s) = LinearMap.det (1 + a * r) := by
    rw [hD1, map_mul, map_mul]
    calc LinearMap.det ι * LinearMap.det (1 + a * r) * LinearMap.det κ
        = LinearMap.det (1 + a * r) * (LinearMap.det ι * LinearMap.det κ) := by ring
      _ = LinearMap.det (1 + a * r) := by rw [hdet, mul_one]
  have hE : LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) = LinearMap.det (1 + a * r) := by
    have h := dpb_sylv E (P ∘ₗ a)
    have h2 : E ∘ₗ (P ∘ₗ a) = a * r := by
      show (E ∘ₗ P) ∘ₗ a = a * r
      rw [hEP, ← hra]
      rfl
    rw [h2] at h
    exact h.symm
  rw [hA, map_mul, hB, hC, map_mul, hD, hE]
  ring

theorem dpb_abs (t θ α ι N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hθ : ∀ v, θ (θ v) = v) (hα : ∀ v, α (α v) = v) (hθα : ∀ v, θ (α v) = α (θ v))
    (htθ : ∀ v, θ (t v) = t (θ v)) (htα : ∀ v, α (t v) = t (α v))
    (hNC : ∀ v, N (C v) = t v - v) (hCN : ∀ v, C (N v) = t v - v) (hθN : ∀ v, θ (N v) = -N (θ v))
    (hι : ∀ v, ι (ι v) = -v) (hιt : ∀ v, ι (t v) = t (ι v)) (hιθ : ∀ v, θ (ι v) = ι (θ v))
    (hια : ∀ v, α (ι v) = -ι (α v))
    (hEP : ∀ v, E (P v) = (1 / 4 : ℝ) • (v + α v - θ v - α (θ v))) (hPE : ∀ w, P (E w) = w) :
    LinearMap.det t = LinearMap.det (P ∘ₗ t ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have key := det_one_add_compression (t - 1) ((1 / 2 : ℝ) • (1 + θ)) ((1 / 2 : ℝ) • (1 - θ))
    ((1 / 4 : ℝ) • (1 + α - θ - α * θ)) ((1 / 4 : ℝ) • (1 - α - θ + α * θ)) ι (-ι) N C E P
    (by ext v; simp; module)
    (by ext v; simp [hθ]; try module)
    (by ext v; simp [htθ]; try module)
    (by ext v; simp [hNC]) (by ext v; simp [hCN])
    (by ext v; simp [hθN]; try module)
    (by ext v; simp; module)
    (by ext v; simp [hθ, hα, hθα]; try module)
    (by ext v; simp [htθ, htα]; try module)
    (by ext v; simp [hι])
    (by ext v; simp [hιt])
    (by ext v; simp [hιθ, hια]; try module)
    (by ext v; simp [hEP])
  have e1 : (1 : Module.End ℝ V) + (t - 1) = t := by abel
  have e2 : (1 + P ∘ₗ (t - 1) ∘ₗ E : W →ₗ[ℝ] W) = P ∘ₗ t ∘ₗ E := by
    ext w; simp [hPE]
  rwa [e1, e2] at key

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbH (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) * Uᴴ

def dpbD (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (x i : ℂ)

theorem dpbH_add (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W W' : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h (W + W') = dpbH U x h W + dpbH U x h W' := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (W + W') * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) +
        Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W' * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul]
  simp only [dpbH]
  rw [key, mul_add, add_mul]

theorem dpbH_smul (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (c : ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h (c • W) = c • dpbH U x h W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (c • W) * U) i j) =
      c • Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
    ring
  simp only [dpbH]
  rw [key, Matrix.mul_smul, Matrix.smul_mul]

def dpbL (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := dpbH U x h
  map_add' := dpbH_add U x h
  map_smul' c W := by
    have := dpbH_smul U x h (c : ℂ) W
    simpa only [Complex.coe_smul, RingHom.id_apply] using this

theorem dpbH_conjTranspose (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (he : ∀ u, h (-u) = h u)
    (W : Matrix (Fin n) (Fin n) ℂ) : (dpbH U x h W)ᴴ = dpbH U x h Wᴴ := by
  have key : (Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j))ᴴ =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * Wᴴ * U) i j) := by
    ext i j
    have h1 : (Uᴴ * Wᴴ * U) i j = star ((Uᴴ * W * U) j i) := by
      rw [← Matrix.conjTranspose_apply]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h2 : h (x j - x i) = h (x i - x j) := by rw [← neg_sub, he]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [h1, h2, star_mul']
    simp [Complex.conj_ofReal]
  rw [dpbH, dpbH, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, key]
  exact (Matrix.mul_assoc _ _ _).symm

theorem dpb_had_conj (Q M : Matrix (Fin n) (Fin n) ℂ) (F G : Fin n → Fin n → ℂ)
    (hFG : ∀ i j k l, Q i j ≠ 0 → Q l k ≠ 0 → F i l = G j k) :
    Matrix.of (fun i l => F i l * (Q * M * Qᴴ) i l) = Q * Matrix.of (fun j k => G j k * M j k) * Qᴴ := by
  ext i l
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : Q i j = 0
  · simp [h1]
  by_cases h2 : Q l k = 0
  · simp [h2]
  rw [hFG i j k l h1 h2]
  ring

theorem dpbH_indep {U V : Matrix (Fin n) (Fin n) ℂ} {x x' : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) (hY : U * dpbD x * Uᴴ = V * dpbD x' * Vᴴ) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h W = dpbH V x' h W := by
  have hQ : dpbD x * (Uᴴ * V) = (Uᴴ * V) * dpbD x' := by
    calc dpbD x * (Uᴴ * V) = Uᴴ * (U * dpbD x * Uᴴ) * V := by
          simp only [Matrix.mul_assoc]
          rw [← mul_assoc Uᴴ U, hU, one_mul]
      _ = Uᴴ * (V * dpbD x' * Vᴴ) * V := by rw [hY]
      _ = (Uᴴ * V) * dpbD x' := by
          simp only [Matrix.mul_assoc]
          rw [hV, mul_one]
  have hx : ∀ i j, (Uᴴ * V) i j ≠ 0 → x i = x' j := by
    intro i j hne
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hQ
    simp only [dpbD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    have h2 : ((x i : ℂ) - x' j) * (Uᴴ * V) i j = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.mp h3
    · exact absurd h3 hne
  have hQM : (Uᴴ * V) * (Vᴴ * W * V) * (Uᴴ * V)ᴴ = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uᴴ * V * (Vᴴ * W * V) * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * W * (V * Vᴴ) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hV', mul_one, mul_one]
  have key := dpb_had_conj (Uᴴ * V) (Vᴴ * W * V) (fun i l => ((h (x i - x l) : ℝ) : ℂ))
    (fun j k => ((h (x' j - x' k) : ℝ) : ℂ)) (by
      intro i j k l h1 h2
      show ((h (x i - x l) : ℝ) : ℂ) = ((h (x' j - x' k) : ℝ) : ℂ)
      rw [hx i j h1, hx l k h2])
  try simp only at key
  rw [hQM] at key
  simp only [dpbH]
  rw [key, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [hU', mul_one, ← mul_assoc U Uᴴ, hU', one_mul]

theorem dpbH_theta {U J : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hJ : J * J = 1) (hJ' : Jᴴ = J) (hY : J * (U * dpbD x * Uᴴ) * J = -(U * dpbD x * Uᴴ)) (h : ℝ → ℝ)
    (he : ∀ u, h (-u) = h u) (W : Matrix (Fin n) (Fin n) ℂ) :
    J * dpbH U x h W * J = dpbH U x h (J * W * J) := by
  have hV : (J * U)ᴴ * (J * U) = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * U) = Uᴴ * (J * J) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, mul_one, hU]
  have hV' : (J * U) * (J * U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc J * U * (Uᴴ * J) = J * (U * Uᴴ) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', mul_one, hJ]
  have hD : dpbD (-x) = -dpbD x := by
    ext i j
    simp only [dpbD, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply, Complex.ofReal_neg]
    split_ifs <;> simp
  have hY' : U * dpbD x * Uᴴ = (J * U) * dpbD (-x) * (J * U)ᴴ := by
    rw [hD, Matrix.conjTranspose_mul, hJ']
    calc U * dpbD x * Uᴴ = -(J * (U * dpbD x * Uᴴ) * J) := by rw [hY, neg_neg]
      _ = J * U * -dpbD x * (Uᴴ * J) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hM : (J * U)ᴴ * (J * W * J) * (J * U) = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * W * J) * (J * U) = Uᴴ * (J * J) * W * (J * J) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hJ, mul_one, mul_one]
  have hA : Matrix.of (fun i j => ((h ((-x) i - (-x) j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Pi.neg_apply]
    rw [neg_sub_neg, ← neg_sub, he]
  rw [dpbH_indep hU hU' hV hV' hY' h (J * W * J)]
  simp only [dpbH]
  rw [hM, hA, Matrix.conjTranspose_mul, hJ']
  simp only [Matrix.mul_assoc]

theorem dpb_comm_D (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dpbD x * X - X * dpbD x) i j = ((x i - x j : ℝ) : ℂ) * X i j := by
  simp only [dpbD, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_sub]
  ring

theorem dpbH_sub_one {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU' : U * Uᴴ = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x (fun u => h u - 1) W = dpbH U x h W - W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) - 1 : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) - Uᴴ * W * U := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sub_apply, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  simp only [dpbH]
  rw [key, mul_sub, sub_mul]
  congr 1
  calc U * (Uᴴ * W * U) * Uᴴ = (U * Uᴴ) * W * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = W := by rw [hU', one_mul, mul_one]

private theorem unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) : U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc U * A * Uᴴ * (U * B * Uᴴ) = U * A * (Uᴴ * U) * B * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uᴴ := by
        rw [hU, mul_one]
        simp only [Matrix.mul_assoc]

theorem dpbH_ad_left {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    (U * dpbD x * Uᴴ) * dpbH U x h W - dpbH U x h W * (U * dpbD x * Uᴴ) = dpbH U x (fun u => u * h u) W := by
  simp only [dpbH]
  rw [unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, ← sub_mul, ← mul_sub]
  congr 2
  ext i j
  rw [dpb_comm_D]
  simp only [Matrix.of_apply, Complex.ofReal_mul]
  ring

theorem dpbH_ad_right {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) = dpbH U x (fun u => u * h u) W := by
  have e1 : Uᴴ * (U * dpbD x * Uᴴ * W) * U = dpbD x * (Uᴴ * W * U) := by
    calc Uᴴ * (U * dpbD x * Uᴴ * W) * U = (Uᴴ * U) * dpbD x * (Uᴴ * W * U) := by
          simp only [Matrix.mul_assoc]
      _ = dpbD x * (Uᴴ * W * U) := by rw [hU, one_mul]
  have e2 : Uᴴ * (W * (U * dpbD x * Uᴴ)) * U = (Uᴴ * W * U) * dpbD x * (Uᴴ * U) := by
    simp only [Matrix.mul_assoc]
  have key : Uᴴ * ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) * U =
      dpbD x * (Uᴴ * W * U) - (Uᴴ * W * U) * dpbD x := by
    rw [mul_sub, sub_mul, e1, e2, hU, mul_one]
  simp only [dpbH]
  rw [key]
  congr 2
  ext i j
  simp only [Matrix.of_apply]
  rw [dpb_comm_D, Complex.ofReal_mul]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbE (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def dpbP (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun W ab := (1 / 2 : ℝ) • (W ab.1.1 ab.1.2 + star (W ab.1.2 ab.1.1))
  map_add' W W' := by
    ext ab
    simp only [Matrix.add_apply, Pi.add_apply, star_add]
    module
  map_smul' c W := by
    ext ab
    simp only [Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, star_smul, star_trivial]
    module

theorem dpbP_herm {ε : Fin n → Bool} {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ = W) (ab : PCoord ε) :
    dpbP ε W ab = W ab.1.1 ab.1.2 := by
  have h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2 := by
    have := congrFun (congrFun hW ab.1.1) ab.1.2
    simpa [Matrix.conjTranspose_apply] using this
  simp only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, Complex.real_smul]
  push_cast
  ring

theorem dpbP_E {ε : Fin n → Bool} (w : PCoord ε → ℂ) : dpbP ε (dpbE ε w) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, hab, hne⟩ := ab
  have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.mpr hab.le)
  simp only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1,
    star_star]
  rw [Complex.real_smul]
  push_cast
  ring

theorem dpb_JWJ (ε : Fin n → Bool) (W : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * W * Jm ε) a b = if ε a = ε b then W a b else -W a b := by
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases ε a <;> cases ε b <;> simp

theorem dpbE_P {ε : Fin n → Bool} (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbE ε (dpbP ε W) = (1 / 4 : ℝ) • (W + Wᴴ - Jm ε * W * Jm ε - (Jm ε * W * Jm ε)ᴴ) := by
  ext a b
  simp only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]
  by_cases hε : ε a = ε b
  · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => h.2 hε
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => h.2 hε.symm
    rw [dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]
    simp
  · rw [if_neg hε, if_neg (Ne.symm hε)]
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => absurd h'.1 (not_lt.mpr h.le)
      rw [dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]
      simp only [Complex.real_smul]
      push_cast
      simp only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]
      ring
    · exact absurd (h ▸ rfl) hε
    · rw [dif_pos (And.intro h hε)]
      simp only [star_neg, Complex.real_smul]
      push_cast
      ring

theorem dpb_JYJ {ε : Fin n → Bool} (y : PCoord ε → ℂ) : Jm ε * pmat y * Jm ε = -pmat y := by
  ext a b
  rw [dpb_JWJ]
  split_ifs with h
  · have : pmat y a b = 0 := by simp [pmat, h]
    rw [Matrix.neg_apply, this, neg_zero]
  · rw [Matrix.neg_apply]

theorem dpb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

theorem dpb_shc_fac : (fun u : ℝ => u * ((shc u - 1) / u)) = fun u => shc u - 1 := by
  funext u
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h]
    field_simp

theorem dpb_theta_ad {J Y : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hY : J * Y * J = -Y)
    (W : Matrix (Fin n) (Fin n) ℂ) : J * (Y * W - W * Y) * J = -(Y * (J * W * J) - (J * W * J) * Y) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J := by
    intro A B
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]
  simp only [neg_mul, mul_neg]
  abel

theorem dpb_det {ε : Fin n → Bool} {U : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hY : Jm ε * (U * dpbD x * Uᴴ) * Jm ε = -(U * dpbD x * Uᴴ)) :
    LinearMap.det (dpbL U x shc) = LinearMap.det (dpbP ε ∘ₗ dpbL U x shc ∘ₗ dpbE ε) ^ 4 := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Jm ε * W * Jm ε
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Wᴴ
      map_add' := fun W W' => Matrix.conjTranspose_add W W'
      map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }
  let ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Complex.I • W
      map_add' := fun W W' => smul_add _ _ _
      map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  let N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c W => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  let C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) := dpbL U x (fun u => (shc u - 1) / u)
  have hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1) := by
    rw [dpb_shc_fac]
  refine dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]
  · intro v
    show (vᴴ)ᴴ = v
    exact Matrix.conjTranspose_conjTranspose v
  · intro v
    show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
  · intro v
    show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)
    exact dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v
  · intro v
    show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ
    exact dpbH_conjTranspose U x shc dpb_shc_neg v
  · intro v
    show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v -
      dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v
    rw [dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) =
      dpbH U x shc v - v
    rw [dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε =
      -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))
    exact dpb_theta_ad hJJ hY v
  · intro v
    show Complex.I • (Complex.I • v) = -v
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  · intro v
    show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)
    exact (dpbH_smul U x shc Complex.I v).symm
  · intro v
    show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · intro v
    show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · intro v
    exact dpbE_P v
  · intro w
    exact dpbP_E w

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PolarJacobianDeterminant

theorem prod_shc_sq_eq_Jac_pow {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = Jac z ^ 4 := by
  set f : Fin n → Fin n → ℝ := fun i j => shc (pev z i - pev z j) with hf
  have hsym : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]; rw [← neg_sub, PolarJacobianDeterminant.shc_neg]
  have hpt : ∀ i j, f i j = (if i < j then f i j else 1) * (if j < i then f i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst h; simp [hf, shc]
    · simp [h, not_lt_of_gt h]
  have hswap : ∏ i, ∏ j, (if j < i then f i j else 1) = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [hsym]
  have hJ : Jac z = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    simp only [Jac, Finset.prod_filter, hf]
  have hall : ∏ i, ∏ j, f i j = Jac z ^ 2 := by
    calc ∏ i, ∏ j, f i j
          = ∏ i, ∏ j, ((if i < j then f i j else 1) * (if j < i then f i j else 1)) :=
          Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hpt i j
      _ = (∏ i, ∏ j, (if i < j then f i j else 1)) * ∏ i, ∏ j, (if j < i then f i j else 1) := by
          simp only [Finset.prod_mul_distrib]
      _ = Jac z ^ 2 := by rw [hswap, ← hJ, sq]
  have : ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = (∏ i, ∏ j, f i j) ^ 2 := by
    simp only [hf, Finset.prod_pow]
  rw [this, hall, ← pow_mul]

theorem fderiv_shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    fderiv ℝ (shcAdC y) 0 = LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y) := by
  have : shcAdC y = ⇑(LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y)) := by
    funext w; rfl
  rw [this]
  exact ContinuousLinearMap.fderiv _

end PolarJacobianDeterminant

theorem detP {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) = Jac y := by
  have h4 := (detPb y).symm.trans ((detPa y).trans (PolarJacobianDeterminant.prod_shc_sq_eq_Jac_pow y))
  have hpos : 0 < LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) := by
    rw [PolarJacobianDeterminant.fderiv_shcAdC, LinearMap.coe_toContinuousLinearMap]
    exact PolarJacobianDeterminant.det_shcAdCL_pos y
  have hJ : 0 ≤ Jac y := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    (PolarJacobianDeterminant.shc_pos _).le
  exact (pow_left_inj₀ hpos.le hJ (by norm_num)).mp h4

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

namespace JacB

section Gen

variable {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

theorem contDiff_exp_alg : ContDiff ℝ 1 (NormedSpace.exp : 𝔸 → 𝔸) := by
  first
  | exact contDiff_exp
  | exact NormedSpace.contDiff_exp
  | exact (NormedSpace.analyticOnNhd_exp (𝕂 := ℝ)).contDiff
  | exact (analyticOnNhd_exp (𝕂 := ℝ)).contDiff
  | exact contDiff_iff_contDiffAt.mpr fun x =>
      (analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (by simp [expSeries_radius_eq_top])).contDiffAt
  | exact contDiff_iff_contDiffAt.mpr fun x =>
      (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (by simp [NormedSpace.expSeries_radius_eq_top])).contDiffAt

theorem hasFDerivAt_exp_alg (x : 𝔸) :
    HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸) (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) x) x := by
  first
  | exact ((contDiff_exp_alg (𝔸 := 𝔸)).differentiable one_ne_zero x).hasFDerivAt
  | exact ((contDiff_exp_alg (𝔸 := 𝔸)).differentiable le_rfl x).hasFDerivAt

theorem fderiv_exp_eq {x W D : 𝔸} (h : HasDerivAt (fun s : ℝ => NormedSpace.exp (x + s • W)) D 0) :
    fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) x W = D := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add x
  have h2 := (hasFDerivAt_exp_alg (x + (0 : ℝ) • W)).comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, add_zero] at h2
  exact h2.unique h

theorem contDiffAt_of_exp [FiniteDimensional ℝ 𝔸] {f : E → 𝔸} {z : E} (hf : ContinuousAt f z)
    (hg : ContDiffAt ℝ 1 (fun w => NormedSpace.exp (f w)) z)
    (hi : Function.Injective (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z))) :
    ContDiffAt ℝ 1 f z := by
  let e : 𝔸 ≃L[ℝ] 𝔸 :=
    (LinearEquiv.ofInjectiveEndo
      (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z) : 𝔸 →ₗ[ℝ] 𝔸) hi).toContinuousLinearEquiv
  have he : (e : 𝔸 →L[ℝ] 𝔸) = fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z) := by
    ext v; rfl
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸) (e : 𝔸 →L[ℝ] 𝔸) (f z) := by
    rw [he]; exact hasFDerivAt_exp_alg _
  have hc : ContDiffAt ℝ 1 (NormedSpace.exp : 𝔸 → 𝔸) (f z) := contDiff_exp_alg.contDiffAt
  have h1 := hc.to_localInverse hd one_ne_zero
  have h2 := (hc.hasStrictFDerivAt' hd one_ne_zero).eventually_left_inverse
  have h3 := ContDiffAt.comp z (g := hc.localInverse hd one_ne_zero) h1 hg
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hf.eventually h2] with w hw
  exact hw.symm

end Gen

variable {n : ℕ}

theorem shc_pos' (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hu | hu
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hu) hu
    · exact div_pos (Real.sinh_pos_iff.mpr hu) hu

theorem jac_pos' {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 < Jac y := by
  unfold Jac
  exact Finset.prod_pos (fun a _ => Finset.prod_pos (fun b _ => shc_pos' _))

def pmatLin (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def crdLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun X := fun ab => X ab.1.1 ab.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem crd_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : crdLin ε (pmat z) = z := by
  funext ab
  show pmat z ab.1.1 ab.1.2 = z ab
  simp only [pmat]
  rw [dif_pos ab.2]

def shcAdLin {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := shcAd y
  map_add' V W := by
    unfold shcAd
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    ext i j
    simp only [Matrix.add_mul, Matrix.add_apply, Matrix.of_apply, mul_add]
  map_smul' c W := by
    unfold shcAd
    rw [RingHom.id_apply, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.of_apply, mul_smul_comm]

theorem shcAd_eq_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) {W : Matrix (Fin n) (Fin n) ℂ}
    (h : shcAd y W = 0) : W = 0 := by
  unfold shcAd at h
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have h2 : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  set S := Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) with hS
  have h3 : S = 0 := by
    have : Uᴴ * (U * S * Uᴴ) * U = S := by
      calc Uᴴ * (U * S * Uᴴ) * U = (Uᴴ * U) * S * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [← this, h, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : Uᴴ * W * U = 0 := by
    ext i j
    have h5 : S i j = 0 := by rw [h3]; rfl
    rw [hS, Matrix.of_apply, mul_eq_zero] at h5
    rcases h5 with h5 | h5
    · exact absurd (Complex.ofReal_eq_zero.1 h5) (shc_pos' _).ne'
    · exact h5
  calc W = (U * Uᴴ) * W * (U * Uᴴ) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * W * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h4, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_two (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp ((2 : ℝ) • X) = NormedSpace.exp X * NormedSpace.exp X := by
  rw [two_smul]
  first
  | exact Matrix.exp_add_of_commute _ _ (Commute.refl X)
  | exact Matrix.exp_add_of_commute (Commute.refl X)
  | exact NormedSpace.exp_add_of_commute (Commute.refl X)

theorem exp_two_actR {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (z : PCoord ε → ℂ) :
    NormedSpace.exp ((2 : ℝ) • pmat (actR g z)) = gᴴ * NormedSpace.exp ((2 : ℝ) • pmat z) * g := by
  obtain ⟨k, hk⟩ := actR_spec hg z
  have hk1 : (toMK k)ᴴ * toMK k = 1 := k.2.1.1
  have hz : (NormedSpace.exp (pmat z))ᴴ = NormedSpace.exp (pmat z) := (pmat_isHermitian z).exp
  have hw : (NormedSpace.exp (pmat (actR g z)))ᴴ = NormedSpace.exp (pmat (actR g z)) :=
    (pmat_isHermitian _).exp
  have h1 : (NormedSpace.exp (pmat z) * g)ᴴ * (NormedSpace.exp (pmat z) * g) =
      (toMK k * NormedSpace.exp (pmat (actR g z)))ᴴ * (toMK k * NormedSpace.exp (pmat (actR g z))) := by
    rw [hk]; rfl
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hz, hw, Matrix.mul_assoc _ (toMK k)ᴴ,
    ← Matrix.mul_assoc (toMK k)ᴴ, hk1, Matrix.one_mul] at h1
  rw [exp_two, exp_two, ← h1]
  simp only [Matrix.mul_assoc]

section Op

open scoped Matrix.Norms.Operator

def pmatC (ε : Fin n → Bool) : (PCoord ε → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (pmatLin ε)

def crdC (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (PCoord ε → ℂ) :=
  LinearMap.toContinuousLinearMap (crdLin ε)

theorem pmat_contDiff (ε : Fin n → Bool) : ContDiff ℝ 1 (fun z : PCoord ε → ℂ => pmat z) := by
  first
  | exact (pmatC ε).contDiff
  | exact ContinuousLinearMap.contDiff (pmatC ε)

theorem actR_continuous {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Continuous (actR (ε := ε) g) := by
  choose k hk using actR_spec hg
  have h1 : Continuous (fun z => (k z, actR g z)) := by
    rw [(polarM_isClosedEmbedding ε).isEmbedding.continuous_iff]
    have h2 : (polarM ∘ fun z => (k z, actR g z)) = fun z => NormedSpace.exp (pmat z) * g := by
      funext z; exact (hk z).symm
    rw [h2]
    exact ((contDiff_exp_alg.comp (pmat_contDiff ε)).mul contDiff_const).continuous
  exact continuous_snd.comp h1

theorem fderiv_exp_two {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) W = NormedSpace.exp (pmat y) * shcAd y W * NormedSpace.exp (pmat y) := by
  apply fderiv_exp_eq
  have h := hasDerivAt_exp_two y W
  have e : (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • pmat y + (s : ℂ) • W)) =
      fun s : ℝ => NormedSpace.exp ((2 : ℝ) • pmat y + s • W) := by
    funext s
    rw [two_smul, two_smul, Complex.coe_smul]
  rw [e] at h
  exact h

theorem conj_cancel {A B X : Matrix (Fin n) (Fin n) ℂ}
    (h : NormedSpace.exp X * A * NormedSpace.exp X = NormedSpace.exp X * B * NormedSpace.exp X) :
    A = B := by
  have hu : IsUnit (NormedSpace.exp X) := Matrix.isUnit_exp X
  exact hu.mul_left_cancel (hu.mul_right_cancel h)

theorem fderiv_exp_two_inj {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Function.Injective (fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y)) := by
  intro W1 W2 hW
  have h0 : fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) (W1 - W2) = 0 := by
    rw [map_sub, hW, sub_self]
  rw [fderiv_exp_two] at h0
  have h1 : shcAd y (W1 - W2) = 0 :=
    conj_cancel (X := pmat y) (by rw [h0, Matrix.mul_zero, Matrix.zero_mul])
  exact sub_eq_zero.mp (shcAd_eq_zero y h1)

theorem actR_contDiff' {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ContDiff ℝ 1 (actR (ε := ε) g) := by
  have h1 : ContDiff ℝ 1 (fun z : PCoord ε → ℂ => (2 : ℝ) • pmat (actR g z)) := by
    refine contDiff_iff_contDiffAt.2 fun z => contDiffAt_of_exp ?_ ?_ (fderiv_exp_two_inj _)
    · exact (((pmat_contDiff ε).continuous.comp (actR_continuous hg)).const_smul (2 : ℝ)).continuousAt
    · exact (((contDiff_const (c := gᴴ)).mul
        (contDiff_exp_alg.comp ((pmat_contDiff ε).const_smul (2 : ℝ)))).mul
        (contDiff_const (c := g))).contDiffAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => exp_two_actR hg w)
  have h2 := ((crdC ε).contDiff.comp h1).const_smul (1 / 2 : ℝ)
  convert h2 using 1
  funext z
  change actR g z = (1 / 2 : ℝ) • crdLin ε ((2 : ℝ) • pmat (actR g z))
  rw [map_smul, crd_pmat, smul_smul]
  norm_num

theorem shcAd_fderiv_actR {ε : Fin n → Bool} (y v : PCoord ε → ℂ) :
    shcAd y (pmat (fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 v)) = pmat v := by
  have hg := exp_pmat_inUJ y
  have hY : (NormedSpace.exp (pmat y))ᴴ = NormedSpace.exp (pmat y) := (pmat_isHermitian y).exp
  have hD := ((actR_contDiff' hg).differentiable one_ne_zero 0).hasFDerivAt
  set D := fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0
  have h1 := ((pmatC ε).hasFDerivAt.comp 0 hD).const_smul (2 : ℝ)
  have h2 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        ((2 : ℝ) • pmat y)) ((2 : ℝ) • pmat (actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ))) := by
    rw [actR_exp_zero]; exact hasFDerivAt_exp_alg _
  have h3 := HasFDerivAt.comp (0 : PCoord ε → ℂ) h2 h1
  have h4 := ((pmatC ε).hasFDerivAt (x := 0)).const_smul (2 : ℝ)
  have h5 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
        ((2 : ℝ) • pmatC ε (0 : PCoord ε → ℂ)) := by
    rw [map_zero, smul_zero]; exact hasFDerivAt_exp_zero
  have h6 := ((HasFDerivAt.comp (0 : PCoord ε → ℂ) h5 h4).const_mul
    (NormedSpace.exp (pmat y))).mul_const' (NormedSpace.exp (pmat y))
  have h7 := h3.unique (h6.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
    have := exp_two_actR hg z
    rw [hY] at this
    exact this))
  have h8 := congrArg (fun T => T v) h7
  have h9 : fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) ((2 : ℝ) • pmat (D v)) =
      NormedSpace.exp (pmat y) * ((2 : ℝ) • pmat v) * NormedSpace.exp (pmat y) := h8
  rw [fderiv_exp_two] at h9
  have h10 : shcAdLin y ((2 : ℝ) • pmat (D v)) = (2 : ℝ) • pmat v := conj_cancel h9
  rw [map_smul] at h10
  exact smul_right_injective _ (two_ne_zero (α := ℝ)) h10

end Op

theorem jacBase' {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac y = 1 := by
  let S : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ) :=
    LinearMap.toContinuousLinearMap (crdLin ε ∘ₗ shcAdLin y ∘ₗ pmatLin ε)
  have hS : fderiv ℝ (shcAdC y) 0 = S := S.fderiv
  have h1 := detP y
  rw [hS] at h1
  set D := fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 with hD
  have h2 : (S : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) ∘ₗ (D : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) =
      LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change crdLin ε (shcAd y (pmat (D v))) = v
    rw [hD, shcAd_fderiv_actR, crd_pmat]
  have h3 := congrArg LinearMap.det h2
  rw [LinearMap.det_comp, LinearMap.det_id, h1] at h3
  rw [← abs_of_pos (jac_pos' y), ← abs_mul, mul_comm, h3, abs_one]

end JacB

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace



end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jall_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem jall_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

def adKL {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, jall_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, jall_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, Pi.smul_apply, Matrix.smul_apply,
      RingHom.id_apply, Complex.real_smul, smul_eq_mul]

theorem jall_adK_inv {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : adK k⁻¹ (adK k z) = z := by
  have hk := toMK_facts k
  have h : pmat (adK k⁻¹ (adK k z)) = pmat z := by
    rw [pmat_adK, pmat_adK, toMK_inv, Matrix.conjTranspose_conjTranspose]
    calc (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ) * toMK k
        = ((toMK k)ᴴ * toMK k) * pmat z * ((toMK k)ᴴ * toMK k) := by simp only [Matrix.mul_assoc]
      _ = pmat z := by rw [hk.1, Matrix.one_mul, Matrix.mul_one]
  rw [← pact_pmat_coords (adK k⁻¹ (adK k z)), h, pact_pmat_coords]

theorem jall_abs_det_adKL {ε : Fin n → Bool} (k : KG ε) : |LinearMap.det (adKL k)| = 1 := by
  have hinj : Function.Injective (adKL k) := fun x y hxy => by
    have := congrArg (adK k⁻¹) hxy
    simpa only [adKL, LinearMap.coe_mk, AddHom.coe_mk, jall_adK_inv] using this
  have hmp := adK_measurePreserving k
  have hcs : IsCompact ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    (isCompact_closedBall 0 1).image (LinearMap.continuous_of_finiteDimensional _)
  have h1 : volume ((adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1)) =
      volume ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    hmp.measure_preimage hcs.isClosed.measurableSet.nullMeasurableSet
  have hpre : (adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) =
      Metric.closedBall (0 : PCoord ε → ℂ) 1 := Set.preimage_image_eq _ hinj
  rw [hpre, MeasureTheory.Measure.addHaar_image_linearMap] at h1
  have hpos : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hfin : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : PCoord ε → ℂ) 1).measure_lt_top.ne
  have h2 : ENNReal.ofReal |LinearMap.det (adKL k)| = 1 := by
    have h3 : 1 * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) =
        ENNReal.ofReal |LinearMap.det (adKL k)| * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).mp h3).symm
  exact ENNReal.ofReal_eq_one.mp h2

def jdetA {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : ℝ :=
  LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
    (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))

theorem jall_diff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    DifferentiableAt ℝ (actR (ε := ε) g) z := by
  first
  | exact (JacB.actR_contDiff' hg).differentiable one_ne_zero z
  | exact (JacB.actR_contDiff' hg).differentiable le_rfl z

theorem jall_chain {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : jdetA (g * h) z = jdetA h (actR g z) * jdetA g z := by
  unfold jdetA
  have hfun : actR (ε := ε) (g * h) = actR h ∘ actR g := funext (actR_mul hg hh)
  rw [hfun, fderiv_comp z (jall_diff hh (actR g z)) (jall_diff hg z)]
  exact LinearMap.det_comp _ _

theorem jall_fderiv_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    fderiv ℝ (actR (ε := ε) (toMK k)) z = LinearMap.toContinuousLinearMap (adKL k⁻¹) := by
  have e : actR (ε := ε) (toMK k) = ⇑(LinearMap.toContinuousLinearMap (adKL k⁻¹)) := by
    funext w
    rw [actR_K]
    rfl
  rw [e]
  exact ContinuousLinearMap.fderiv _

theorem jall_abs_jdetA_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    |jdetA (toMK k) z| = 1 := by
  unfold jdetA
  rw [jall_fderiv_K]
  exact jall_abs_det_adKL k⁻¹

theorem jall_inUJ_K {ε : Fin n → Bool} (k : KG ε) : inUJ ε (toMK k) := by
  first
  | exact k.1.2
  | exact k.val.property
  | exact k.2.1

theorem jall_actR_K_zero {ε : Fin n → Bool} (k : KG ε) : actR (ε := ε) (toMK k) 0 = 0 := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  apply actR_of_eq_polarM (k := k)
  simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]

theorem jacAll {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac (actR g z) = Jac z := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  obtain ⟨k, hk⟩ := actR_spec hg z
  set w := actR g z with hw
  have hEz := exp_pmat_inUJ z
  have hEw := exp_pmat_inUJ w
  have hK := jall_inUJ_K k
  have h0z : actR (ε := ε) (NormedSpace.exp (pmat z)) 0 = z := by
    apply actR_of_eq_polarM (k := 1)
    simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul]
    first
    | rfl
    | (rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.one_mul])
    | simp
  have hc1 := jall_chain hEz hg 0
  rw [h0z] at hc1
  have hc2 := jall_chain hK hEw 0
  rw [jall_actR_K_zero] at hc2
  have hmul : NormedSpace.exp (pmat z) * g = toMK k * NormedSpace.exp (pmat w) := by
    rw [hk]; rfl
  rw [hmul, hc2] at hc1
  have hab : |jdetA g z| * |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| = |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| := by
    have := congrArg abs hc1
    rw [abs_mul, abs_mul, jall_abs_jdetA_K, mul_one] at this
    rw [this, mul_comm]
  have hbZ : |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| * Jac z = 1 := JacB.jacBase' z
  have hcW : |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| * Jac w = 1 := JacB.jacBase' w
  show |jdetA g z| * Jac w = Jac z
  linear_combination (-(|jdetA g z| * Jac w)) * hbZ + (Jac w * Jac z) * hab + Jac z * hcW

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inv_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inUJ ε (Jm ε * gᴴ * Jm ε) ∧ (Jm ε * gᴴ * Jm ε) * g = 1 ∧ g * (Jm ε * gᴴ * Jm ε) = 1 := by
  have hJ : Jm ε * Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hg' : gᴴ * (Jm ε * g) = Jm ε := by
    unfold inUJ at hg
    rw [← Matrix.mul_assoc]; exact hg
  have h1 : Jm ε * gᴴ * Jm ε * g = 1 := by
    simp only [Matrix.mul_assoc]; rw [hg', hJ]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp h1
    | exact Matrix.mul_eq_one_comm.mp h1
    | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h1
  have h3 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * (Jm ε * (gᴴ * X)) = Jm ε * X := fun X => by
    calc g * (Jm ε * (gᴴ * X)) = g * (Jm ε * gᴴ * Jm ε) * (Jm ε * X) := by
          simp only [Matrix.mul_assoc, hJJ]
      _ = Jm ε * X := by rw [h2, Matrix.one_mul]
  refine ⟨?_, h1, h2⟩
  unfold inUJ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, Matrix.mul_assoc, hJJ, h3]

theorem coreP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Measure.map (actR (ε := ε) g) (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) =
      volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z) := by
  obtain ⟨hh, hhg, hgh⟩ := inv_inUJ hg
  set h := Jm ε * gᴴ * Jm ε with hdef
  have hleft : ∀ z, actR (ε := ε) h (actR g z) = z := fun z => by
    rw [← actR_mul hg hh, hgh, actR_one]
  have hright : ∀ z, actR (ε := ε) g (actR h z) = z := fun z => by
    rw [← actR_mul hh hg, hhg, actR_one]
  have hmeas : Measurable (actR (ε := ε) g) := (JacB.actR_continuous hg).measurable
  ext A hA
  rw [Measure.map_apply hmeas hA, withDensity_apply _ hA, withDensity_apply _ (hmeas hA)]
  have himg : actR (ε := ε) g '' (actR g ⁻¹' A) = A :=
    Set.image_preimage_eq A (fun y => ⟨actR h y, hright y⟩)
  calc ∫⁻ z in actR g ⁻¹' A, ENNReal.ofReal (Jac z)
        = ∫⁻ z in actR g ⁻¹' A, ENNReal.ofReal |(fderiv ℝ (actR (ε := ε) g) z).det| *
            ENNReal.ofReal (Jac (actR g z)) := by
          refine lintegral_congr (fun z => ?_)
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          rw [← jacAll hg z]
    _ = ∫⁻ z in actR g '' (actR g ⁻¹' A), ENNReal.ofReal (Jac z) :=
          (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hmeas hA)
            (fun z _ => (jall_diff hg z).hasFDerivAt.hasFDerivWithinAt)
            (fun x _ y _ hxy => by rw [← hleft x, hxy, hleft y]) (fun z => ENNReal.ofReal (Jac z))).symm
    _ = ∫⁻ z in A, ENNReal.ofReal (Jac z) := by rw [himg]

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def rmulPR (G : Matrix (Fin n) (Fin n) ℂ) (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) * G

def polarPR {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : Fin n → Fin n → ℂ := polarM kz

theorem continuous_rmulPR (G : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulPR G) := by
  unfold rmulPR
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * G)

theorem measurable_polarPR (ε : Fin n → Bool) : Measurable (polarPR (ε := ε)) := by
  have h : Continuous (polarPR (ε := ε)) := polarM_continuous ε
  exact h.measurable

theorem rmulPR_polarPR {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G)
    (z : PCoord ε → ℂ) : ∃ k' : KG ε, ∀ k : KG ε,
      rmulPR G (polarPR (k, z)) = polarPR (k * k', actR G z) := by
  have hE : inUJ ε (NormedSpace.exp (pmat z)) := exp_pmat_inUJ z
  have hEG : inUJ ε (NormedSpace.exp (pmat z) * G) := by
    unfold inUJ at hE hG ⊢
    rw [Matrix.conjTranspose_mul]
    calc Gᴴ * (NormedSpace.exp (pmat z))ᴴ * Jm ε * (NormedSpace.exp (pmat z) * G)
        = Gᴴ * ((NormedSpace.exp (pmat z))ᴴ * Jm ε * NormedSpace.exp (pmat z)) * G := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hE, hG]
  obtain ⟨⟨k', w⟩, hkw⟩ := polarM_surj _ hEG
  have hw : actR G z = w := by
    funext ab
    have h1 : plog (NormedSpace.exp (pmat z) * G) = pmat w := by
      rw [← hkw, plog_polarM]
    simp only [actR, h1, pmat, dif_pos ab.2]
  refine ⟨k', fun k => ?_⟩
  rw [hw]
  simp only [rmulPR, polarPR, polarM] at hkw ⊢
  have hm : toMK (k * k') = toMK k * toMK k' := rfl
  show toMK k * NormedSpace.exp (pmat z) * G = _
  rw [Matrix.mul_assoc, ← hkw, hm, Matrix.mul_assoc]

theorem muPolarMat_mul_right (ε : Fin n → Bool) {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G) :
    Measure.map (rmulPR G) (muPolarMat ε) = muPolarMat ε := by
  have hP : Measurable (polarPR (ε := ε)) := measurable_polarPR ε
  have hR : Measurable (rmulPR G) := (continuous_rmulPR G).measurable
  have hA : Measurable (actR (ε := ε) G) := (JacB.actR_continuous hG).measurable
  have hc := coreP hG

  have key : ∀ S : Set (Fin n → Fin n → ℂ), MeasurableSet S →
      muPolarMat ε S = ∫⁻ z, dk ε {k | polarPR (k, z) ∈ S}
        ∂(volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    intro S hS
    show (Measure.map (polarPR (ε := ε)) ((dk ε).prod
      (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))) S = _
    rw [Measure.map_apply hP hS, Measure.prod_apply_symm (hP hS)]
    rfl
  ext S hS
  rw [Measure.map_apply hR hS, key _ (hR hS), key _ hS]
  have step : ∀ z : PCoord ε → ℂ, dk ε {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
      dk ε {k | polarPR (k, actR G z) ∈ S} := by
    intro z
    obtain ⟨k', hk'⟩ := rmulPR_polarPR hG z
    have hset : {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
        (fun k => k * k') ⁻¹' {k | polarPR (k, actR G z) ∈ S} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hk']
    rw [hset, measure_preimage_mul_right]
  simp_rw [step]
  have hφ : Measurable fun w : PCoord ε → ℂ => dk ε {k | polarPR (k, w) ∈ S} :=
    measurable_measure_prodMk_right (hP hS)
  rw [← lintegral_map hφ hA, hc]

theorem muPolar_mul_right (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muPolar ε) = muPolar ε := by
  show Measure.map (fun x => x * g) (Measure.comap (intMuCD_eM ε) (muPolarMat ε)) =
    Measure.comap (intMuCD_eM ε) (muPolarMat ε)
  by_cases h : Function.Injective (intMuCD_eM ε) ∧
      ∀ s, MeasurableSet s → NullMeasurableSet (intMuCD_eM ε '' s) (muPolarMat ε)
  swap
  · simp only [Measure.comap, dif_neg h, Measure.map_zero]
  haveI : BorelSpace (UJ ε) := ⟨rfl⟩
  have hRm : Measurable (fun x : UJ ε => x * g) := (continuous_mul_right g).measurable
  have hG : inUJ ε (toM g) := g.2
  have h4 := muPolarMat_mul_right ε hG
  have hRM : Measurable (rmulPR (toM g)) := (continuous_rmulPR (toM g)).measurable
  ext S hS
  rw [Measure.map_apply hRm hS, Measure.comap_apply₀ _ _ h.1 h.2 (hRm hS).nullMeasurableSet,
    Measure.comap_apply₀ _ _ h.1 h.2 hS.nullMeasurableSet]
  have h1 : toM g * toM g⁻¹ = 1 := by
    rw [show toM g * toM g⁻¹ = toM (g * g⁻¹) from rfl, mul_inv_cancel]
    rfl
  have himg : intMuCD_eM ε '' ((fun x => x * g) ⁻¹' S) =
      rmulPR (toM g) ⁻¹' (intMuCD_eM ε '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * g, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y * g⁻¹, ?_, ?_⟩
      · show y * g⁻¹ * g ∈ S
        rw [inv_mul_cancel_right]
        exact hy
      · have hx : toM y = Matrix.of x * toM g := hxy
        show toM y * toM g⁻¹ = x
        rw [hx, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
  rw [himg, ← Measure.map_apply₀ hRM.aemeasurable (by rw [h4]; exact h.2 S hS), h4]

end ReciprocityTheory.ChartRestriction.DS
end
end
