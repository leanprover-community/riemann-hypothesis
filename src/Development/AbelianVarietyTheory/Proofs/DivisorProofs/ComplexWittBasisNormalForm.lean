import Mathlib
import BuildAid.ForwardExisting

section
section
open scoped ComplexOrder
open Matrix

namespace GlobalTheory

open scoped ComplexOrder in
open Matrix in

theorem _root_.GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  intro n d J P X Y y₀ hJ hP hXX hYY hXY hPX hPY k hk m G
  have hki : (k⁻¹).1 = k.1ᴴ := by
    calc (k⁻¹).1 = (k.1ᴴ * k.1) * (k⁻¹).1 := by rw [hk, Matrix.one_mul]
      _ = k.1ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hm : m.1 = y₀.1 * k.1 * (y₀⁻¹).1 := by simp [m]
  have hmi : (m⁻¹).1 = y₀.1 * k.1ᴴ * (y₀⁻¹).1 := by
    simp only [m, _root_.mul_inv_rev, inv_inv, Units.val_mul, hki, Matrix.mul_assoc]
  have hab : y₀.1ᴴ * (y₀⁻¹).1ᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hAm : m.1ᴴ * ((y₀⁻¹).1ᴴ * (y₀⁻¹).1) * m.1 = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [hm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y₀.1ᴴ, hab, Matrix.one_mul, ← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hBm : (m⁻¹).1 * (y₀.1 * y₀.1ᴴ) * (m⁻¹).1ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [hmi]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc y₀.1ᴴ, hab,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hAh : ((y₀⁻¹).1ᴴ * (y₀⁻¹).1)ᴴ = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : (y₀.1 * y₀.1ᴴ)ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [G]
  generalize (y₀⁻¹).1ᴴ * (y₀⁻¹).1 = A at hPX hAm hAh
  generalize y₀.1 * y₀.1ᴴ = B at hPY hBm hBh
  generalize m.1 = m₁ at hAm
  generalize (m⁻¹).1 = m₂ at hBm
  have hYX : Yᴴ * J * X = 1 := by
    have h := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using h
  have hXP : Xᴴ * P = A * (Yᴴ * J) := by
    have h := congrArg conjTranspose hPX
    simpa [conjTranspose_mul, hJ, hP, hAh, Matrix.mul_assoc] using h
  have hYP : Yᴴ * P = B * (Xᴴ * J) := by
    have h := congrArg conjTranspose hPY
    simpa [conjTranspose_mul, hJ, hP, hBh, Matrix.mul_assoc] using h
  have r1 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (X * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have r2 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (Y * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have r3 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (Y * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have r4 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (X * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have r5 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (X * Z) = J * (Y * (A * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPX]
  have r6 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (Y * Z) = J * (X * (B * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPY]
  have r7 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Xᴴ * (P * Z) = A * (Yᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hXP]
  have r8 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Yᴴ * (P * Z) = B * (Xᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hYP]
  have r9 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₁ᴴ * (A * (m₁ * Z)) = A * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hAm]
  have r10 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₂ * (B * (m₂ᴴ * Z)) = B * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hBm]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hXP, hYP,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero, zero_add]
  abel

end GlobalTheory
end

open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  atlas_forward_decl GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj
end

section
section
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory

open Matrix

theorem posDef_exists_conjTranspose_mul_mul_eq_one :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]

end GlobalTheory
end
end

open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  atlas_forward_decl GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one
end

section
section
open scoped ComplexOrder
open Matrix

namespace GlobalTheory

theorem radical_elt_moving_dual_to_majorant (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.conjTranspose = J) (hθ : θ * θ = 1) (hQ : (J * θ).PosDef)
    (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ) (hXX : X₂.conjTranspose * J * X₂ = 0)
    (hYY : Y₂.conjTranspose * J * Y₂ = 0) (hXY : X₂.conjTranspose * J * Y₂ = 1) :
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  have hθJ : θᴴ * J = J * θ := by
    have := hQ.isHermitian.eq
    rwa [conjTranspose_mul, hJ] at this
  have hYX : Y₂ᴴ * J * X₂ = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hinj : Function.Injective X₂.mulVec := by
    intro a b hab
    have := congrArg (fun v => (Y₂ᴴ * J).mulVec v) hab
    simpa [Matrix.mulVec_mulVec, hYX] using this
  have hP : (X₂ᴴ * (J * θ) * X₂).PosDef := hQ.conjTranspose_mul_mul_same hinj
  obtain ⟨P, hPdef⟩ : ∃ P, P = X₂ᴴ * (J * θ) * X₂ := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPiH : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.isHermitian.eq]
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = θ * X₂ * P⁻¹ := ⟨_, rfl⟩
  have hXY' : X₂ᴴ * J * Y' = 1 := by
    rw [← hPPi, hY', hPdef]; simp only [Matrix.mul_assoc]
  have hY'Y' : Y'ᴴ * J * Y' = 0 := by
    have h1 : ∀ B : Matrix (Fin n) (Fin p) ℂ, θᴴ * (J * (θ * B)) = J * B := by
      intro B
      rw [← Matrix.mul_assoc, hθJ, Matrix.mul_assoc, ← Matrix.mul_assoc θ, hθ, Matrix.one_mul]
    have h2 : X₂ᴴ * (J * (X₂ * P⁻¹)) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
    rw [hY']
    simp only [conjTranspose_mul, hPiH, Matrix.mul_assoc, h1, h2, Matrix.mul_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Y' - Y₂ := ⟨_, rfl⟩
  have hXD : X₂ᴴ * J * D = 0 := by rw [hD, Matrix.mul_sub, hXY', hXY, sub_self]
  have hDX : Dᴴ * J * X₂ = 0 := by
    have := congrArg conjTranspose hXD
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hkey : Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D = 0 := by
    rw [hD]
    simp only [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] at hY'Y' hYY ⊢
    rw [hY'Y', hYY]
    abel

  have tXX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have tXD : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (D * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXD, Matrix.zero_mul]
  have tDX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), Dᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have tXY : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (Y₂ * B)) = B := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have hXX' : X₂ᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hXX]
  have hXD' : X₂ᴴ * (J * D) = 0 := by rw [← Matrix.mul_assoc, hXD]
  have hDX' : Dᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hDX]
  have hXY'' : X₂ᴴ * (J * Y₂) = 1 := by rw [← Matrix.mul_assoc, hXY]
  obtain ⟨E, hE⟩ : ∃ E, E = Dᴴ * J * Y₂ := ⟨_, rfl⟩
  have hE' : Dᴴ * (J * Y₂) = E := by rw [hE, Matrix.mul_assoc]
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ,
      u = 1 + (D * X₂ᴴ * J - X₂ * Dᴴ * J + X₂ * E * X₂ᴴ * J) := ⟨_, rfl⟩
  have huJ : uᴴ * J * u = J := by
    have hexp : uᴴ * J * u = J + J * X₂ * (Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D) * X₂ᴴ * J := by
      rw [hu, hE]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_one,
        conjTranspose_conjTranspose, hJ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, tXX, tXD, tDX,
        hXX', hXD', hDX', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]
      abel
    rw [hexp, hkey]; simp
  have huX : u * X₂ = X₂ := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXX', hDX',
      Matrix.mul_zero, add_zero, sub_zero]
  have huY : u * Y₂ = Y' := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXY'',
      Matrix.mul_one, hE']
    rw [hD]; abel
  have hdetJ : J.det ≠ 0 := by
    intro h0
    have := hQ.det_pos
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact lt_irrefl _ this
  have hudet : IsUnit u.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetJ ?_
    have := congrArg Matrix.det huJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have huU : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).mpr hudet
  refine ⟨huU.unit, ?_, ?_, ?_, ?_⟩
  · simpa using huJ
  · simpa using huX
  · intro v hv
    have hv' : X₂ᴴ *ᵥ (J *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec]; exact hv
    refine ⟨-(Dᴴ *ᵥ (J *ᵥ v)), ?_⟩
    simp only [IsUnit.unit_spec, hu, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero, Matrix.mulVec_neg]
    abel
  · simp only [IsUnit.unit_spec, huY, hY', Matrix.mul_assoc, hPiP, Matrix.mul_one]

end GlobalTheory
end

open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant : ∀ (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → θ * θ = 1 → (J * θ).PosDef →
    ∀ (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ), X₂.conjTranspose * J * X₂ = 0 → Y₂.conjTranspose * J * Y₂ = 0 →
      X₂.conjTranspose * J * Y₂ = 1 →
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 → ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  atlas_forward_decl GlobalTheory.radical_elt_moving_dual_to_majorant
end

section
section
open scoped ComplexOrder

namespace GlobalTheory

open Matrix

theorem levi_element_cpx : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  intro n a b J Q hJ hQ X₁ Y₁ Xb Yb h11 h1b hbb h1Y h1Yb hYbYb hbYb

  have hYb1 : Ybᴴ * J * X₁ = 0 := by
    have := congrArg conjTranspose h1Yb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hYbb : Ybᴴ * J * Xb = 1 := by
    have := congrArg conjTranspose hbYb
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hY1 : Y₁ᴴ * J * X₁ = 1 := by
    have := congrArg conjTranspose h1Y
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this

  have hinj : Function.Injective X₁.mulVec := by
    intro x y hxy
    have := congrArg (fun w => (Y₁ᴴ * J) *ᵥ w) hxy
    simp only [mulVec_mulVec] at this
    simpa [hY1] using this
  set G := X₁ᴴ * Q * X₁ with hG
  have hGpd : G.PosDef := hQ.conjTranspose_mul_mul_same hinj
  have hGu : IsUnit G := hGpd.isUnit
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGu
  set A : Matrix (Fin a) (Fin b) ℂ := -(G⁻¹ * (X₁ᴴ * Q * Xb)) with hA
  set T : Matrix (Fin n) (Fin n) ℂ := X₁ * A * Ybᴴ * J - Yb * Aᴴ * X₁ᴴ * J with hT
  have hT2 : T * T = 0 := by
    simp only [hT, sub_mul, mul_sub]
    have e1 : X₁ * A * Ybᴴ * J * (X₁ * A * Ybᴴ * J) = X₁ * A * (Ybᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e2 : X₁ * A * Ybᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = X₁ * A * (Ybᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e3 : Yb * Aᴴ * X₁ᴴ * J * (X₁ * A * Ybᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * X₁) * A * Ybᴴ * J := by
      simp only [Matrix.mul_assoc]
    have e4 : Yb * Aᴴ * X₁ᴴ * J * (Yb * Aᴴ * X₁ᴴ * J) = Yb * Aᴴ * (X₁ᴴ * J * Yb) * Aᴴ * X₁ᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2, e3, e4, hYb1, hYbYb, h11, h1Yb]
    simp
  have hTJ : Tᴴ * J = -(J * T) := by
    simp only [hT, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hJ, sub_mul, mul_sub,
      Matrix.mul_assoc, neg_sub]
  let u : GL (Fin n) ℂ := ⟨1 + T, 1 - T, by
      rw [mul_sub, mul_one, add_mul, one_mul, hT2]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hT2]; abel⟩
  refine ⟨u, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (1 + T)ᴴ * J * (1 + T) = J
    rw [conjTranspose_add, conjTranspose_one, add_mul, one_mul, add_mul, mul_add, mul_add, hTJ]
    simp only [mul_one, neg_mul, Matrix.mul_assoc, hT2, mul_zero, neg_zero, add_zero]
    abel
  · show (1 + T) * X₁ = X₁
    have : T * X₁ = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * X₁ = X₁ * A * (Ybᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * X₁ = Yb * Aᴴ * (X₁ᴴ * J * X₁) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYb1, h11]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · show (1 + T) * Xb = Xb + X₁ * A
    have : T * Xb = X₁ * A := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Xb = X₁ * A * (Ybᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Xb = Yb * Aᴴ * (X₁ᴴ * J * Xb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbb, h1b]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this]
  · show (1 + T) * Yb = Yb
    have : T * Yb = 0 := by
      simp only [hT, Matrix.sub_mul]
      have e1 : X₁ * A * Ybᴴ * J * Yb = X₁ * A * (Ybᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      have e2 : Yb * Aᴴ * X₁ᴴ * J * Yb = Yb * Aᴴ * (X₁ᴴ * J * Yb) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hYbYb, h1Yb]; simp
    rw [Matrix.add_mul, Matrix.one_mul, this, add_zero]
  · intro v hv
    show (1 + T) *ᵥ v = v + X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v))
    rw [add_mulVec, one_mulVec]
    congr 1
    simp only [hT, sub_mulVec]
    have e1 : (X₁ * A * Ybᴴ * J) *ᵥ v = X₁ *ᵥ (A *ᵥ ((Ybᴴ * J) *ᵥ v)) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (Yb * Aᴴ * X₁ᴴ * J) *ᵥ v = (Yb * Aᴴ) *ᵥ ((X₁ᴴ * J) *ᵥ v) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [e1, e2, hv, mulVec_zero, sub_zero]
  · rw [Matrix.mul_add]
    have : X₁ᴴ * Q * (X₁ * A) = G * A := by rw [hG]; simp only [Matrix.mul_assoc]
    rw [this, hA, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGdet, Matrix.one_mul]
    simp

end GlobalTheory
end

open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by
  atlas_forward_decl GlobalTheory.levi_element_cpx
end

section
section
open scoped ComplexOrder

namespace GlobalTheory

open Matrix

theorem schur_complement_step_cpx : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  intro n r J θ hJ hpos X Y hXY l d h u₁ A X₁ Xb X₂ Yb Y₂ hθ h0

  let K : Matrix (Fin (l + d)) (Fin d) ℂ := fun i j =>
    Fin.addCases (motive := fun _ => ℂ) (fun i => A i j)
      (fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j) i
  have hK : X₂ * K = Xb + X₁ * A := by
    ext a c
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp only [K, Fin.addCases_left, Fin.addCases_right, Matrix.add_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Matrix.mul_apply]
    rw [add_comm]
    rfl
  have hP : ∀ {m : ℕ} (f : Fin m → Fin (l + d)),
      (X₂.submatrix id f)ᴴ * (J * θ) * (Xb + X₁ * A)
        = (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix f id := fun _ => rfl
  have hrow1 : (X₂ᴴ * (J * θ) * (Xb + X₁ * A)).submatrix (Fin.castAdd d) id = 0 :=
    (hP (Fin.castAdd d)).symm.trans h0
  have key : ∀ P : Matrix (Fin (l + d)) (Fin d) ℂ, P.submatrix (Fin.castAdd d) id = 0 →
      Y₂ * P = Yb * P.submatrix (Fin.natAdd l) id := by
    intro P hP0
    ext a c
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
    have h00 : ∀ i, P (Fin.castAdd d i) c = 0 := fun i => by
      simpa using congrFun (congrFun hP0 i) c
    simp only [h00, mul_zero, Finset.sum_const_zero, zero_add]
    rfl
  have hmain : θ * (Xb + X₁ * A) = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := by
    calc θ * (Xb + X₁ * A) = θ * X₂ * K := by rw [← hK, Matrix.mul_assoc]
      _ = u₁ * Y₂ * (X₂ᴴ * (J * θ) * X₂) * K := by rw [hθ]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (X₂ * K))) := by simp only [Matrix.mul_assoc]
      _ = u₁ * (Y₂ * (X₂ᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [hK]
      _ = u₁ * (Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A))) := by rw [key _ hrow1]; rfl
      _ = u₁ * Yb * (Xbᴴ * (J * θ) * (Xb + X₁ * A)) := (Matrix.mul_assoc u₁ Yb _).symm
  have hzero : (X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) = 0 := by
    have h0' := h0
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] at h0' ⊢
    rw [h0', Matrix.mul_zero]
  have hsame : Xbᴴ * (J * θ) * (Xb + X₁ * A)
      = (Xb + X₁ * A)ᴴ * (J * θ) * (Xb + X₁ * A) := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.add_mul, hzero, add_zero]
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg Matrix.conjTranspose hXY
    simpa [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hL : (Ybᴴ * J) * (Xb + X₁ * A) = 1 := by
    have e1 : Ybᴴ * J * Xb = 1 := by
      have : Ybᴴ * J * Xb = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      simp [Matrix.one_apply, Fin.ext_iff]
    have e2 : Ybᴴ * J * X₁ = 0 := by
      have : Ybᴴ * J * X₁ = (Yᴴ * J * X).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
          (fun j : Fin l => (⟨j.val, by omega⟩ : Fin r)) := rfl
      rw [this, hYX]
      ext i j
      have := j.isLt
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff, Matrix.zero_apply]
      rw [if_neg (by omega)]
    rw [Matrix.mul_add, e1, ← Matrix.mul_assoc, e2, Matrix.zero_mul, add_zero]
  have hinj : Function.Injective (Xb + X₁ * A).mulVec := by
    intro v w hvw
    have := congrArg (Ybᴴ * J).mulVec hvw
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.one_mulVec] at this
    exact this
  refine ⟨hmain, ?_⟩
  rw [hsame]
  exact hpos.conjTranspose_mul_mul_same hinj

end GlobalTheory
end

open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_flag_complement_posDef_factorization : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  atlas_forward_decl GlobalTheory.schur_complement_step_cpx
end

section
section
open scoped ComplexOrder

namespace GlobalTheory

theorem isotropic_unipotent_column_relations : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  intro n r J X hX l d h u A X₁ Xb X₂ h1 hb hperp
  classical

  have hext : ∀ (m : ℕ) (hm : m ≤ r) (a : Fin m → ℂ),
      Matrix.mulVec X (fun i : Fin r => if hi : i.val < m then a ⟨i.val, hi⟩ else 0) =
        Matrix.mulVec (X.submatrix id fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) a := by
    intro m hm a
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    symm
    refine Fintype.sum_of_injective (fun j : Fin m => (⟨j.val, by omega⟩ : Fin r)) ?_ _ _ ?_ ?_
    · intro x y hxy
      exact Fin.ext (by simpa using congrArg Fin.val hxy)
    · intro i hi
      have : ¬ i.val < m := by
        intro hlt
        exact hi ⟨⟨i.val, hlt⟩, rfl⟩
      simp [this]
    · intro j
      simp
  have he1 : ∀ a : Fin l → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₁ a := fun a => hext l (by omega) a
  have he2 : ∀ a : Fin (l + d) → ℂ, Matrix.mulVec X (fun i : Fin r => if hi : i.val < l + d then a ⟨i.val, hi⟩ else 0) =
      Matrix.mulVec X₂ a := fun a => hext (l + d) h a
  have hcol : ∀ (v : Fin n → ℂ) (i : Fin (l + d)),
      Matrix.mulVec (X₂.conjTranspose * J) v i =
        Matrix.mulVec (X.conjTranspose * J) v ⟨i.val, by omega⟩ := by
    intro v i
    rfl
  have hXc : ∀ (i j : Fin r), Matrix.mulVec (X.conjTranspose * J) (fun k => X k j) i = 0 := by
    intro i j
    exact congrFun (congrFun hX i) j
  have key : ∀ j : Fin r, ∃ c : Fin r → ℂ,
      (∀ i, c i ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
      Matrix.mulVec u (fun k => X k j) = (fun k => X k j) + Matrix.mulVec X c := by
    intro j
    by_cases hj1 : j.val < l
    · refine ⟨0, fun i hi => absurd rfl hi, ?_⟩
      funext k
      have := congrFun (congrFun h1 k) ⟨j.val, hj1⟩
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, X₁] using this
    by_cases hj2 : j.val < l + d
    · refine ⟨fun i => if hi : i.val < l then A ⟨i.val, hi⟩ ⟨j.val - l, by omega⟩ else 0, ?_, ?_⟩
      · intro i hi
        left
        by_cases hil : i.val < l
        · exact ⟨hil, by omega⟩
        · exact absurd (by simp [hil]) hi
      · have he1' := he1 (fun i => A i ⟨j.val - l, by omega⟩)
        beta_reduce at he1'
        rw [he1']
        funext k
        have := congrFun (congrFun hb k) ⟨j.val - l, by omega⟩
        have hjj : (⟨l + (j.val - l), by omega⟩ : Fin r) = j := Fin.ext (by simp; omega)
        simp only [Matrix.mul_apply, Matrix.add_apply, Xb, X₁, Matrix.submatrix_apply, id, hjj] at this
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, X₁] using this
    · have hz : Matrix.mulVec (X₂.conjTranspose * J) (fun k => X k j) = 0 := by
        funext i
        rw [hcol]
        exact hXc _ _
      obtain ⟨w, a, hwa⟩ := hperp _ hz
      refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
          (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
      · intro i hi
        right
        refine ⟨?_, by omega⟩
        by_contra hc
        have hc' : ¬ i.val < l := by omega
        exact hi (by simp [hc, hc'])
      · rw [Matrix.mulVec_add, he1, he2, ← hwa]
        abel
  choose c hc hc' using key
  refine ⟨Matrix.of fun i j => c j i, ?_, ?_, ?_⟩
  · ext k j
    have := congrFun (hc' j) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro i j hij
    exact hc j i (by simpa using hij)
  · intro v hv
    have hz : Matrix.mulVec (X₂.conjTranspose * J) v = 0 := by
      funext i
      rw [hcol]
      exact hv _ (by simp)
    obtain ⟨w, a, hwa⟩ := hperp v hz
    refine ⟨(fun i : Fin r => if hi : i.val < l + d then w ⟨i.val, hi⟩ else 0) +
        (fun i : Fin r => if hi : i.val < l then a ⟨i.val, hi⟩ else 0), ?_, ?_⟩
    · intro i hi
      by_contra hc
      have hc' : ¬ i.val < l := by omega
      exact hi (by simp [hc, hc'])
    · rw [hwa, Matrix.mulVec_add, he1, he2]

end GlobalTheory
end

open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  atlas_forward_decl GlobalTheory.isotropic_unipotent_column_relations
end

section
open scoped ComplexOrder

namespace GlobalTheory.MajPosCpx

theorem gram_sub_eq {n r a b : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) (g : Fin b → Fin r) (R : Matrix (Fin a) (Fin b) ℂ)
    (hR : ∀ i j, (X.conjTranspose * J * Y) (f i) (g j) = R i j) :
    (X.submatrix id f).conjTranspose * J * (Y.submatrix id g) = R := by
  ext i j; rw [← hR]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem mul_submatrix_id {n r a : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) : u * X.submatrix id f = (u * X).submatrix id f := by
  ext i j; simp [Matrix.mul_apply]

theorem exists_unip_conj_unitary : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 → Y.conjTranspose * J * Y = 0 → X.conjTranspose * J * Y = 1 →
    ∀ (c : GL (Fin n) ℂ) (ε : Fin n → Bool), (c.1).conjTranspose * J * c.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GL (Fin n) ℂ) (N : Matrix (Fin r) (Fin r) ℂ),
        (u.1).conjTranspose * J * u.1 = J ∧ u.1 * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u.1 v - v = Matrix.mulVec X w) ∧
        ∃ y₀ : GL (Fin d) ℂ, ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
          let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
          let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
          let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
          let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
          let M : Matrix (Fin n) (Fin n) ℂ := (c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1
          M.conjTranspose * M = 1 := by
  intro n r J hJ X Y hXX hYY hXY c ε hc l d h
  set Dg : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if ε i then 1 else -1) with hDg
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> norm_num
  have hcc : c.1 * (c⁻¹).1 = 1 := Units.mul_inv c
  have hcc' : (c⁻¹).1 * c.1 = 1 := Units.inv_mul c
  have hcH : (c⁻¹).1.conjTranspose * (c.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hcc, Matrix.conjTranspose_one]
  have hJc : J = (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 := by
    have e : (c⁻¹).1.conjTranspose * Dg * (c⁻¹).1 =
        ((c⁻¹).1.conjTranspose * (c.1).conjTranspose) * J * (c.1 * (c⁻¹).1) := by
      rw [← hc]; simp only [Matrix.mul_assoc]
    rw [e, hcH, hcc, Matrix.one_mul, Matrix.mul_one]
  set θ : Matrix (Fin n) (Fin n) ℂ := c.1 * Dg * (c⁻¹).1 with hθ
  have hθθ : θ * θ = 1 := by
    simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hcc]
  have hQ : J * θ = (c⁻¹).1.conjTranspose * (c⁻¹).1 := by
    rw [hJc]; simp only [hθ, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c⁻¹).1 c.1, hcc', Matrix.one_mul, ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul]
  have hQpd : (J * θ).PosDef := by
    rw [hQ]; exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (c⁻¹).isUnit)
  set X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₁
  set Y₁ : Matrix (Fin n) (Fin l) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₁
  set Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩ with hXb
  set Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩ with hYb
  set X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩ with hX₂
  set Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩ with hY₂
  have w11 : X₁.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have w1b : X₁.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have wbb : Xb.conjTranspose * J * Xb = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have v11 : X₁.conjTranspose * J * Y₁ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have v1b : X₁.conjTranspose * J * Yb = 0 :=
    gram_sub_eq J X Y _ _ 0 (fun i j => by
      rw [hXY, Matrix.one_apply, if_neg]
      · rfl
      · simp only [Fin.ext_iff]; omega)
  have ybb : Yb.conjTranspose * J * Yb = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have vbb : Xb.conjTranspose * J * Yb = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w22 : X₂.conjTranspose * J * X₂ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  have y22 : Y₂.conjTranspose * J * Y₂ = 0 := gram_sub_eq J Y Y _ _ 0 (fun i j => by rw [hYY]; rfl)
  have v22 : X₂.conjTranspose * J * Y₂ = 1 :=
    gram_sub_eq J X Y _ _ 1 (fun i j => by rw [hXY]; simp [Matrix.one_apply, Fin.ext_iff])
  have w21 : X₂.conjTranspose * J * X₁ = 0 := gram_sub_eq J X X _ _ 0 (fun i j => by rw [hXX]; rfl)
  obtain ⟨u₂, A, hu₂J, hu₂X₁, hu₂Xb, hu₂Yb, hu₂v, hA⟩ :=
    GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal n l d J (J * θ) hJ hQpd X₁ Y₁ Xb Yb w11 w1b wbb v11 v1b ybb vbb
  obtain ⟨u₁, hu₁J, hu₁X₂, hu₁v, hθX₂⟩ := GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant n (l + d) J θ hJ hθθ hQpd X₂ Y₂ w22 y22 v22
  have hu₁X₁ : u₁.1 * X₁ = X₁ := by
    have e : X₁ = X₂.submatrix id (fun j : Fin l => ⟨j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  have hu₁Xb : u₁.1 * Xb = Xb := by
    have e : Xb = X₂.submatrix id (fun j : Fin d => ⟨l + j.val, by omega⟩) := rfl
    rw [e, mul_submatrix_id, hu₁X₂]
  set u : GL (Fin n) ℂ := u₁ * u₂ with hu
  have huv : u.1 = u₁.1 * u₂.1 := Units.val_mul u₁ u₂
  have huJ : (u.1).conjTranspose * J * u.1 = J := by
    have e : (u₂.1).conjTranspose * (u₁.1).conjTranspose * J * (u₁.1 * u₂.1) =
        (u₂.1).conjTranspose * ((u₁.1).conjTranspose * J * u₁.1) * u₂.1 := by simp only [Matrix.mul_assoc]
    rw [huv, Matrix.conjTranspose_mul, e, hu₁J, hu₂J]
  have huX₁ : u.1 * X₁ = X₁ := by rw [huv, Matrix.mul_assoc, hu₂X₁, hu₁X₁]
  have huXb : u.1 * Xb = Xb + X₁ * A := by
    rw [huv, Matrix.mul_assoc, hu₂Xb, Matrix.mul_add, hu₁Xb, ← Matrix.mul_assoc, hu₁X₁]
  have huYb : u.1 * Yb = u₁.1 * Yb := by rw [huv, Matrix.mul_assoc, hu₂Yb]
  have huP : ∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
      ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u.1 v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a := by
    intro v hv
    have h1 : Matrix.mulVec (X₁.conjTranspose * J) v = 0 := by
      funext i; exact congrFun hv ⟨i.val, by omega⟩
    set a := Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v) with ha
    have h2 : Matrix.mulVec (X₂.conjTranspose * J) (v + Matrix.mulVec X₁ a) = 0 := by
      rw [Matrix.mulVec_add, hv, Matrix.mulVec_mulVec, w21, Matrix.zero_mulVec, add_zero]
    obtain ⟨w, hw⟩ := hu₁v _ h2
    refine ⟨w, a, ?_⟩
    rw [huv, ← Matrix.mulVec_mulVec, hu₂v v h1, ← hw]
    abel
  obtain ⟨N, hN, hNs, hNp⟩ := GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse n r J X hXX l d h u.1 A huX₁ huXb huP
  obtain ⟨hθX', hHpd⟩ := GlobalTheory.T.hermitian_flag_complement_posDef_factorization n r J θ hJ hQpd X Y hXY l d h u₁.1 A hθX₂ hA
  set H : Matrix (Fin d) (Fin d) ℂ := Xb.conjTranspose * (J * θ) * (Xb + X₁ * A) with hHdef
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' d H hHpd
  have hθu : θ * u.1 * Xb = u.1 * Yb * H := by
    rw [Matrix.mul_assoc, huXb, hθX', huYb]
  have hy1 : (y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hHy : H = (y₀⁻¹).1.conjTranspose * (y₀⁻¹).1 := by
    calc H = ((y₀⁻¹).1.conjTranspose * (y₀.1).conjTranspose) * H * (y₀.1 * (y₀⁻¹).1) := by
          rw [hy1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (y₀⁻¹).1.conjTranspose * ((y₀.1).conjTranspose * H * y₀.1) * (y₀⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hy₀, Matrix.mul_one]
  have hHinv : H * (y₀.1 * (y₀.1).conjTranspose) = 1 := by
    calc H * (y₀.1 * (y₀.1).conjTranspose) = (y₀⁻¹).1.conjTranspose * ((y₀⁻¹).1 * y₀.1) * (y₀.1).conjTranspose := by
          rw [hHy]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, hy1]
  have huJ' : (u.1).conjTranspose * J = J * (u⁻¹).1 := by
    calc (u.1).conjTranspose * J = (u.1).conjTranspose * J * (u.1 * (u⁻¹).1) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((u.1).conjTranspose * J * u.1) * (u⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = J * (u⁻¹).1 := by rw [huJ]
  have hθuY : θ * u.1 * Yb = u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc θ * u.1 * Yb = θ * u.1 * Yb * (H * (y₀.1 * (y₀.1).conjTranspose)) := by rw [hHinv, Matrix.mul_one]
      _ = θ * (θ * u.1 * Xb) * (y₀.1 * (y₀.1).conjTranspose) := by rw [hθu]; simp only [Matrix.mul_assoc]
      _ = (θ * θ) * u.1 * Xb * (y₀.1 * (y₀.1).conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hθθ, Matrix.one_mul]
  have hPX : (u.1).conjTranspose * (J * θ) * u.1 * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Xb = ((u.1).conjTranspose * J) * (θ * u.1 * Xb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Yb * H := by rw [huJ', hθu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one, hHy]
  have hPY : (u.1).conjTranspose * (J * θ) * u.1 * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) := by
    calc (u.1).conjTranspose * (J * θ) * u.1 * Yb = ((u.1).conjTranspose * J) * (θ * u.1 * Yb) := by
          simp only [Matrix.mul_assoc]
      _ = J * ((u⁻¹).1 * u.1) * Xb * (y₀.1 * (y₀.1).conjTranspose) := by rw [huJ', hθuY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.mul_one]
  have hPH : ((u.1).conjTranspose * (J * θ) * u.1).conjTranspose = (u.1).conjTranspose * (J * θ) * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQpd.1.eq]
    simp only [Matrix.mul_assoc]
  refine ⟨u, N, huJ, hN, hNs, fun v hv => hNp v hv, y₀, fun k hk => ?_⟩
  intro Xb' Yb' m G M
  have hG : G.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * G = (u.1).conjTranspose * (J * θ) * u.1 :=
    GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary n d J ((u.1).conjTranspose * (J * θ) * u.1) Xb Yb y₀ hJ hPH wbb ybb vbb hPX hPY k hk
  show ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) = 1
  have e1 : ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1) =
      (c.1).conjTranspose * ((u⁻¹).1.conjTranspose *
        (G.conjTranspose * ((u.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * u.1) * G) * (u⁻¹).1) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e1, ← hQ, hG]
  have e2 : (c.1).conjTranspose * ((u⁻¹).1.conjTranspose * ((u.1).conjTranspose * (J * θ) * u.1) * (u⁻¹).1) * c.1 =
      (c.1).conjTranspose * ((u.1 * (u⁻¹).1).conjTranspose * (J * θ) * (u.1 * (u⁻¹).1)) * c.1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hQ]
  have e3 : (c.1).conjTranspose * ((c⁻¹).1.conjTranspose * (c⁻¹).1) * c.1 =
      ((c⁻¹).1 * c.1).conjTranspose * ((c⁻¹).1 * c.1) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e3, hcc', Matrix.conjTranspose_one, Matrix.one_mul]

end GlobalTheory.MajPosCpx
end
