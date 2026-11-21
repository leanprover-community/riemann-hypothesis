import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ColMeas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.LangWitt

open Matrix

section Field

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]


end Field

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

local notation "𝕎" => WittVector p

theorem constantCoeff_frobenius (x : 𝕎 k) :
    WittVector.constantCoeff (WittVector.frobenius x) = frobenius k p (WittVector.constantCoeff x) := by
  show (WittVector.frobenius x).coeff 0 = frobenius k p (x.coeff 0)
  rw [WittVector.coeff_frobenius_charP, frobenius_def]

theorem constantCoeff_p : WittVector.constantCoeff (p : 𝕎 k) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

variable [IsAlgClosed k]

theorem p_dvd_iff (x : 𝕎 k) : (p : 𝕎 k) ∣ x ↔ WittVector.constantCoeff x = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]

theorem map_sub' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A - B).map f = A.map f - B.map f :=
  map_sub f.mapMatrix A B

theorem map_add' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A + B).map f = A.map f + B.map f :=
  map_add f.mapMatrix A B

theorem exists_step {d : ℕ} (N V E : Matrix (Fin d) (Fin d) (𝕎 k)) (hN : IsUnit N.det)
    (hV : IsUnit (V.map WittVector.constantCoeff).det) (n : ℕ)
    (hE : V.map WittVector.frobenius - N * V = ((p : 𝕎 k) ^ (n + 1)) • E) :
    ∃ Y E' : Matrix (Fin d) (Fin d) (𝕎 k),
      (V + (p : 𝕎 k) ^ (n + 1) • Y).map WittVector.frobenius - N * (V + (p : 𝕎 k) ^ (n + 1) • Y)
        = ((p : 𝕎 k) ^ (n + 2)) • E' := by
  classical
  set c : 𝕎 k →+* k := WittVector.constantCoeff with hc
  set φ : 𝕎 k →+* 𝕎 k := WittVector.frobenius with hφ
  have hcp : c (p : 𝕎 k) = 0 := constantCoeff_p
  have hcφ : ∀ A : Matrix (Fin d) (Fin d) (𝕎 k), (A.map φ).map c = (A.map c).map (frobenius k p) := by
    intro A; ext i j; exact constantCoeff_frobenius _
  have hmod : (V.map c).map (frobenius k p) = N.map c * V.map c := by
    have h1 := congrArg (fun A => A.map c) hE
    simp only [map_sub', Matrix.map_mul, hcφ] at h1
    rw [← sub_eq_zero, h1]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hcp,
      Matrix.zero_apply]
    simp
  set Vb := V.map c
  set Nb := N.map c
  have hNb : IsUnit Nb.det := by
    show IsUnit (c.mapMatrix N).det
    rw [← RingHom.map_det]; exact hN.map c
  set Mb := Nb * Vb
  have hMb : IsUnit Mb.det := by rw [Matrix.det_mul]; exact hNb.mul hV
  set R := -(Mb⁻¹ * E.map c)
  choose z hz using fun i j => GlobalTheory.PMonE.LangIsogenyConstruction.as_root p hp.out.one_lt (R i j)
  set Z : Matrix (Fin d) (Fin d) k := Matrix.of z
  have hZ : Z.map (frobenius k p) - Z = R := by
    refine Matrix.ext fun i j => ?_
    simp [Z, frobenius_def, hz]
  set Y : Matrix (Fin d) (Fin d) (𝕎 k) := (Vb * Z).map (WittVector.teichmuller p)
  have hYc : Y.map c = Vb * Z := by
    refine Matrix.ext fun i j => ?_
    simp [Y, c, WittVector.teichmuller_coeff_zero]
  set G := E + Y.map φ - N * Y
  have hG : G.map c = 0 := by
    simp only [G, map_sub', map_add', Matrix.map_mul, hcφ, hYc, hmod]
    have : E.map c + Mb * Z.map (frobenius k p) - Nb * (Vb * Z)
        = E.map c + Mb * (Z.map (frobenius k p) - Z) := by
      simp only [Mb, Matrix.mul_sub, Matrix.mul_assoc]; abel
    rw [this, hZ]
    simp only [R, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMb, Matrix.one_mul]
    abel
  have hGd : ∀ i j, (p : 𝕎 k) ∣ G i j := fun i j => by
    rw [p_dvd_iff]; exact congrFun (congrFun hG i) j
  choose E' hE' using hGd
  refine ⟨Y, Matrix.of E', ?_⟩
  have hexp : (V + (p : 𝕎 k) ^ (n + 1) • Y).map φ - N * (V + (p : 𝕎 k) ^ (n + 1) • Y)
      = (V.map φ - N * V) + (p : 𝕎 k) ^ (n + 1) • (Y.map φ - N * Y) := by
    refine Matrix.ext fun i j => ?_
    simp [Matrix.mul_add, Matrix.mul_smul, map_pow, map_natCast, φ]
    ring
  rw [hexp, hE]
  refine Matrix.ext fun i j => ?_
  have := hE' i j
  simp only [G, Matrix.add_apply, Matrix.sub_apply] at this
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Matrix.of_apply]
  linear_combination ((p : 𝕎 k) ^ (n + 1)) * this

end Witt


end GlobalTheory.LangWitt
