module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev gi (g : GL (Fin N) L) : Matrix (Fin N) (Fin N) L := ((g⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L)

theorem z_ne (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (w : InfinitePlace L) : z w ≠ 0 := by
  intro h
  have h1 := hc w
  rw [h, zero_smul] at h1
  have h2 : (mt c w).det = 1 := (c w).prop
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [h1, Matrix.det_zero] at h2
  exact zero_ne_one h2

theorem toL_ne {y : Lat L N} (hy : y ≠ 0) : toL y ≠ 0 := by
  intro h
  apply hy
  funext a
  have h1 := congrFun h a
  simpa [toL] using h1

theorem gi_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : gi g *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have := congrArg (fun v => (g : Matrix (Fin N) (Fin N) L) *ᵥ v) h
  simpa [mulVec_mulVec, Units.mul_inv, one_mulVec] using this

theorem gT_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have h2 : (gi g)ᵀ * (g : Matrix (Fin N) (Fin N) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]
  have h1 : (gi g)ᵀ *ᵥ ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) = (gi g)ᵀ *ᵥ 0 := by rw [h]
  rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h1

theorem int_d {d : ℤ} {G : Matrix (Fin N) (Fin N) L} (hd : ∀ i j, IsIntegral ℤ ((d : L) * G i j)) (y : Lat L N)
    (a : Fin N) : IsIntegral ℤ ((d : L) * (G *ᵥ toL y) a) := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [← mul_assoc]
  exact (hd a j).mul (RingOfIntegers.isIntegral_coe (y j))

theorem sum_sq_ge (hL : IsTotallyComplex L) {d : ℤ} (hd : d ≠ 0) {β : L} (hβ : β ≠ 0)
    (hint : IsIntegral ℤ ((d : L) * β)) : ((d : ℝ) ^ 2)⁻¹ ≤ ∑ w : InfinitePlace L, ‖w.embedding β‖ ^ 2 := by
  have hdR : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  let α : 𝓞 L := ⟨(d : L) * β, hint⟩
  have hαc : ((α : 𝓞 L) : L) = (d : L) * β := rfl
  have hα0 : α ≠ 0 := by
    intro h
    have h1 : ((α : 𝓞 L) : L) = 0 := by rw [h]; rfl
    rw [hαc] at h1
    exact mul_ne_zero (Int.cast_ne_zero.mpr hd) hβ h1
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, 1 ≤ w ((α : 𝓞 L) : L) := by
    by_contra H
    push_neg at H
    obtain ⟨w0⟩ : Nonempty (InfinitePlace L) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one hα0 (fun z _ => H z)) (not_le.mpr (H w0))
  have hwα : w ((α : 𝓞 L) : L) = |(d : ℝ)| * ‖w.embedding β‖ := by
    rw [← InfinitePlace.norm_embedding_eq, hαc, map_mul, norm_mul, map_intCast, Complex.norm_intCast]
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have h1 : 1 ≤ (d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2 := by
    have h2 : (1 : ℝ) ≤ (|(d : ℝ)| * ‖w.embedding β‖) ^ 2 := one_le_pow₀ (hwα ▸ hw)
    rwa [mul_pow, sq_abs] at h2
  have key : ((d : ℝ) ^ 2)⁻¹ ≤ ‖w.embedding β‖ ^ 2 := by
    calc ((d : ℝ) ^ 2)⁻¹ = ((d : ℝ) ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ ((d : ℝ) ^ 2)⁻¹ * ((d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2) := by gcongr
      _ = ‖w.embedding β‖ ^ 2 := by field_simp
  exact key.trans (Finset.single_le_sum (f := fun v : InfinitePlace L => ‖v.embedding β‖ ^ 2)
    (fun v _ => sq_nonneg _) (Finset.mem_univ w))

end PositivityTheory.KB.MomentRationality.Ht
