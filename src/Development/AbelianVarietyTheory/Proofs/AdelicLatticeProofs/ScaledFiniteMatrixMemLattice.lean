import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight

section
namespace GlobalTheory.NatMulIntegralNsmul

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ M : ℕ, 0 < M ∧ IsIntegral ℤ ((M : E) * a) := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]; exact hint
  · have h2 : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h2, Int.cast_neg, neg_mul]
    exact hint.neg

theorem exists_nsmul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (h : Submodule.IsLattice E Λ)
    (v : Fin n → E) : ∃ (N : ℕ), (0 : ℕ) < N ∧ N • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [h.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_smul]; exact nsmul_mem hx M
    · rw [mul_comm, mul_smul]; exact nsmul_mem hy N
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hint⟩ := exists_nat_mul_integral a
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (M : E) * a := ⟨⟨(M : E) * a, hint⟩, rfl⟩
    have hmem := Λ.smul_mem r hx
    have e : (M * N) • a • x = r • N • x := by
      rw [← algebraMap_smul E r (N • x), hr]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply,
        Pi.natCast_apply]
      ring
    rw [e]; exact hmem

end GlobalTheory.NatMulIntegralNsmul
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Den

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsLattice E Λ) (v : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem
  | exact _root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem
  | (apply _root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem ..)

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem exists_nsmul_finRat_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT γ
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ D.host.AA, a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact AA_ne_zero D (FractionalIdeal.eq_zero_iff.2 hc)
  rw [Matrix.matrix_eq_sum_single γ]
  simp_rw [← Finset.sum_product']
  refine Finset.sum_induction _ (fun γ => ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ?_ ?_ ?_
  · rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    rw [AddMonoidHom.map_add, nsmul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact nsmul_mem hx M
    · rw [mul_nsmul']; exact nsmul_mem hy N
  · exact ⟨1, one_pos, by rw [AddMonoidHom.map_zero, nsmul_zero]; exact zero_mem _⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨N, hN, ht⟩ := exists_nsmul_mem_lattice ΛT hT (Pi.single i (γ i j / a))
    obtain ⟨M, hM, hs⟩ := exists_nsmul_mem_lattice ΛS hS (fun k => star (S.gram⁻¹ j k))
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    refine AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv,
      a, ha, _, hs, _, ht, ?_⟩
    rw [← map_nsmul]
    funext i' j'
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _ = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _
    congr 1
    have hG : ∑ k, S.gram⁻¹ j k * S.gram k j' = (1 : Matrix _ _ D.host.E) j j' := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Formalism.L2.Theta.gram_det_ne S).isUnit]
    have h2 : ∑ k, star ((M • fun k => star (S.gram⁻¹ j k)) k) * S.gram k j' =
        (M : D.host.E) * (1 : Matrix _ _ D.host.E) j j' := by
      rw [← hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, star_nsmul, star_star, nsmul_eq_mul, mul_assoc]
    rw [h2]
    simp only [Matrix.smul_apply, Pi.smul_apply, nsmul_eq_mul, Matrix.single_apply, Pi.single_apply, Matrix.one_apply,
      Nat.cast_mul]
    by_cases h1 : i = i' <;> by_cases h3 : j = j'
    · subst h1 h3; simp; field_simp
    · simp [h3]
    · simp [h1, Ne.symm h1]
    · simp [h1, h3]

end GlobalTheory.VacUnique.Den
end
