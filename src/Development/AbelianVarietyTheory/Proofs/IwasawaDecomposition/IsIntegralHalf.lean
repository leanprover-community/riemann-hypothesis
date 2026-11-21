import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb

section
namespace GlobalTheory.CoordsOfMemAdjoin

open IntermediateField

theorem exists_coords_of_mem_adjoin {F : Type*} [Field F] [Algebra ℚ F] {s : F} {c : ℚ}
    (hs : s ^ 2 = algebraMap ℚ F c) {x : F} (hx : x ∈ ℚ⟮s⟯) :
    ∃ a b : ℚ, x = algebraMap ℚ F a + algebraMap ℚ F b * s := by
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set F) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    refine ⟨0, 1, ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    simp
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a + a', b + b', ?_⟩
    simp only [map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add, map_mul, ← hs]
    ring

theorem exists_rat_coords {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {x : H.E} (hx : x ∈ H.K) :
    ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD := by
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hs : H.sqrtMinusD ^ 2 = algebraMap ℚ H.E (-(H.d : ℚ)) := by
    rw [map_neg, map_natCast]
    exact hb
  obtain ⟨a, b, h⟩ := exists_coords_of_mem_adjoin hs hx
  exact ⟨a, b, by simpa only [eq_ratCast] using h⟩

end GlobalTheory.CoordsOfMemAdjoin
end

section
noncomputable section

namespace GlobalTheory.Mem.Col2.HostK

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.UnusedSlot33.HK
open scoped BigOperators

variable {R : Ranks} (H : Host R)

theorem emb_conj (f : H.E →+* ℂ) (y : H.E) : f (H.conj y) = starRingEnd ℂ (f y) := Formalism.HC.HostAx.conjE_apply _ _ _

theorem sqrt_mem : H.sqrtMinusD ∈ H.K := bE_mem H

theorem φ₀_sqrt : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem exists_coords {x : H.E} (hx : x ∈ H.K) : ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD :=
  by apply _root_.GlobalTheory.CoordsOfMemAdjoin.exists_rat_coords <;> assumption

theorem conj_coords (a b : ℚ) :
    H.conj ((a : H.E) + (b : H.E) * H.sqrtMinusD) = (a : H.E) - (b : H.E) * H.sqrtMinusD := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, H.conj_sqrtMinusD]
  ring

theorem conj_mem {x : H.E} (hx : x ∈ H.K) : H.conj x ∈ H.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords H hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a) (mul_mem (SubfieldClass.ratCast_mem _ b) (sqrt_mem H))

def conjK : H.K →+* H.K :=
  RingHom.codRestrict ((H.conj : H.E →+* H.E).comp H.K.val.toRingHom) H.K (fun x => conj_mem H x.2)

theorem coe_conjK (x : H.K) : ((conjK H x : H.K) : H.E) = H.conj (x : H.E) := rfl

theorem conjK_conjK (x : H.K) : conjK H (conjK H x) = x := Subtype.ext (conj_conj H x)

theorem exists_norm_int (x : 𝓞 H.K) : ∃ m : ℤ, (x : H.K) * conjK H x = m :=
  ⟨Algebra.intNorm ℤ (𝓞 H.K) x, Subtype.ext (by
    have := norm_int H x
    simpa [coe_conjK] using this.symm)⟩

theorem isGalois_over : IsGalois H.K H.E := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : H.E) : ((Algebra.trace H.K H.E y : H.K) : H.E) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ y := by
  have := isGalois_over H
  exact trace_eq_sum_automorphisms (K := H.K) y

theorem conj_comm (τ : H.E ≃ₐ[H.K] H.E) (y : H.E) : H.conj (τ y) = τ (H.conj y) :=
  H.φ₀.injective (by
    rw [emb_conj H H.φ₀ (τ y)]
    exact (emb_conj H (H.φ₀.comp (τ : H.E →+* H.E)) y).symm)

theorem trace_conj (y : H.E) : Algebra.trace H.K H.E (H.conj y) = conjK H (Algebra.trace H.K H.E y) := by
  apply Subtype.ext
  rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm H τ y).symm

theorem trace_pos (y : H.E) (hy : y ≠ 0) : ∃ a : ℚ, 0 < a ∧ Algebra.trace H.K H.E (y * H.conj y) = (a : H.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords H (Algebra.trace H.K H.E (y * H.conj y)).2
  have hfix : H.conj ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E)
      = ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : H.E) * H.sqrtMinusD = 0 := by linear_combination (-1 / 2 : H.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg H.φ₀ hab
  rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : H.E ≃ₐ[H.K] H.E, H.φ₀ (τ (y * H.conj y)) = ((Complex.normSq (H.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : H.E ≃ₐ[H.K] H.E, Complex.normSq (H.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem card_tau : Fintype.card (Tau R) = Module.finrank H.K H.E := by
  have := isGalois_over H
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective (GlobalTheory.InducedType.galK_bijective H)

theorem embT_K (τ : Tau R) (a : H.K) : embT H τ (a : H.E) = H.φ₀ (a : H.E) := by
  change H.φ₀ (H.sigmaOf _ _) = _
  rw [sigmaOf_fix_K H _ τ.2 _ a.2]

theorem sum_embT (y : H.E) : ∑ τ, embT H τ y = H.φ₀ ((Algebra.trace H.K H.E y : H.K) : H.E) := by
  rw [coe_trace, map_sum]
  exact Fintype.sum_bijective (GlobalTheory.InducedType.galK H) (GlobalTheory.InducedType.galK_bijective H) _ _ (fun τ => rfl)

theorem isIntegral_half : IsIntegral ℤ ((1 + (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K)) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := by
    have := H.hyp.2.2.2.1
    exact ⟨(H.d + 1) / 4, by omega⟩
  have hs : (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K) ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa using H.sqrtMinusD_sq)
  have hm' : (H.d : H.K) + 1 = 4 * m := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : H.K) * hs - (1 / 4 : H.K) * hm'

end GlobalTheory.Mem.Col2.HostK

end
end
