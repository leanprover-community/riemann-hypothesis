import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def integralAtPlaces {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) :
    Subalgebra ℤ L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul]
    exact mul_le_one₀ (ha w hw) (apply_nonneg w b) (hb w hw)
  add_mem' {a b} ha hb w hw := (FinitePlace.add_le w a b).trans (max_le (ha w hw) (hb w hw))
  algebraMap_mem' z w _ := by
    rw [eq_intCast, ← FinitePlace.mk_maximalIdeal w, FinitePlace.mk_apply,
      FinitePlace.norm_embedding]
    exact NumberField.HeightOneSpectrum.adicAbv_intCast_le_one (K := L) (v := w.maximalIdeal) z

def SemilocalQuotCard.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Set (FinitePlace L)), S.Finite →
    ∀ t : integralAtPlaces S, t ≠ 0 →
      (Nat.card (integralAtPlaces S ⧸ Ideal.span {t}) : ℝ) = ∏ᶠ w ∈ S, (w (t : L))⁻¹

example : ∃ (S : Set (FinitePlace ℚ)) (t : integralAtPlaces S), S.Finite ∧ S.Nonempty ∧ t ≠ 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
  have hne : P ≠ ⊥ := fun h ↦
    RingOfIntegers.not_isField ℚ (Ring.isField_iff_maximal_bot.mpr (h ▸ hP))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨P, hP.isPrime, hne⟩
  refine ⟨{FinitePlace.mk v}, 2, Set.finite_singleton _, Set.singleton_nonempty _, ?_⟩
  intro h
  have := congrArg (fun y : integralAtPlaces ({FinitePlace.mk v} : Set (FinitePlace ℚ)) ↦ (y : ℚ)) h
  norm_num at this

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def CentredConductor.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal],
      ∃ c : O, c ≠ 0 ∧
        ∀ x ∈ integralAtPlaces {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t},
          ∃ a s : O, s ∉ m ∧ (s : L) * c * x = a

example : ∃ (O : Subalgebra ℤ ℚ) (m : Ideal O), Algebra.FiniteType ℤ O ∧
    IsFractionRing O ℚ ∧ m.IsMaximal := by
  let e : (⊥ : Subalgebra ℤ ℚ) ≃ₐ[ℤ] ℤ := Algebra.botEquivOfInjective Int.cast_injective
  have hft : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ ℚ) := Algebra.FiniteType.equiv inferInstance e.symm
  have hfr : IsFractionRing (⊥ : Subalgebra ℤ ℚ) ℚ := by
    refine IsFractionRing.of_field (⊥ : Subalgebra ℤ ℚ) ℚ fun z ↦ ⟨algebraMap ℤ _ z.num, algebraMap ℤ _ z.den, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp [Rat.num_div_den]
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (⊥ : Subalgebra ℤ ℚ)) bot_ne_top
  exact ⟨⊥, m, hft, hfr, hm⟩

end GroundTheory.Heights₂.Heights
end
