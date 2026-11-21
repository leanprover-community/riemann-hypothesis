import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef

section
theorem UpperTheory.infinite_norm_one_elements :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by
  intro F E _ _ _ _ σ hE hσ
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)
  generalize w.embedding = τ at hw
  have hinv : ∀ x : E, σ (σ x) = x := fun x =>
    τ.injective (by rw [hσ, hσ, star_star])
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [h] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  have h1 : ∀ n : ℕ, (n : E) + a ≠ 0 := by
    intro n hn
    apply ha
    have : a = -(n : E) := by linear_combination hn
    rw [this, map_neg, map_natCast]
  have h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0 := by
    intro n hn
    apply h1 n
    have := congrArg σ hn
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_
  · intro m n hmn
    have h3 := (div_eq_div_iff (h2 m) (h2 n)).mp hmn
    have h4 : ((m : E) - n) * (σ a - a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact Nat.cast_injective (R := E) (sub_eq_zero.mp h)
    · exact absurd (sub_eq_zero.mp h) ha
  · intro n
    show _ * σ _ = 1
    rw [map_div₀, map_add, map_add, map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]
end

section
theorem UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite :=
  UpperTheory.infinite_norm_one_elements
end

section
theorem UpperTheory.Reformulated.B.InfiniteNormOne.infinite_norm_one :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
      {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
      {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
      {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E},
      PositivityTheory.ThKW.Ctx σ B JS JT ξ₀ θ ι → {t : E | t * (σ : E → E) t = (1 : E)}.Infinite := by
  intro F E _ _ _ _ _ σ B nS nT JS JT ξ θ ι h
  obtain ⟨-, -, -, h0, hσ, -, -⟩ := h
  have hz : ∀ n : ℤ, (n : E) - ξ ≠ 0 := fun n hn => h0 <| by
    have e : ξ = (n : E) := (sub_eq_zero.mp hn).symm
    have e2 : σ ξ = ξ := by rw [e, map_intCast]
    linear_combination (1 / 2 : E) * hσ - (1 / 2 : E) * e2
  have hp : ∀ n : ℤ, (n : E) + ξ ≠ 0 := fun n hn => hz (-n) <| by
    push_cast; linear_combination -hn
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => ((n : E) + ξ) / ((n : E) - ξ))
    (fun n m hnm => ?_) (fun n => ?_)
  · have e := (div_eq_div_iff (hz n) (hz m)).mp hnm
    have e2 : ((n : E) - m) * ξ = 0 := by linear_combination (-1 / 2 : E) * e
    exact Int.cast_injective (sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right h0))
  · simp only [Set.mem_setOf_eq, map_div₀, map_add, map_sub, map_intCast, hσ, sub_neg_eq_add,
      ← sub_eq_add_neg]
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hz n) (hp n))]
end
