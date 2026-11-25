module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Mathlib.Order.CompletePartialOrder
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Formalism.WachCohomologyFacts.PLenBound in
theorem submodule_generator_count : SubGen := by
  intro O _ _ _ M _ _ _ _ ℓ e F P h
  classical

  have hA (n : ℕ) : Module.length O (O ⧸ Ideal.span {ℓ ^ n}) ≤
      (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    induction n with
    | zero =>
      have : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) := Ideal.Quotient.subsingleton_iff.2 (by simp)
      simp [Module.length_eq_zero]
    | succ n ih =>
      have hle : Ideal.span {ℓ ^ (n + 1)} ≤ Ideal.span {ℓ ^ n} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ (Nat.le_succ n))
      let g : (O ⧸ Ideal.span {ℓ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ n}) :=
        Submodule.mapQ _ _ LinearMap.id (fun x hx => hle hx)
      have hg : Function.Surjective g := Submodule.factor_surjective hle

      let f0 : (O ⧸ Ideal.span {ℓ}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ (n + 1)}) :=
        (Ideal.span {ℓ}).liftQ (ℓ ^ n • (Ideal.span {ℓ ^ (n + 1)}).mkQ) (by
          intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
          rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
          exact ⟨c, by rw [smul_eq_mul]; ring⟩)
      have hf0 : ∀ x, f0 x ∈ LinearMap.ker g := by
        intro x
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.mem_ker]
        simp only [f0, g, Submodule.liftQ_apply, LinearMap.smul_apply, Submodule.mkQ_apply,
          map_smul, Submodule.mapQ_apply, LinearMap.id_apply]
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
        exact ⟨a, by rw [smul_eq_mul, mul_comm]⟩
      have hf1 : Function.Surjective (f0.codRestrict (LinearMap.ker g) hf0) := by
        rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        have ha : a ∈ Ideal.span {ℓ ^ n} := (Submodule.Quotient.mk_eq_zero _).mp hy
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        refine ⟨Submodule.Quotient.mk c, Subtype.ext ?_⟩
        simp only [LinearMap.codRestrict_apply, f0, Submodule.liftQ_apply, LinearMap.smul_apply,
          Submodule.mkQ_apply]
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]
      rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
        (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)]
      refine (add_le_add (Module.length_le_of_surjective _ hf1) ih).trans_eq ?_
      push_cast
      ring

  obtain ⟨k, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  have hk : k ≤ Module.finrank O M := by
    have h1 := Submodule.finrank_le F
    rwa [Module.finrank_eq_card_basis bF, Fintype.card_fin] at h1
  set Q := P.comap F.subtype with hQ

  let φ : Fin k → (O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := fun i =>
    (Ideal.span {ℓ ^ e}).liftQ (LinearMap.toSpanSingleton O (↥F ⧸ Q) (Q.mkQ (bF i))) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, mul_smul]
      exact Q.smul_mem c (by
        rw [hQ, Submodule.mem_comap, map_smul]
        exact h _ (bF _).2))
  let ψ : (Fin k → O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := ∑ i, (φ i).comp (LinearMap.proj i)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨fun i => Submodule.Quotient.mk (bF.repr x i), ?_⟩
    have hx : (Submodule.Quotient.mk x : ↥F ⧸ Q) =
        ∑ i, bF.repr x i • Submodule.Quotient.mk (bF i) := by
      conv_lhs => rw [← bF.sum_repr x]

      rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    rw [hx]
    simp only [ψ, φ, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
  calc Module.length O (↥F ⧸ Q)
      ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
        simpa [Module.length_pi_of_fintype] using Module.length_le_of_surjective ψ hψ
    _ ≤ (k : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) := by
        gcongr
        exact hA e
    _ ≤ ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
        push_cast
        rw [mul_assoc]
        gcongr

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
