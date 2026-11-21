import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealIntegralLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumTwoSidedMulEqMatrixUnitUnitaryDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjOfIntegralConjGeneratorStatement

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem GlobalTheory.AbsLattice.exists_unit_of_conj_stable : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by

  intro A B _ _ j Λ R r e h0 h1 hadd hneg hmul hR0 hR1 hRadd hRneg hRmul hrep hmem hE hden hsq X hX
  rcases r with _ | n
  · have hall : ∀ a : A, a = 0 := fun a => by
      obtain ⟨β, hβ, -⟩ := hrep a
      simpa using hβ
    have key : ∀ a : A, a ∈ Λ := fun a => by rw [hall a]; exact h0
    exact ⟨1, key _, key _⟩
  ·
    have hL : ∀ ρ ∈ R, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (j ρ * x) ∈ Λ := by
      intro ρ hρ x hx
      have : (X : A) * (j ρ * x) = ((X : A) * j ρ * ↑X⁻¹) * ((X : A) * x) := by
        simp [mul_assoc]
      rw [this]; exact hmul _ (hX ρ hρ) _ hx
    have hRt : ∀ μ ∈ Λ, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (x * μ) ∈ Λ := by
      intro μ hμ x hx
      rw [← mul_assoc]; exact hmul _ hx _ hμ
    have hS : ∀ (N : ℕ) (f : Fin N → A), (∀ k, (X : A) * f k ∈ Λ) → (X : A) * ∑ k, f k ∈ Λ := by
      intro N f hf
      rw [Finset.mul_sum]
      exact Finset.sum_induction _ (· ∈ Λ) (fun a b ha hb => hadd a ha b hb) h0 (fun k _ => hf k)
    have hsingle : ∀ b : B, ∑ i'', j ((Pi.single (0 : Fin (n+1)) b : Fin (n+1) → B) i'') * e i'' = j b * e 0 := by
      intro b
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, map_zero, zero_mul]
      · simp
    have hsingleR : ∀ b : B, j b * e 0 ∈ Λ ↔ b ∈ R := by
      intro b
      rw [← hsingle, hmem]
      constructor
      · intro h; simpa using h 0
      · intro hb i
        by_cases hi : i = 0
        · subst hi; simpa using hb
        · rw [Pi.single_eq_of_ne hi]; exact hR0
    have he0 : e 0 ∈ Λ := by
      have := (hsingleR 1).2 hR1
      rwa [map_one, one_mul] at this

    have hA : ∀ β : Fin (n+1) → B, (X : A) * (∑ i, j (β i) * e i) ∈ Λ →
        ∀ i', (X : A) * (j (β i') * e 0) ∈ Λ := by
      intro β hx i'
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE 0 i'
      rw [← hf β]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hx))

    have hB : ∀ b : B, (X : A) * (j b * e 0) ∈ Λ → ∀ i, (X : A) * (j b * e i) ∈ Λ := by
      intro b hb i
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE i 0
      have h := hf (Pi.single 0 b)
      rw [hsingle, Pi.single_eq_same] at h
      rw [← h]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hb))
    have hsum : ∀ β : Fin (n+1) → B, (∀ i, (X : A) * (j (β i) * e 0) ∈ Λ) →
        (X : A) * (∑ i, j (β i) * e i) ∈ Λ :=
      fun β hβ => hS _ _ (fun i => hB _ (hβ i) i)
    have hRint : ∀ z : ℤ, (z : B) ∈ R := by
      intro z
      induction z using Int.induction_on with
      | zero => simpa using hR0
      | succ i ih => rw [Int.cast_add, Int.cast_one]; exact hRadd _ ih _ hR1
      | pred i ih =>
        have : ((-(i : ℤ) - 1 : ℤ) : B) = ((-(i : ℤ) : ℤ) : B) + -1 := by push_cast; ring
        rw [this]; exact hRadd _ ih _ (hRneg _ hR1)
    obtain ⟨D₁, hD₁, hD₁m⟩ := hden (X : A)
    obtain ⟨D₂, hD₂, hD₂m⟩ := hden (↑X⁻¹ : A)
    have hDR : ∀ ρ ∈ R, (X : A) * (j (ρ * D₁) * e 0) ∈ Λ := by
      intro ρ hρ
      rw [map_mul, map_intCast, mul_assoc]
      apply hL ρ hρ
      rw [← mul_assoc, ← (Int.cast_commute D₁ (X : A)).eq]
      exact hmul _ hD₁m _ he0
    have hDI : ∀ β : B, (X : A) * (j β * e 0) ∈ Λ → β * D₂ ∈ R := by
      intro β hβ
      rw [← hsingleR]
      have : j (β * D₂) * e 0 = ((D₂ : A) * ↑X⁻¹) * ((X : A) * (j β * e 0)) := by
        rw [map_mul, map_intCast, ← (Int.cast_commute D₂ (j β)).eq, mul_assoc, mul_assoc,
          Units.inv_mul_cancel_left]
      rw [this]; exact hmul _ hD₂m _ hβ
    obtain ⟨m, hm⟩ := hsq {β | (X : A) * (j β * e 0) ∈ Λ}
      (by show (X : A) * (j 0 * e 0) ∈ Λ; simpa using h0)
      (fun x hx y hy => by
        show (X : A) * (j (x + y) * e 0) ∈ Λ
        rw [map_add, add_mul, mul_add]; exact hadd _ hx _ hy)
      (fun ρ hρ x hx => by
        show (X : A) * (j (ρ * x) * e 0) ∈ Λ
        rw [map_mul, mul_assoc]; exact hL ρ hρ _ hx)
      ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂,
        fun x hx => by
          show (X : A) * (j (((D₁ * D₂ : ℤ) : B) * x) * e 0) ∈ Λ
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₂ : B) * (x * D₁) := by push_cast; ring
          rw [this, map_mul, mul_assoc]
          exact hL _ (hRint D₂) _ (hDR x hx),
        fun x hx => by
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₁ : B) * (x * D₂) := by push_cast; ring
          rw [this]
          exact hRmul _ (hRint D₁) _ (hDI x hx)⟩
    refine ⟨m, ?_, ?_⟩
    · obtain ⟨γ, hγ, -⟩ := hrep 1
      have hγR : ∀ i, γ i ∈ R := (hmem γ).1 (hγ ▸ h1)
      have hjm : j (m : B) = ∑ i, j ((m : B) * γ i) * e i := by
        conv_lhs => rw [← mul_one (j (m : B)), hγ]
        rw [Finset.mul_sum]
        simp only [map_mul, mul_assoc]
      rw [hjm]
      exact hsum _ (fun i => (hm _).2 ⟨γ i, hγR i, rfl⟩)
    · obtain ⟨β, hβ, -⟩ := hrep (↑X⁻¹ : A)
      have hXinv : (X : A) * (∑ i, j (β i) * e i) ∈ Λ := by
        rw [← hβ, Units.mul_inv]; exact h1
      have hc : ∀ i, ∃ ρ ∈ R, β i = (m : B) * ρ := fun i => (hm _).1 (hA β hXinv i)
      choose ρ hρR hρeq using hc
      have : j (↑m⁻¹ : B) * (↑X⁻¹ : A) = ∑ i, j (ρ i) * e i := by
        rw [hβ, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← mul_assoc, ← map_mul, hρeq, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact (hmem ρ).2 hρR
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_lattice_basis_integrality : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by
  first | (exact @GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (exact GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (intros; apply GlobalTheory.AbsLattice.exists_unit_of_conj_stable  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_ring_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type) (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_eventually  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_finset_isIntB_one_tmul (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type)
    (b : Module.Basis κ ℚ M) (x : M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  have hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite :=
    (b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)
  refine ⟨hfin.toFinset, fun v hv i => ?_⟩
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  by_cases hi : b.repr x i = 0
  · rw [hi, map_zero]; exact zero_mem _
  · have h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i) := fun h =>
      hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))
    have h2 : v.valuation ℚ (b.repr x i) ≤ 1 := not_lt.1 h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)
    rw [← h3] at h2
    convert h2 using 2
    rfl

end GlobalTheory.AdicSpan
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_one_tmul_adic_integral_coords : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M) (x : M),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  first | (exact @GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul) | (exact GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul) | (intros; apply GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_int_smul_mem_adicCompletionIntegers_of_elt (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : v.adicCompletion ℚ) * a ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨d, hd, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [mul_comm]
  simpa using h

theorem exists_int_smul_isIntB : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  intro M _ _ κ b v y
  choose d hd0 hd using exists_int_smul_mem_adicCompletionIntegers_of_elt v
  set c := (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y with hc
  refine ⟨∏ i ∈ c.support, d (c i), Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _, fun i => ?_⟩
  rw [map_zsmul, ← hc, Finsupp.smul_apply, zsmul_eq_mul]
  by_cases hi : i ∈ c.support
  · rw [← Finset.prod_erase_mul _ _ hi, Int.cast_mul, mul_assoc]
    exact mul_mem (intCast_mem _ _) (hd _)
  · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]
    exact zero_mem _

end GlobalTheory.AdicSpan
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  first | (exact @GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (exact GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_int_smul_isIntB  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.LeftBasisBC

theorem existsUnique_coords_baseChange (K : Type) [CommRing K] [Algebra ℚ K]
    (L : Type) [Field L] [Algebra ℚ L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (h : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i)
    (y : K ⊗[ℚ] C) :
    ∃! β : Fin r → K ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (β i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
  let φ : (Fin r → L) →ₗ[ℚ] C :=
    { toFun := fun c => ∑ i, ι (c i) * e i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun q a => by simp [Finset.smul_sum] }
  have hφ : Function.Bijective φ := by
    rw [Function.bijective_iff_existsUnique]
    intro x
    obtain ⟨c, hc, hu⟩ := h x
    exact ⟨c, hc.symm, fun d hd => hu d hd.symm⟩
  let E : (Fin r → L) ≃ₗ[ℚ] C := LinearEquiv.ofBijective φ hφ
  let P : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] (Fin r → K ⊗[ℚ] L) :=
    TensorProduct.piRight ℚ ℚ K (fun _ : Fin r => L)
  let F : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] K ⊗[ℚ] C := TensorProduct.congr (LinearEquiv.refl ℚ K) E
  have key : ∀ z : K ⊗[ℚ] (Fin r → L), F z =
      ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (P z i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp [F, P, E, φ, TensorProduct.tmul_sum]
    | add a b ha hb =>
      simp only [map_add, ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  refine ⟨P (F.symm y), ?_, ?_⟩
  · show y = _
    rw [← key, LinearEquiv.apply_symm_apply]
  · intro β hβ
    have h1 := key (P.symm β)
    rw [LinearEquiv.apply_symm_apply, ← hβ] at h1
    rw [← h1, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem existsUnique_coords_adicCompletion :
    ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] C),
    ∃! β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) :=
  fun L _ _ C _ _ ι r e h v y =>
    existsUnique_coords_baseChange (v.adicCompletion ℚ) L C ι r e h y

end GlobalTheory.LeftBasisBC
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_left_basis_coords_adicCompletion : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] C),
    ∃! β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  first | (exact @GlobalTheory.LeftBasisBC.existsUnique_coords_adicCompletion) | (exact GlobalTheory.LeftBasisBC.existsUnique_coords_adicCompletion) | (intros; apply GlobalTheory.LeftBasisBC.existsUnique_coords_adicCompletion  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.LeftBasis

theorem isIntB_of_isIntB_of_repr {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) (v : HeightOneSpectrum ℤ)
    (h : ∀ k' k, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' k') k) ∈ v.adicCompletionIntegers ℚ)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) (hy : IsIntB v b' y) : IsIntB v b y := by
  intro k
  rw [eq_sum_tmul b' v y, map_sum, Finsupp.finset_sum_apply]
  refine sum_mem fun k' _ => ?_
  rw [repr_tmul_apply]
  exact mul_mem (hy k') (h k' k)

theorem isIntB_iff_eventually {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ y, IsIntB v b y ↔ IsIntB v b' y := by
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ' × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ',
      algebraMap ℚ (v.adicCompletion ℚ) (b'.repr (b t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv y => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  exact ⟨isIntB_of_isIntB_of_repr b' b v (fun k k' => hv.2 (k, k')) y,
    isIntB_of_isIntB_of_repr b b' v (fun k' k => hv.1 (k', k)) y⟩

theorem isIntB_sum_leftBasis_iff_eventually : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  intro L _ _ C _ _ ι r e he κ ℓ κ' b
  let Φl : (Fin r → L) →ₗ[ℚ] C :=
    ∑ i, (LinearMap.mulRight ℚ (e i)) ∘ₗ ι.toLinearMap ∘ₗ LinearMap.proj i
  have hΦl : ∀ c, Φl c = ∑ i, ι (c i) * e i := fun c => by
    simp [Φl, LinearMap.sum_apply]
  have hbij : Function.Bijective Φl := by
    refine ⟨fun c c' hcc => ?_, fun x => ?_⟩
    · obtain ⟨d, -, hd⟩ := he (Φl c)
      exact (hd c (hΦl c)).trans (hd c' (hcc.trans (hΦl c'))).symm
    · obtain ⟨d, hd, -⟩ := he x
      exact ⟨d, (hΦl d).trans hd.symm⟩
  let Φ := LinearEquiv.ofBijective Φl hbij
  let b' : Module.Basis (Σ _ : Fin r, κ) ℚ C := (Pi.basis fun _ : Fin r => ℓ).map Φ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  haveI : FiniteDimensional ℚ C := Module.Finite.of_basis b'
  haveI : Fintype κ' := FiniteDimensional.fintypeBasisIndex b
  have hsingle : ∀ (j : Fin r) (l : L), Φ (Pi.single j l) = ι l * e j := by
    intro j l
    show Φl _ = _
    rw [hΦl, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · simp
  have hrepr : ∀ (j : Fin r) (l : L) (i : Fin r) (a : κ),
      b'.repr (ι l * e j) ⟨i, a⟩ = ℓ.repr ((Pi.single j l : Fin r → L) i) a := by
    intro j l i a
    rw [← hsingle]
    simp [b', Module.Basis.map_repr, Pi.basis_repr]
  have hcoord : ∀ (v : HeightOneSpectrum ℤ) (j : Fin r) (z : v.adicCompletion ℚ ⊗[ℚ] L) (i : Fin r) (a : κ),
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
        (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι z * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr ((Pi.single j z : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) i) a := by
    intro v j z i a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, AlgHom.id_apply,
        repr_tmul_apply, hrepr]
      by_cases h : i = j
      · subst h; simp [repr_tmul_apply]
      · simp [h]
    | add x y hx hy =>
      rw [map_add, add_mul, LinearEquiv.map_add, Finsupp.add_apply, hx, hy, Pi.single_add, Pi.add_apply,
        LinearEquiv.map_add, Finsupp.add_apply]
  obtain ⟨S, hS⟩ := isIntB_iff_eventually b b'
  refine ⟨S, fun v hv β => ?_⟩
  have hy : ∀ (i : Fin r) (a : κ), (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
      (∑ j, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β j) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr (β i) a := by
    intro i a
    rw [map_sum, Finsupp.finset_sum_apply]
    simp_rw [hcoord]
    rw [← Finsupp.finset_sum_apply, ← map_sum]
    congr 2
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hS v hv]
  constructor
  · intro h i a
    rw [← hy]
    exact h ⟨i, a⟩
  · rintro h ⟨i, a⟩
    rw [hy]
    exact h i a

end GlobalTheory.AdicSpan.LeftBasis
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_basis_integral : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  first | (exact @GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (exact GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (intros; apply GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adicCompletion_tensor_matrixUnit_identity : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (N : ℕ) (l : Fin N → L) (c : Fin N → C) (i i' : Fin r),
    (∀ β : Fin r → L, ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L),
    ∑ k, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i'') *
          ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  intro L _ _ C _ _ ι r e N l c i i' h v β
  set φ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι with hφ
  let P : (Fin r → v.adicCompletion ℚ ⊗[ℚ] L) → Prop := fun β =>
    ∑ k, φ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', φ (β i'') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      φ (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
  have hzero : P 0 := by simp [P]
  have hadd : ∀ β₁ β₂, P β₁ → P β₂ → P (β₁ + β₂) := by
    intro β₁ β₂ h₁ h₂
    simp only [P, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  have hpure : ∀ (a : v.adicCompletion ℚ) (γ : Fin r → L), P (fun j => a ⊗ₜ[ℚ] γ j) := by
    intro a γ
    simp only [P, hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum]
    rw [h γ]
  have hsingle : ∀ j x, P (Pi.single j x) := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simpa using hzero
    | tmul a m =>
      have : (Pi.single j (a ⊗ₜ[ℚ] m) : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) =
          fun j' => a ⊗ₜ[ℚ] (Pi.single j m : Fin r → L) j' := by
        funext j'
        by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [this]; exact hpure a _
    | add x y hx hy =>
      rw [Pi.single_add]; exact hadd _ _ hx hy
  have hall : P (∑ j, Pi.single j (β j)) :=
    Finset.sum_induction _ P hadd hzero (fun j _ => hsingle j (β j))
  rw [Finset.univ_sum_single] at hall
  exact hall

end GlobalTheory
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_change_adic_tensor_identity : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (N : ℕ) (l : Fin N → L) (c : Fin N → C) (i i' : Fin r),
    (∀ β : Fin r → L, ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L),
    ∑ k, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i'') *
          ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  first | (exact @GlobalTheory.adicCompletion_tensor_matrixUnit_identity) | (exact GlobalTheory.adicCompletion_tensor_matrixUnit_identity) | (intros; apply GlobalTheory.adicCompletion_tensor_matrixUnit_identity  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_left_basis_through_algHom : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  intro L _ _ C _ _ _ ι
  letI : Module L C := Module.compHom C ι.toRingHom
  have hsmul : ∀ (l : L) (x : C), l • x = ι l * x := fun _ _ => rfl
  haveI : IsScalarTower ℚ L C := ⟨fun q l x => by
    rw [hsmul, hsmul, map_smul, smul_mul_assoc]⟩
  haveI : Module.Finite L C := Module.Finite.of_restrictScalars_finite ℚ L C
  let b := Module.finBasis L C
  refine ⟨Module.finrank L C, b, fun x => ⟨b.repr x, ?_, ?_⟩⟩
  · simp only [← hsmul]
    exact (b.sum_repr x).symm
  · intro c hc
    simp only [← hsmul] at hc
    rw [hc, b.repr_sum_self]

end GlobalTheory
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_over_subfield_embedding : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  first | (exact @GlobalTheory.exists_left_basis_through_algHom) | (exact GlobalTheory.exists_left_basis_through_algHom) | (intros; apply GlobalTheory.exists_left_basis_through_algHom  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LatStep

theorem isIntB_add' (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg' (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) :
    IsIntB v b (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem lattice_step : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    (minpoly G.F (γ : G.C)).Separable → ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι → (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X X' : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      IsIntB v b (↑X' * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X'⁻¹) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m * ↑X'⁻¹) ∧
        IsIntB v b (↑X' * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m⁻¹ * ↑X⁻¹) := by
  intro p _ G γ hdeg _hsep L _ _ ι hι hcent κ b
  let ℓ := Module.finBasis ℚ L
  obtain ⟨r, e, he⟩ := GlobalTheory.T.exists_basis_over_subfield_embedding L G.C ι
  have hE := fun i i' => GlobalTheory.T.exists_sum_two_sided_mul_eq_matrixUnit_unitaryDatum p G γ hdeg L ι hι hcent r e he i i'
  choose N l c hlc using hE
  have hl := fun (i i' : Fin r) (k : Fin (N i i')) => GlobalTheory.T.eventually_one_tmul_adic_integral_coords L _ ℓ (l i i' k)
  have hc := fun (i i' : Fin r) (k : Fin (N i i')) => GlobalTheory.T.eventually_one_tmul_adic_integral_coords G.C κ b (c i i' k)
  choose Sl hSl using hl
  choose Sc hSc using hc
  obtain ⟨S1, hS1⟩ := GlobalTheory.T.adicIntegralTensorBasis_ring_eventually G.C κ b
  obtain ⟨S2, hS2⟩ := GlobalTheory.T.adicIntegralTensorBasis_ring_eventually L _ ℓ
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.almost_all_places_basis_integral L G.C ι r e he _ ℓ κ b
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conj_of_integral_conj_generator p G γ hdeg L ι hι hcent κ b _ ℓ
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.fractional_ideal_integral_lattice L _ ℓ
  let SE : Finset (HeightOneSpectrum ℤ) := Finset.univ.biUnion (fun ii : Fin r × Fin r =>
    Finset.univ.biUnion (fun k : Fin (N ii.1 ii.2) => Sl ii.1 ii.2 k ∪ Sc ii.1 ii.2 k))
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ SE, ?_⟩
  intro v hv X X' hX hX'
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hvE⟩ := hv
  have hvE' : ∀ i i' k, v ∉ Sl i i' k ∧ v ∉ Sc i i' k := fun i i' k => by
    have : v ∉ Sl i i' k ∪ Sc i i' k := fun h => hvE (Finset.mem_biUnion.2
      ⟨(i, i'), Finset.mem_univ _, Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, h⟩⟩)
    simpa [Finset.mem_union, not_or] using this
  let jv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have key := GlobalTheory.T.order_lattice_basis_integrality (jv : v.adicCompletion ℚ ⊗[ℚ] L →+* v.adicCompletion ℚ ⊗[ℚ] G.C)
    {y | IsIntB v b y} {x | IsIntB v ℓ x} r (fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
    (isIntB_zero v b) (hS1 v hv1).1 (fun x hx y hy => isIntB_add' v b hx hy) (fun x hx => isIntB_neg' v b hx)
    (fun x hx y hy => (hS1 v hv1).2 x y hx hy)
    (isIntB_zero v ℓ) (hS2 v hv2).1 (fun x hx y hy => isIntB_add' v ℓ hx hy) (fun x hx => isIntB_neg' v ℓ hx)
    (fun x hx y hy => (hS2 v hv2).2 x y hx hy)
    (fun a => GlobalTheory.T.existsUnique_left_basis_coords_adicCompletion L G.C ι r e he v a) (hS3 v hv3)
    (fun i i' => ⟨N i i', fun k => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l i i' k,
      fun k => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c i i' k, fun k => hSl i i' k v (hvE' i i' k).1,
      fun k => hSc i i' k v (hvE' i i' k).2,
      fun β => GlobalTheory.T.basis_change_adic_tensor_identity L G.C ι r e (N i i') (l i i') (c i i') i i' (hlc i i') v β⟩)
    (fun a => by
      obtain ⟨D, hD, h⟩ := GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis G.C κ b v a
      exact ⟨D, hD, by simpa [zsmul_eq_mul] using h⟩)
    (fun I h0 hadd hmul hD => hS5 v hv5 I h0 hadd hmul hD)
  obtain ⟨m, hm1, hm2⟩ := key X (fun ρ hρ => hS4 v hv4 X hX ρ hρ)
  obtain ⟨m', hm1', hm2'⟩ := key X' (fun ρ hρ => hS4 v hv4 X' hX' ρ hρ)
  refine ⟨m * m'⁻¹, ?_, ?_⟩
  · have := (hS1 v hv1).2 _ _ hm1 hm2'
    convert this using 1
    simp only [RingHom.coe_coe, Units.val_mul, map_mul, mul_assoc, jv]
  · have := (hS1 v hv1).2 _ _ hm1' hm2
    convert this using 1
    simp only [RingHom.coe_coe, _root_.mul_inv_rev, inv_inv, Units.val_mul, map_mul, mul_assoc, jv]

end GlobalTheory.LatStep
end
end
