module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IrreducibleSpacePrimeSpectrumAway

@[expose] public section

open PowerSeries IsLocalRing

noncomputable section

namespace GlobalTheory.ChartRing

section Local

variable {O : Type*} [CommRing O] [IsLocalRing O]

variable (O) in
theorem maximalIdeal_eq_comap :
    maximalIdeal O⟦X⟧ = (maximalIdeal O).comap (constantCoeff (R := O)) := by
  ext f
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

theorem X_mem_maximalIdeal : (X : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by
  simp [maximalIdeal_eq_comap]

theorem C_mem_maximalIdeal_iff {a : O} : (C a : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ ↔ a ∈ maximalIdeal O := by
  rw [maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_C]

instance isAdicComplete_maximalIdeal [IsAdicComplete (maximalIdeal O) O] :
    IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := by
  rw [maximalIdeal_eq_comap]
  exact isAdicComplete_comap_constantCoeff _

end Local

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem maximalIdeal_eq_span (hπ : Irreducible π) :
    maximalIdeal O⟦X⟧ = Ideal.span {C π, X} := by
  rw [maximalIdeal_eq_comap, ← map_C_sup_span_X, hπ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.span_insert]

theorem eq_span_X_or_eq_maximalIdeal (P : Ideal O⟦X⟧) [hP : P.IsPrime] (hX : X ∈ P) :
    P = Ideal.span {X} ∨ P = maximalIdeal O⟦X⟧ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  by_cases h : C π ∈ P
  · refine Or.inr (le_antisymm (le_maximalIdeal hP.ne_top) ?_)
    rw [maximalIdeal_eq_span hπ, Ideal.span_le]
    rintro _ (rfl | rfl)
    exacts [h, hX]
  · refine Or.inl (le_antisymm (fun f hf => ?_) (by rwa [Ideal.span_singleton_le_iff_mem]))
    rw [mem_span_X_iff]
    by_contra h0
    have h1 : C (constantCoeff f) ∈ P := by
      rw [← sub_eq_iff_eq_add'.mpr f.eq_X_mul_shift_add_const]
      exact sub_mem hf (P.mul_mem_right _ hX)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
    rw [hu, map_mul, map_pow, Ideal.unit_mul_mem_iff_mem _ (u.isUnit.map _)] at h1
    exact h (hP.mem_of_pow_mem n h1)

theorem isPrincipal_of_ne_maximalIdeal (P : Ideal O⟦X⟧) [P.IsPrime]
    (hP : P ≠ maximalIdeal O⟦X⟧) : P.IsPrincipal := by
  by_cases hX : X ∈ P
  · rw [(eq_span_X_or_eq_maximalIdeal P hX).resolve_right hP]
    exact ⟨⟨X, rfl⟩⟩
  · obtain ⟨_, h⟩ := (IsPrincipalIdealRing.principal (P.map constantCoeff)).principal
    obtain ⟨_, rfl, _, h⟩ := exist_eq_span_eq_ncard_of_X_notMem hX h.symm (Set.finite_singleton _)
    simp only [Set.ncard_singleton, Set.ncard_eq_one] at h
    obtain ⟨a, rfl⟩ := h
    exact ⟨⟨a, rfl⟩⟩

instance isRegularLocalRing : IsRegularLocalRing O⟦X⟧ :=
  IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ <| by
    rw [ringKrullDim_eq_two]
    exact_mod_cast spanFinrank_maximalIdeal_le O

theorem isPrincipalIdealRing_of_isLocalization (M : Submonoid O⟦X⟧) {f : O⟦X⟧} (hfM : f ∈ M)
    (hf : f ∈ maximalIdeal O⟦X⟧) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S] [IsLocalization M S] :
    IsPrincipalIdealRing S := by
  refine IsPrincipalIdealRing.of_prime fun P hP => ?_
  have hne : P.under O⟦X⟧ ≠ maximalIdeal O⟦X⟧ := by
    intro h
    rw [← h] at hf
    exact hP.ne_top (P.eq_top_of_isUnit_mem hf (IsLocalization.map_units S (⟨f, hfM⟩ : M)))
  obtain ⟨⟨a, ha⟩⟩ := isPrincipal_of_ne_maximalIdeal _ hne
  rw [← IsLocalization.map_under M S P, ha, Ideal.submodule_span_eq, Ideal.map_span,
    Set.image_singleton]
  exact ⟨⟨_, rfl⟩⟩

theorem isPrincipalIdealRing_away {f : O⟦X⟧} (hf : f ∈ maximalIdeal O⟦X⟧)
    (S : Type*) [CommRing S] [Algebra O⟦X⟧ S] [IsLocalization.Away f S] :
    IsPrincipalIdealRing S :=
  isPrincipalIdealRing_of_isLocalization (Submonoid.powers f) (Submonoid.mem_powers f) hf S

section AwayUniformiser

variable (hπ : Irreducible π) (T : Type*) [CommRing T] [Algebra O⟦X⟧ T]
  [IsLocalization.Away (C π : O⟦X⟧) T]
include hπ

theorem isPrincipalIdealRing_away_C : IsPrincipalIdealRing T :=
  isPrincipalIdealRing_away (C_mem_maximalIdeal_iff.2 hπ.not_isUnit) T

end AwayUniformiser

section Eval

variable [IsAdicComplete (maximalIdeal O) O]

variable (hπ : Irreducible π)

@[simp] theorem ev_X : ev hπ X = π := evalAdic_X _ _

@[simp] theorem ev_C (a : O) : ev hπ (C a) = a := (ev hπ).commutes a

instance isLocalHom_ev : IsLocalHom (ev hπ) :=
  isLocalHom_of_X_mem _ (by rw [ev_X]; exact hπ.not_isUnit)

instance isLocalHom_ev_toRingHom : IsLocalHom (ev hπ : O⟦X⟧ →+* O) :=
  ⟨(isLocalHom_ev hπ).map_nonunit⟩

variable (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
  (U : Type*) [CommRing U] [Algebra O⟦X⟧ U] [IsLocalization.Away (C π * X : O⟦X⟧) U]

@[simp] theorem evFrac_algebraMap (f : O⟦X⟧) :
    evFrac hπ K U (algebraMap O⟦X⟧ U f) = algebraMap O K (ev hπ f) :=
  IsLocalization.Away.lift_eq _ _ _

end Eval

end DVR

end GlobalTheory.ChartRing
