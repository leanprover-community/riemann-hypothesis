import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem translate_mem_aug_of_not_intertwine {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (J : Set G) (θ : G → ℂ) (u : V) (hu : IsEig π J θ u) (y j : G) (hj : j ∈ J) (hc : y * j * y⁻¹ ∈ J)
    (hne : θ j ≠ θ (y * j * y⁻¹)) : π y u ∈ aug π J θ := by
  have h1 : π (y * j * y⁻¹) (π y u) = θ j • π y u := by
    have : π (y * j * y⁻¹) (π y u) = π y (π j u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [this, hu j hj, map_smul]
  have h2 : (θ j - θ (y * j * y⁻¹)) • π y u ∈ aug π J θ := by
    apply Submodule.subset_span
    exact ⟨_, hc, π y u, by rw [h1, sub_smul]⟩
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne)).mp h2

theorem eig_eq_zero_of_mem_aug_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ →
    Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) →
    ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ hJ hN hy u hu he
  classical
  obtain ⟨R, h1, hR, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ N _ hN u hu
  simp only [inv_one, one_smul] at hs
  refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ J θ hJ).1 u ?_ he
  rw [← Finset.sum_filter_add_sum_filter_not R (fun y => y ∈ J ∧ θ y = 1)] at hs
  have hA : ∑ y ∈ R.filter (fun y => y ∈ J ∧ θ y = 1), π y u
      = ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) • u := by
    rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro y hy'
    obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hy'
    rw [he y a, b, one_smul]
  have hB : ∑ y ∈ R.filter (fun y => ¬ (y ∈ J ∧ θ y = 1)), π y u ∈ aug π J θ := by
    refine Submodule.sum_mem _ fun y hy' => ?_
    obtain ⟨a, b⟩ := Finset.mem_filter.mp hy'
    obtain ⟨j, hj, hc, hne⟩ := (hy y (hR y a)).resolve_left b
    exact translate_mem_aug_of_not_intertwine π J θ u he y j hj hc hne
  have hc : ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, Finset.mem_filter.mpr ⟨h1, hJ.one, hJ.val_one⟩⟩
  rw [← Submodule.smul_mem_iff _ hc, ← hA, eq_neg_of_add_eq_zero_left hs]
  exact Submodule.neg_mem _ hB

end GlobalTheory.PsType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ → Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  atlas_forward_decl GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem isEig_translate_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  intro G V _ _ _ _ _ π hπ J N₀ N₁ θ z hJ hN hsub hconj hdec u u' hu hu' hd
  have hmul : ∀ (a b : G) (v : V), π a (π b v) = π (a * b) v := fun a b v => by
    rw [map_mul]; rfl
  have hw' : IsEig π N₀ (fun _ => 1) (π z u') := by
    intro y hy
    have h1 : z⁻¹ * y * z ∈ N₁ := (hconj _).2 (by
      have : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [this]; exact hy)
    have h2 := hu' _ h1
    have h3 : y * z = z * (z⁻¹ * y * z) := by group
    rw [hmul, h3, ← hmul, h2, map_smul]
  have hmap : ∀ x ∈ aug π N₁ (fun _ => 1), π z x ∈ aug π N₀ (fun _ => 1) := by
    intro x hx
    have : aug π N₁ (fun _ => 1) ≤ (aug π N₀ (fun _ => 1)).comap (π z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, hh, w, rfl⟩
      refine Submodule.subset_span ⟨z * h * z⁻¹, (hconj h).1 hh, π z w, ?_⟩
      rw [map_sub, map_smul, hmul, hmul]
      congr 3
      group
    exact this hx
  have hww : π z u - π z u' ∈ aug π N₀ (fun _ => 1) := by
    rw [← map_sub]; exact hmap _ hd
  obtain ⟨R, hR1, hRJ, hS⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ J θ hJ (π z u)
  have hterm : ∀ j ∈ R, (θ j)⁻¹ • π j (π z u) - π z u ∈ aug π N₀ (fun _ => 1) := by
    intro j hj
    have hjJ := hRJ j hj
    obtain ⟨y, hy, h1, h2⟩ := hdec j hjJ
    have hne : θ j ≠ 0 := by
      intro h0
      have := hJ.val_mul j hjJ j⁻¹ (hJ.inv j hjJ)
      rw [mul_inv_cancel, hJ.val_one, h0, zero_mul] at this
      exact one_ne_zero this
    have h3 := hu _ h1
    have h4 : j * z = y * (z * (z⁻¹ * (y⁻¹ * j) * z)) := by group
    have h5 : π j (π z u) = θ j • π y (π z u) := by
      rw [hmul, h4, ← hmul, ← hmul, h3, h2, map_smul, map_smul]
    rw [h5, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact Submodule.subset_span ⟨y, hy, π z u, by rw [one_smul]⟩
  set S : V := ∑ j ∈ R, (θ j)⁻¹ • π j (π z u) with hSdef
  have hc : (R.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, hR1⟩).ne'
  have hA : S - (R.card : ℂ) • π z u ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.sum_mem _ hterm
    rwa [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at this
  have hB : S - (R.card : ℂ) • π z u' ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.add_mem _ hA (Submodule.smul_mem _ (R.card : ℂ) hww)
    rwa [smul_sub, sub_add_sub_cancel] at this
  have hC : IsEig π N₀ (fun _ => 1) (S - (R.card : ℂ) • π z u') := by
    intro y hy
    rw [map_sub, map_smul, hS y (hsub y hy).1, (hsub y hy).2, hw' y hy]
    simp
  have h0 := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ N₀ _ hN).1 _ hB hC
  have hE : π z u' = (R.card : ℂ)⁻¹ • S := by
    rw [sub_eq_zero.1 h0, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro j hj
  rw [hE, map_smul, hS j hj, smul_comm]

end GlobalTheory.PsType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEig_apply_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  atlas_forward_decl GlobalTheory.PsType.isEig_translate_of_sub_mem_aug
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem map_mem_aug_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (A B : Set G) (z : G) (h : ∀ y ∈ B, z * y * z⁻¹ ∈ A) (u : V) (hu : u ∈ aug π B (fun _ => 1)) :
    π z u ∈ aug π A (fun _ => 1) := by
  have hle : aug π B (fun _ => 1) ≤ (aug π A (fun _ => 1)).comap (π z) := by
    unfold aug
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, hy, w, rfl⟩
    refine Submodule.subset_span ⟨z * y * z⁻¹, h y hy, π z w, ?_⟩
    have e : π (z * y * z⁻¹) (π z w) = π z (π y w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [e, map_sub, map_smul]
  exact hle hu

theorem aug_mono_set {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    {A B : Set G} (θ : G → ℂ) (h : A ⊆ B) : aug π A θ ≤ aug π B θ := by
  unfold aug
  refine Submodule.span_mono ?_
  rintro x ⟨y, hy, w, rfl⟩
  exact ⟨y, h hy, w, rfl⟩

theorem eig_eq_zero_of_mem_aug_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ z hJ hN hmono h0 hconj h1 hz m
  induction m with
  | zero =>
    intro u hu heig
    refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 0) (fun _ => 1) (hN 0)).1 u hu ?_
    intro y hy
    rw [heig y (h0 y hy).1, (h0 y hy).2]
  | succ m ih =>
    intro u hu heig
    obtain ⟨u', hu'eig, hsub⟩ := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 1) (fun _ => 1) (hN 1)).2 u
    have hsub' : u - u' ∈ aug π (N (m + 1)) (fun _ => 1) :=
      aug_mono_set π _ (hmono (Nat.succ_le_succ (Nat.zero_le m))) hsub
    have hu' : u' ∈ aug π (N (m + 1)) (fun _ => 1) := by
      have := Submodule.sub_mem _ hu hsub'
      simpa using this
    have hzu : π z u' ∈ aug π (N m) (fun _ => 1) :=
      map_mem_aug_of_conj π (N m) (N (m + 1)) z (fun y hy => (hconj m y).1 hy) u' hu'
    have hzeig : IsEig π J θ (π z u') :=
      GlobalTheory.T.isEig_apply_of_sub_mem_aug G V π hπ J (N 0) (N 1) θ z hJ (hN 0) h0 (hconj 0) hz u u' heig hu'eig hsub
    have hz0 : π z u' = 0 := ih _ hzu hzeig
    have hu0 : u' = 0 := by
      have e : π z⁻¹ (π z u') = u' := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      rw [← e, hz0, map_zero]
    rw [hu0, sub_zero] at hsub
    exact GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine G V π hπ J (N 1) θ hJ (hN 1) h1 u hsub heig

end GlobalTheory.PsType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  atlas_forward_decl GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain
end
