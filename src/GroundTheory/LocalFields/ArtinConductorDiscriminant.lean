import Mathlib
import GroundTheory.LocalFields.ArtinConductorInduced
import GroundTheory.LocalFields.ConductorMatch

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section HasseArf

theorem exists_int_eq_of_forall_upperRamificationGroup_ne_of_isAbelianGalois
    {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M] [IsAbelianGalois K M] {v : ℝ}
    (h : ∀ w, v < w → upperRamificationGroup K M w ≠ upperRamificationGroup K M v) :
    ∃ m : ℤ, v = m := by
  let ι : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E : IntermediateField K (SeparableClosure K) := ι.fieldRange
  let e : M ≃ₐ[K] E := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K E := IsAbelianGalois.of_algHom (M := M) e.symm.toAlgHom
  apply exists_int_eq_of_forall_upperRamificationGroup_ne E
  intro w hw heq
  apply h w hw
  rw [← map_upperRamificationGroup_autCongr e w, ← map_upperRamificationGroup_autCongr e v] at heq
  exact Subgroup.map_injective e.autCongr.injective heq

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in

theorem upperRamificationGroup_le_of_herbrandPhi_lt {j : ℕ} {w : ℝ} (hw : herbrandPhi K L j < w) :
    upperRamificationGroup K L w ≤ lowerRamificationGroup K L ((j : ℤ) + 1) := by
  have hψ : (j : ℝ) < herbrandPsi K L w := by
    rw [← herbrandPsi_herbrandPhi (K := K) (L := L) (j : ℝ)]
    exact herbrandPsi_strictMono hw
  show lowerRamificationGroup K L ⌈herbrandPsi K L w⌉ ≤ _
  exact lowerRamificationGroup_antitone K L (Int.add_one_le_iff.mpr (Int.lt_ceil.mpr hψ))

omit [IsGalois K L] in

theorem upperRamificationGroup_herbrandPhi_natCast (j : ℕ) :
    upperRamificationGroup K L (herbrandPhi K L j) = lowerRamificationGroup K L j := by
  rw [upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]

theorem exists_int_herbrandPhi_eq_of_monoidHom (ψ : (L ≃ₐ[K] L) →* ℂˣ) {j : ℕ}
    (hj : ¬ lowerRamificationGroup K L j ≤ ψ.ker)
    (hj1 : lowerRamificationGroup K L ((j : ℤ) + 1) ≤ ψ.ker) :
    ∃ m : ℤ, herbrandPhi K L j = m := by
  set M := IntermediateField.fixedField ψ.ker
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).ker = ψ.ker := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hcomm : ∀ a b : (L ≃ₐ[K] L) ⧸ ψ.ker, a * b = b * a := fun a b ↦
    QuotientGroup.kerLift_injective ψ (by rw [map_mul, map_mul, mul_comm])
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun a b ↦ by
    obtain ⟨a', rfl⟩ := (IsGalois.normalAutEquivQuotient ψ.ker).surjective a
    obtain ⟨b', rfl⟩ := (IsGalois.normalAutEquivQuotient ψ.ker).surjective b
    rw [← map_mul, ← map_mul, hcomm]⟩⟩
  have : IsAbelianGalois K M := { }
  apply exists_int_eq_of_forall_upperRamificationGroup_ne_of_isAbelianGalois (K := K) (M := M)
  intro w hw heq
  have h1 : upperRamificationGroup K M w = ⊥ := by
    rw [← map_upperRamificationGroup M w, Subgroup.map_eq_bot_iff, hker]
    exact (upperRamificationGroup_le_of_herbrandPhi_lt hw).trans hj1
  have h2 : upperRamificationGroup K M (herbrandPhi K L j) ≠ ⊥ := by
    rw [← map_upperRamificationGroup M, Ne, Subgroup.map_eq_bot_iff, hker,
      upperRamificationGroup_herbrandPhi_natCast]
    exact hj
  exact h2 (heq ▸ h1)

end HasseArf

section OneDim

variable {G : Type*} [Group G]

def charRep (ψ : G →* ℂˣ) : Representation ℂ G ℂ :=
  (DistribMulAction.toModuleEnd ℂ ℂ).comp ψ

@[simp]
theorem charRep_apply (ψ : G →* ℂˣ) (g : G) (v : ℂ) : charRep ψ g v = (ψ g : ℂ) * v :=
  rfl

theorem character_charRep (ψ : G →* ℂˣ) (g : G) : (charRep ψ).character g = ψ g := by
  have h : charRep ψ g = (ψ g : ℂ) • LinearMap.id := by
    ext
    simp
  rw [Representation.character, h, map_smul, LinearMap.trace_id, finrank_self]
  simp

open Classical in

theorem finrank_invariants_charRep_comp (ψ : G →* ℂˣ) (S : Subgroup G) :
    finrank ℂ (Representation.invariants ((charRep ψ).comp S.subtype)) = if S ≤ ψ.ker then 1 else 0 := by
  split_ifs with h
  · have htop : Representation.invariants ((charRep ψ).comp S.subtype) = ⊤ := by
      ext v
      simp only [Submodule.mem_top, iff_true]
      intro g
      have : ψ g = 1 := h g.2
      simp [this]
    rw [htop, finrank_top, finrank_self]
  · have hbot : Representation.invariants ((charRep ψ).comp S.subtype) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨g, hg, hψ⟩ := SetLike.not_le_iff_exists.mp h
      have hv' : (ψ g : ℂ) * v = v := hv ⟨g, hg⟩
      have hne : (ψ g : ℂ) ≠ 1 := fun h1 ↦ hψ (MonoidHom.mem_ker.mpr (Units.val_eq_one.mp h1))
      have : ((ψ g : ℂ) - 1) * v = 0 := by rw [sub_mul, hv', one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
    rw [hbot, finrank_bot]

end OneDim

section Conductor

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

open Classical in

theorem artinConductor_charRep_eq_sum (ψ : (L ≃ₐ[K] L) →* ℂˣ) {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    artinConductor (charRep ψ) = ∑ i ∈ Finset.range N,
      if lowerRamificationGroup K L i ≤ ψ.ker then 0
      else (Nat.card (lowerRamificationGroup K L i) / Nat.card (lowerRamificationGroup K L 0) : ℚ) := by
  rw [artinConductor_eq_sum _ hN]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finrank_invariants_charRep_comp, finrank_self]
  split_ifs <;> simp

theorem herbrandPhi_natCast_eq_sum (n : ℕ) :
    herbrandPhi K L n = ∑ i ∈ Finset.range n,
      (Nat.card (lowerRamificationGroup K L ((i : ℤ) + 1)) : ℝ) /
        Nat.card (lowerRamificationGroup K L 0) := by
  induction n with
  | zero => simp [herbrandPhi_zero]
  | succ n ih =>
    have h := herbrandPhi_of_mem_Icc (K := K) (L := L) n (u := (n : ℝ) + 1)
      ⟨by linarith, le_rfl⟩
    have hrel := relIndex_mul_card_inf (lowerRamificationGroup K L ((n : ℤ) + 1))
      (lowerRamificationGroup K L 0)
    rw [inf_of_le_left (lowerRamificationGroup_antitone K L (by omega))] at hrel
    have hc : (Nat.card (lowerRamificationGroup K L ((n : ℤ) + 1)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hr : ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
      intro h0
      have h0' : (lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
          (lowerRamificationGroup K L 0) = 0 := by exact_mod_cast h0
      rw [h0', zero_mul] at hrel
      exact Nat.card_pos.ne' hrel.symm
    push_cast
    rw [h, ih, Finset.sum_range_succ, add_sub_cancel_left, ← hrel]
    push_cast
    field_simp

theorem exists_lowerRamificationGroup_jump (ψ : (L ≃ₐ[K] L) →* ℂˣ)
    (h0 : ¬ lowerRamificationGroup K L 0 ≤ ψ.ker) :
    ∃ j : ℕ, ¬ lowerRamificationGroup K L j ≤ ψ.ker ∧
      lowerRamificationGroup K L ((j : ℤ) + 1) ≤ ψ.ker := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have hex : ∃ n : ℕ, lowerRamificationGroup K L n ≤ ψ.ker :=
    ⟨N, by rw [hN N le_rfl]; exact bot_le⟩
  set k := Nat.find hex with hk
  have hk0 : k ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hk, h] at this
    exact h0 (by exact_mod_cast this)
  refine ⟨k - 1, Nat.find_min hex (by omega), ?_⟩
  have := Nat.find_spec hex
  rw [← hk] at this
  convert this using 2
  omega

theorem artinConductor_charRep_eq_one_add_herbrandPhi (ψ : (L ≃ₐ[K] L) →* ℂˣ) {j : ℕ}
    (hj : ¬ lowerRamificationGroup K L j ≤ ψ.ker)
    (hj1 : lowerRamificationGroup K L ((j : ℤ) + 1) ≤ ψ.ker) :
    (artinConductor (charRep ψ) : ℝ) = 1 + herbrandPhi K L j := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have hjN : j < N := by
    by_contra h
    apply hj
    rw [hN j (by exact_mod_cast not_lt.mp h)]
    exact bot_le
  have hiff : ∀ i : ℕ, lowerRamificationGroup K L i ≤ ψ.ker ↔ ¬ i ≤ j := by
    intro i
    constructor
    · intro hi hij
      exact hj ((lowerRamificationGroup_antitone K L (by exact_mod_cast hij)).trans hi)
    · intro hij
      exact (lowerRamificationGroup_antitone K L (by omega)).trans hj1
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [artinConductor_charRep_eq_sum ψ (hN N le_rfl)]
  simp_rw [hiff, ite_not]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.range N).filter (fun i ↦ i ≤ j) = Finset.range (j + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilt, Finset.sum_range_succ', herbrandPhi_natCast_eq_sum]
  push_cast
  rw [div_self h0, add_comm]

theorem exists_nat_artinConductor_charRep_eq [IsGalois K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    ∃ n : ℕ, artinConductor (charRep ψ) = n := by
  by_cases h0 : lowerRamificationGroup K L 0 ≤ ψ.ker
  · refine ⟨0, ?_⟩
    rw [Nat.cast_zero, artinConductor_eq_zero_iff]
    intro σ hσ
    have h1 : ψ σ = 1 := h0 hσ
    ext
    simp [h1]
  obtain ⟨j, hj, hj1⟩ := exists_lowerRamificationGroup_jump ψ h0
  obtain ⟨m, hm⟩ := exists_int_herbrandPhi_eq_of_monoidHom ψ hj hj1
  have hpos : (0 : ℝ) ≤ herbrandPhi K L j := by
    rw [← herbrandPhi_zero (K := K) (L := L)]
    exact herbrandPhi_strictMono.monotone (Nat.cast_nonneg j)
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ m := hm ▸ hpos
    exact_mod_cast this
  refine ⟨(1 + m).toNat, ?_⟩
  have h := artinConductor_charRep_eq_one_add_herbrandPhi ψ hj hj1
  rw [hm] at h
  have hn : (((1 + m).toNat : ℕ) : ℝ) = 1 + m := by
    have h2 : (((1 + m).toNat : ℕ) : ℤ) = 1 + m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast h2
  have h' : ((artinConductor (charRep ψ) : ℚ) : ℝ) = ((((1 + m).toNat : ℕ) : ℚ) : ℝ) := by
    rw [Rat.cast_natCast, hn, h]
  exact Rat.cast_injective h'

end Conductor

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

section Bot

theorem ne_bot_of_nontrivial_aut {F E : Type*} [Field F] [Field E] [Algebra F E]
    (M : IntermediateField F E) [FiniteDimensional F M] [IsGalois F M]
    (hM : Nontrivial (M ≃ₐ[F] M)) : M ≠ ⊥ := by
  rintro rfl
  have h1 : Nat.card ((⊥ : IntermediateField F E) ≃ₐ[F] (⊥ : IntermediateField F E)) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, IntermediateField.finrank_bot]
  have := Finite.one_lt_card_iff_nontrivial.mpr hM
  omega

end Bot

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Jump

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isGreatest_artinConductor_charRep_sub_one (ψ : (L ≃ₐ[K] L) →* ℂˣ) (hψ : ψ ≠ 1) :
    IsGreatest {v : ℝ | ¬ upperRamificationGroup K L v ≤ ψ.ker}
      ((artinConductor (charRep ψ) : ℝ) - 1) := by
  by_cases h0 : lowerRamificationGroup K L 0 ≤ ψ.ker
  · have hf : artinConductor (charRep ψ) = 0 := by
      rw [artinConductor_eq_zero_iff]
      intro σ hσ
      have h1 : ψ σ = 1 := h0 hσ
      ext
      simp [h1]
    rw [hf, Rat.cast_zero, zero_sub]
    refine ⟨?_, fun v hv ↦ ?_⟩
    · show ¬ upperRamificationGroup K L (-1) ≤ ψ.ker
      rw [upperRamificationGroup_of_nonpos (by norm_num), lowerRamificationGroupReal_eq_top le_rfl]
      intro htop
      apply hψ
      refine MonoidHom.ext fun σ ↦ ?_
      rw [MonoidHom.one_apply]
      exact htop (Subgroup.mem_top σ)
    · by_contra hlt
      rw [not_le] at hlt
      apply hv
      refine le_trans ?_ h0
      show lowerRamificationGroup K L ⌈herbrandPsi K L v⌉ ≤ _
      apply lowerRamificationGroup_antitone
      have : -1 < herbrandPsi K L v := by
        rw [← herbrandPsi_of_nonpos (K := K) (L := L) (show (-1 : ℝ) ≤ 0 by norm_num)]
        exact herbrandPsi_strictMono hlt
      exact Int.le_ceil_iff.mpr (by push_cast; linarith)
  · obtain ⟨j, hj, hj1⟩ := exists_lowerRamificationGroup_jump ψ h0
    rw [artinConductor_charRep_eq_one_add_herbrandPhi ψ hj hj1, add_sub_cancel_left]
    refine ⟨?_, fun v hv ↦ ?_⟩
    · show ¬ upperRamificationGroup K L _ ≤ ψ.ker
      rw [upperRamificationGroup_herbrandPhi_natCast]
      exact hj
    · by_contra hlt
      rw [not_le] at hlt
      exact hv ((upperRamificationGroup_le_of_herbrandPhi_lt hlt).trans hj1)


end Jump

section Match

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]

theorem upperRamificationGroup_le_ker_comp_iff (r : (L ≃ₐ[K] L) →* (M ≃ₐ[K] M))
    (hr : ∀ v, (upperRamificationGroup K L v).map r = upperRamificationGroup K M v)
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hψ : Function.Injective ψ) (v : ℝ) :
    upperRamificationGroup K L v ≤ (ψ.comp r).ker ↔ upperRamificationGroup K M v = ⊥ := by
  have hker : (ψ.comp r).ker = r.ker := by
    ext σ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h ↦ hψ (h.trans ψ.map_one.symm), fun h ↦ by rw [h, map_one]⟩
  rw [hker, ← hr v, Subgroup.map_eq_bot_iff]

theorem isGreatest_artinConductor_charRep_comp_sub_one (r : (L ≃ₐ[K] L) →* (M ≃ₐ[K] M))
    (hr : ∀ v, (upperRamificationGroup K L v).map r = upperRamificationGroup K M v)
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hψ : Function.Injective ψ) (hM : Nontrivial (M ≃ₐ[K] M)) :
    IsGreatest {v : ℝ | upperRamificationGroup K M v ≠ ⊥}
      ((artinConductor (charRep (ψ.comp r)) : ℝ) - 1) := by
  have hne : ψ.comp r ≠ 1 := by
    intro h1
    have htop : upperRamificationGroup K M (-1) = ⊥ := by
      rw [← upperRamificationGroup_le_ker_comp_iff r hr ψ hψ, h1, MonoidHom.ker_one]
      exact le_top
    rw [upperRamificationGroup_of_nonpos (by norm_num), lowerRamificationGroupReal_eq_top le_rfl]
      at htop
    exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup (M ≃ₐ[K] M))).mp
      (Subgroup.topEquiv.symm.nontrivial) htop
  have h := isGreatest_artinConductor_charRep_sub_one (ψ.comp r) hne
  have hset : {v : ℝ | ¬ upperRamificationGroup K L v ≤ (ψ.comp r).ker} =
      {v : ℝ | upperRamificationGroup K M v ≠ ⊥} := by
    ext v
    simp only [Set.mem_ofPred_eq, upperRamificationGroup_le_ker_comp_iff r hr ψ hψ]
  rwa [hset] at h

end Match

section Conductor

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

theorem artinConductor_charRep_comp_restrictAut_eq_conductor {L M : IntermediateField K Ω}
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsAbelianGalois K M]
    (h : M ≤ L) (ψ : (M ≃ₐ[K] M) →* ℂˣ) (hψ : Function.Injective ψ) :
    artinConductor (charRep (ψ.comp (restrictAut h))) = conductor M := by
  have hr := map_upperRamificationGroup_restrictAut (K := K) (Ω := Ω) h
  rcases subsingleton_or_nontrivial (M ≃ₐ[K] M) with hM | hM
  · have hbot : ∀ v, upperRamificationGroup K M v = ⊥ := fun v ↦ Subsingleton.elim _ _
    have hc : conductor M = 0 := by
      have := (upperRamificationGroup_natCast_eq_bot_iff M 0).mp (hbot _)
      omega
    have hf : artinConductor (charRep (ψ.comp (restrictAut h))) = 0 := by
      rw [artinConductor_eq_zero_iff]
      intro σ _
      have h1 : restrictAut h σ = 1 := Subsingleton.elim _ _
      ext
      simp [h1]
    rw [hc, hf, Nat.cast_zero]
  · have h1 := isGreatest_artinConductor_charRep_comp_sub_one (restrictAut h) hr ψ hψ hM
    have h2 := isGreatest_conductor_sub_one M (ne_bot_of_nontrivial_aut M hM)
    have h3 := h1.unique h2
    have h4 : ((artinConductor (charRep (ψ.comp (restrictAut h))) : ℚ) : ℝ) =
        ((conductor M : ℚ) : ℝ) := by
      rw [Rat.cast_natCast]
      linarith
    exact Rat.cast_injective h4

theorem artinConductor_charRep_eq_conductor (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (ψ : (L ≃ₐ[K] L) →* ℂˣ) (hψ : Function.Injective ψ) :
    artinConductor (charRep ψ) = conductor L := by
  have h := artinConductor_charRep_comp_restrictAut_eq_conductor (le_refl L) ψ hψ
  have hid : restrictAut (le_refl L) = MonoidHom.id (L ≃ₐ[K] L) := by
    ext σ x
    rw [restrictAut_apply]
    rfl
  rwa [hid, MonoidHom.comp_id] at h

end Conductor

section Dual

variable {G : Type*} [Group G]

theorem addChar_apply_ne_zero (χ : AddChar (Additive G) ℂ) (a : Additive G) : χ a ≠ 0 := by
  intro h
  have := χ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

def monoidHomEquivAddChar : (G →* ℂˣ) ≃ AddChar (Additive G) ℂ where
  toFun ψ :=
    { toFun := fun a ↦ (ψ a.toMul : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b ↦ by simp }
  invFun χ :=
    { toFun := fun g ↦ Units.mk0 (χ (Additive.ofMul g)) (addChar_apply_ne_zero χ _)
      map_one' := Units.ext (by simp)
      map_mul' := fun g h ↦ Units.ext (by simp [AddChar.map_add_eq_mul]) }
  left_inv ψ := by
    ext g
    simp
  right_inv χ := by
    ext a
    simp

end Dual

section Abelian

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsAbelianGalois K L]

end Abelian

section Monomial

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_nat_charArtinConductor_inducedFun (M : IntermediateField K L)
    (ψ : (L ≃ₐ[M] L) →* ℂˣ) :
    ∃ n : ℕ, charArtinConductor K L (inducedFun fun h ↦ (ψ h : ℂ)) = n := by
  obtain ⟨m, hm⟩ := exists_nat_artinConductor_charRep_eq ψ
  refine ⟨residueDegree K M * differentExponent K M + residueDegree K M * m, ?_⟩
  have h1 : (fun h ↦ (ψ h : ℂ)) = (charRep ψ).character :=
    funext fun h ↦ (character_charRep ψ h).symm
  rw [h1, charArtinConductor_inducedFun, ← artinConductor_eq_charArtinConductor, hm,
    character_charRep, map_one, Units.val_one]
  push_cast
  ring

end Monomial

end GroundTheory.LocalField
end
end
