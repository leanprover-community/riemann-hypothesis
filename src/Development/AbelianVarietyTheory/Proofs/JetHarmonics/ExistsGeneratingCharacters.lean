import Mathlib

section
namespace GlobalTheory.ExtensionCharacter

theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun u : Fˣ => u ^ n) := by
  intro x
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x : F)) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact x.ne_zero hz.symm
  have hu : (Units.mk0 z hz0) ^ n.natAbs = x := by
    ext; simp [hz]
  rcases Int.natAbs_eq n with h | h
  · refine ⟨Units.mk0 z hz0, ?_⟩
    simp only
    rw [h, zpow_natCast, hu]
  · refine ⟨(Units.mk0 z hz0)⁻¹, ?_⟩
    simp only
    rw [h, inv_zpow', neg_neg, zpow_natCast, hu]

noncomputable instance divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa [ofMul_zpow] using congrArg Additive.ofMul hy⟩

theorem exists_extension_character : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M]
    [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) →
    ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x := by
  intro H M F _ _ _ _ Φ hΦ χ
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

end GlobalTheory.ExtensionCharacter
end

section
namespace GlobalTheory.PrimaryCharacter

theorem exists_extend_of_injective {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | (apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character ..)

theorem exists_factor_of_ker_le {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := exists_extend_of_injective (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩

end GlobalTheory.PrimaryCharacter
end
