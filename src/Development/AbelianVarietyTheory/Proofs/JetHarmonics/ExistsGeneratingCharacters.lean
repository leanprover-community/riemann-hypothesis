module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionCharacter

@[expose] public section

namespace GlobalTheory.PrimaryCharacter

theorem exists_factor_of_ker_le {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.ExtensionCharacter.exists_extension_character (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩

end GlobalTheory.PrimaryCharacter
