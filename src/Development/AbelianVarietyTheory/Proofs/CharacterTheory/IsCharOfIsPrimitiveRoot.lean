import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePower

section
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_abByP | exact GlobalTheory.BI.isChar_of_abByP | (intros; apply GlobalTheory.BI.isChar_of_abByP <;> assumption)
end

section
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (χ : G → L), IsChar L L χ → χ ∈ Virt K L G → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_isChar_of_mem_virt | exact GlobalTheory.BI.isChar_of_isChar_of_mem_virt | (intros; apply GlobalTheory.BI.isChar_of_isChar_of_mem_virt <;> assumption)
end

section
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) → ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  first | exact @GlobalTheory.BI.mem_virt_of_forall_abByP | exact GlobalTheory.BI.mem_virt_of_forall_abByP | (intros; apply GlobalTheory.BI.mem_virt_of_forall_abByP <;> assumption)
end

section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_isPrimitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ G _ _ hG χ hχ
  refine GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character K L G χ hχ (GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower K L G (fun H hH ψ hψ => ?_) χ hχ)
  exact GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower K L m ζ hm hζ H (fun h => Subtype.ext (by simpa using hG (h : G))) hH ψ hψ
end GlobalTheory.BI
end
