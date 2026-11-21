import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterQuotientOfInjectiveIntertwining

section
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_irreducible_subrepresentation {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

theorem exists_irrChar_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ G _ a ha h0
  obtain ⟨n, ρ, hρ⟩ := ha
  have hn : Nontrivial (Fin n → K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply h0
    funext g
    have : ρ g = 0 := Subsingleton.elim _ _
    simp [hρ, Representation.character, this]
  obtain ⟨S, hS⟩ := exists_irreducible_subrepresentation ρ
  let f : Representation.IntertwiningMap S.toRepresentation ρ :=
    ⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩
  obtain ⟨c, hc, hcg⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G _ _ ρ S.toRepresentation f
    S.toSubmodule.injective_subtype
  refine ⟨_, c, (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ S.toRepresentation).2 hS, hc, ?_⟩
  funext g
  rw [hρ, hcg]
  rfl

end GlobalTheory.BI
end

open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  atlas_forward_decl GlobalTheory.BI.exists_irrChar_add
end

section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.isChar_induction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G]
      [Finite G] (Q : (G → L) → Prop), Q 0 →
      (∀ φ c : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ → _root_.GlobalTheory.BI.IsChar K L c →
        Q c → Q (φ + c)) → ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → Q a := by
  intro K L _ _ _ _ _ G _ _ Q h0 hstep
  have hchar : ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → ∃ n : ℕ, a 1 = n := by
    intro a ha
    unfold _root_.GlobalTheory.BI.IsChar at ha
    obtain ⟨n, ρ, hρ⟩ := ha
    exact ⟨n, by rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
  have hirr : ∀ φ : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ →
      ∃ m : ℕ, 0 < m ∧ φ 1 = m := by
    intro φ hφ
    unfold _root_.GlobalTheory.BI.IsIrrChar at hφ
    obtain ⟨m, ρ, hρirr, hρ⟩ := hφ
    refine ⟨m, Nat.pos_of_ne_zero fun hm => ?_, by
      rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
    subst hm
    have hs : IsSimpleOrder (Subrepresentation ρ) := hρirr
    obtain ⟨x, y, hxy⟩ := hs.toNontrivial.exists_pair_ne
    apply hxy
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => y.toSubmodule.zero_mem, fun _ => x.toSubmodule.zero_mem⟩
  have key : ∀ n : ℕ, ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a 1 = n → Q a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha ha1
      by_cases hz : a = 0
      · rw [hz]; exact h0
      obtain ⟨φ, c, hφ, hc, rfl⟩ := _root_.GlobalTheory.BI.exists_irrChar_add K L G a ha hz
      obtain ⟨m, hm, hφ1⟩ := hirr φ hφ
      obtain ⟨k, hk1⟩ := hchar c hc
      have hn : n = m + k := by
        have hsum : ((m + k : ℕ) : L) = n := by
          rw [Nat.cast_add, ← hφ1, ← hk1]
          exact ha1
        exact_mod_cast hsum.symm
      exact hstep φ c hφ hc (ih k (by omega) c hc hk1)
  intro a ha
  obtain ⟨n, hn⟩ := hchar a ha
  exact key n a ha hn

end GlobalTheory.BI
end
