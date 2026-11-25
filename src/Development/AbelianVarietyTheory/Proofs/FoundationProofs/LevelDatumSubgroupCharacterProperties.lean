module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

@[expose] public section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.LevGroup

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

alias isNilpotent_of_isUp := _root_.GlobalTheory.BadShare.Basic.isNilpotent_of_isUp

theorem lev_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) :=
  fun _ _ _ L => ⟨_root_.GlobalTheory.BadShare.Basic.mem_one L, fun _ _ => _root_.GlobalTheory.BadShare.Basic.mem_mul L, _root_.GlobalTheory.BadShare.Basic.chi_one L, fun _ _ => _root_.GlobalTheory.BadShare.Basic.chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩

end GlobalTheory.BadShare.LevGroup
