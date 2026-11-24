module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

namespace Bl.FirstBlockLemmaK

theorem goal1 :
  ∀ {R : Type} [inst : CommRing.{0} R] {A : Type} [inst_1 : CommRing.{0} A] [inst_2 : Algebra.{0, 0} R A]
  (aug : AlgHom.{0, 0, 0} R A R),
  IsNilpotent.{0} (RingHom.ker.{0, 0, 0} aug) → ∀ (a : A), IsUnit.{0} (DFunLike.coe.{1, 1, 1} aug a) → IsUnit.{0} a := by
  intro R _ A _ _ aug hI a ha
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, hn⟩ := hI
  set c : A := a * algebraMap R A (↑u⁻¹ : R) with hc
  have hker : c - 1 ∈ RingHom.ker aug := by
    rw [RingHom.mem_ker]
    simp only [hc, map_sub, map_mul, AlgHom.commutes, map_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hu]
    simp
  have hnil : IsNilpotent (c - 1) :=
    ⟨n, by simpa [hn] using Ideal.pow_mem_pow hker n⟩
  have hcu : IsUnit c := by
    simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left hcu

end Bl.FirstBlockLemmaK
