import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory

theorem polMod_mul_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  intro E _ _ _ L ⟨N, hN, hL⟩ hu
  have hLfg : L.FG := by
    apply Submodule.FG.of_restrictScalars ℤ
    let f : E →ₗ[ℤ] E := LinearMap.mulLeft ℤ (N : E)
    have hf : Function.Injective f := mul_right_injective₀ (Nat.cast_ne_zero.2 hN.ne')
    let g : 𝓞 E →ₗ[ℤ] E := (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
    have hg : (LinearMap.range g).FG := by
      rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
    refine Submodule.fg_of_fg_map_injective f hf (hg.of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(N : E) * x, hL x hx⟩, rfl⟩
  have hMfg : (polMod L).FG := Submodule.fg_of_isUnit hu
  have hP : (polMod L * L).FG := hMfg.mul hLfg
  exact (Submodule.fg_iff_addSubgroup_fg ((polMod L * L).restrictScalars ℤ)).1 (hP.restrictScalars)

end GlobalTheory
end

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_lattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  atlas_forward_decl GlobalTheory.polMod_mul_fg
