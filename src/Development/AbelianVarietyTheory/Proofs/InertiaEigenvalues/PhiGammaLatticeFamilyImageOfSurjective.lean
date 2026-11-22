module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

@[expose] public section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Img

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
  [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem map_sh (f : V →ₗ[k⸨X⸩] W) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).map (f.restrictScalars k⟦X⟧) = sh a (N.map (f.restrictScalars k⟦X⟧)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hx
    exact ⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩

theorem isLat_map (f : V →ₗ[k⸨X⸩] W) (hf : Function.Surjective f) {N : Submodule k⟦X⟧ V} (h : IsLat N) :
    IsLat (N.map (f.restrictScalars k⟦X⟧)) := by
  refine ⟨h.1.map _, ?_⟩
  have : ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V) := rfl
  rw [this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]

theorem map_pull [Module k V] [Module k W] (f g : V →ₗ[k⸨X⸩] W) (φ : V →ₗ[k] V) (φ' : W →ₗ[k] W)
    (h : ∀ x, f (φ x) = φ' (g x)) (N : Submodule k⟦X⟧ V) :
    (pull φ N).map (f.restrictScalars k⟦X⟧) = pull φ' (N.map (g.restrictScalars k⟦X⟧)) := by
  rw [pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => h x

end

end GlobalTheory.PhiGam.Img
