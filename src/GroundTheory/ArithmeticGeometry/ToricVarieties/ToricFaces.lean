import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.IsFaceOfIffExistsEqExposedFace
import GroundTheory.ArithmeticGeometry.ToricVarieties.Lattice

namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct


variable {N : Type*} [AddCommGroup N]


theorem dualMonoid_anti {σ₁ σ₂ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : σ₁ ≤ σ₂) :
    dualMonoid σ₂ ≤ dualMonoid σ₁ :=
  fun _ hm => mem_dualMonoid.2 fun x hx => mem_dualMonoid.1 hm x (h hx)

variable [Module.Free ℤ N] [Module.Finite ℤ N]



omit [Module.Free ℤ N] [Module.Finite ℤ N] in

theorem dualMonoid_exposedFace {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) {u : Dual ℤ N} (hu : u ∈ dualMonoid σ) :
    dualMonoid (exposedFace σ (toRealDual N u)) = dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [← Finset.coe_image] at hu ⊢
  apply le_antisymm
  · intro m hm
    obtain ⟨p, -, hp⟩ := exists_add_smul_mem_dual (S.image (toRealSpan N))
      (u := toRealDual N u) (w := toRealDual N m) (mem_dualMonoid.1 hu) (mem_dualMonoid.1 hm)
    have hk : p ≤ ((⌈p⌉₊ : ℕ) : ℝ) := Nat.le_ceil p
    rw [AddSubmonoid.mem_sup]
    refine ⟨m + ⌈p⌉₊ • u, mem_dualMonoid.2 fun x hx => ?_, ⌈p⌉₊ • (-u),
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_singleton _)) _,
      by rw [smul_neg, add_neg_cancel_right]⟩
    have := hp _ hk x hx
    rw [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact this
  · refine sup_le (dualMonoid_anti fun x hx => (mem_exposedFace.1 hx).1) ?_
    rw [AddSubmonoid.closure_le, Set.singleton_subset_iff]
    exact mem_dualMonoid.2 fun x hx => by simp [(mem_exposedFace.1 hx).2]

end GroundTheory.Arith.Toric
