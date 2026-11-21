import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel

/-! An affine averaging argument for finite-index descent of a linear cocycle. -/
namespace UpperTheory

theorem finiteIndexCoboundary {k G W : Type} [Field k] [CharZero k] [Group G]
    [AddCommGroup W] [Module k W] (a : G → W →ₗ[k] W)
    (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (cocycle : ∀ g h, f (g * h) = f g + a g (f h))
    (H : Subgroup G) [H.FiniteIndex] (x : W)
    (fixed : ∀ h ∈ H, f h = a h x - x) :
    ∃ y, ∀ g, f g = a g y - y := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let orbit (g : G) := a g x - f g
  have const (g h : G) (hh : h ∈ H) : orbit (g * h) = orbit g := by
    simp only [orbit, hmul, cocycle, fixed h hh, map_sub]
    abel
  let point : G ⧸ H → W := Quotient.lift orbit (by
    intro g u hgu
    simpa using (const g (g⁻¹ * u) (QuotientGroup.leftRel_apply.mp hgu)).symm)
  have shift (g : G) (q : G ⧸ H) : point (g • q) = a g (point q) - f g := by
    induction q using QuotientGroup.induction_on with
    | H u =>
      change a (g * u) x - f (g * u) = a g (a u x - f u) - f g
      rw [hmul, cocycle, map_sub]
      abel
  let S : W := ∑ q, point q
  let n : k := Fintype.card (G ⧸ H)
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨n⁻¹ • S, fun g => ?_⟩
  have sum : S = a g S - n • f g := by
    calc S = ∑ q, point (g • q) := (Equiv.sum_comp (MulAction.toPerm g) point).symm
         _ = _ := by simp only [shift, Finset.sum_sub_distrib, Finset.sum_const,
                                 Finset.card_univ, ← map_sum, S, n, Nat.cast_smul_eq_nsmul]
  have delta : a g S - S = n • f g := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp sum.symm)
  rw [map_smul, ← smul_sub, delta, inv_smul_smul₀ hn]

end UpperTheory
