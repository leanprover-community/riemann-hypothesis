import Lib.Base

/-!
# Translation-invariant inner products on a finite group

An inner product matrix whose entries depend only on the group difference
has the same row sum in every row.
-/

open InnerProductSpace Finset Complex
open scoped BigOperators

namespace New

variable {G H : Type*} [Group G] [Fintype G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {u : G → H}

/-- If the inner product of two families of vectors indexed by a finite group `G` has the form
`⟪u a, v b⟫ = f (a⁻¹ * b)`, then `⟪∑ a, u a, ∑ a, v a⟫ = |G| · ∑ s, f s`. -/
lemma inner_sum_sum_eq_card_mul {v : G → H} (f : G → ℂ)
    (h : ∀ a b : G, ⟪u a, v b⟫_ℂ = f (a⁻¹ * b)) :
    ⟪∑ a : G, u a, ∑ a : G, v a⟫_ℂ = Fintype.card G * ∑ s : G, f s := by
  -- For each `a` the map `b ↦ a⁻¹ * b` is a bijection of `G`.
  have h_row (a : G) : ⟪u a, ∑ b : G, v b⟫_ℂ = ∑ s : G, f s := by
    simpa [inner_sum, h] using (Group.mulLeft_bijective a⁻¹).sum_comp f
  rw [sum_inner]
  simp [h_row]

end New
