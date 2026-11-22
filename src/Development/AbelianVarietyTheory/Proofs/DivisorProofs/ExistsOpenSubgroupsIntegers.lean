module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SBBox

theorem exists_nhds_zero_add_eq {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {Y : Type}
    [Zero Y] {g : X → Y} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ N ∈ nhds (0 : X), ∀ y, ∀ u ∈ N, g (y + u) = g y := by
  classical
  have hW : ∀ x : X, ∃ W ∈ nhds (0 : X), ∀ a ∈ W, ∀ b ∈ W, g (x + (a + b)) = g x := by
    intro x
    have h1 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ nhds (0 : X) := by
      refine (hg.isOpen_fiber (g x)).preimage (continuous_const.add continuous_id) |>.mem_nhds ?_
      simp
    obtain ⟨W, hW, hWW⟩ := exists_nhds_zero_half h1
    exact ⟨W, hW, fun a ha b hb => hWW a ha b hb⟩
  choose W hW0 hWg using hW
  let V : X → Set X := fun x => W x ∩ Neg.neg ⁻¹' W x
  have hV0 : ∀ x, V x ∈ nhds (0 : X) := fun x => Filter.inter_mem (hW0 x) (neg_mem_nhds_zero X (hW0 x))
  have hcov : tsupport g ⊆ ⋃ x : X, (fun y => y - x) ⁻¹' interior (V x) := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    simp only [Set.mem_preimage, sub_self]
    exact mem_interior_iff_mem_nhds.2 (hV0 x)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun x => (fun y => y - x) ⁻¹' interior (V x))
    (fun x => isOpen_interior.preimage (continuous_id.sub continuous_const)) hcov
  refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV0 x, fun y u hu => ?_⟩
  have hu' : ∀ x ∈ t, u ∈ W x ∧ -u ∈ W x := fun x hx => by
    have := Set.mem_iInter₂.1 hu x hx
    exact ⟨this.1, this.2⟩
  have h0 : ∀ x, (0 : X) ∈ W x := fun x => mem_of_mem_nhds (hW0 x)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hyx' : y - x ∈ W x := (interior_subset hyx : y - x ∈ V x).1
    have e1 : g (y + u) = g x := by
      have := hWg x (y - x) hyx' u (hu' x hx).1
      rwa [show x + (y - x + u) = y + u by abel] at this
    have e2 : g y = g x := by
      have := hWg x (y - x) hyx' 0 (h0 x)
      rwa [show x + (y - x + 0) = y by abel] at this
    rw [e1, e2]
  · by_cases hyu : y + u ∈ tsupport g
    · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyu)
      have hyx' : y + u - x ∈ W x := (interior_subset hyx : y + u - x ∈ V x).1
      have e1 : g y = g x := by
        have := hWg x (y + u - x) hyx' (-u) (hu' x hx).2
        rwa [show x + (y + u - x + -u) = y by abel] at this
      have e2 : g (y + u) = g x := by
        have := hWg x (y + u - x) hyx' 0 (h0 x)
        rwa [show x + (y + u - x + 0) = y + u by abel] at this
      rw [e1, e2]
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.SBBox

namespace GlobalTheory.SBBox

end GlobalTheory.SBBox
