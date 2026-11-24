module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.SupIndep
import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

universe u_1

namespace Bl.general_b_fact_second_ter_form

theorem goal1 {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type u_1}
    (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ (i : ι) (v : V), v ∈ p i ↔ ∀ w, C w v = χ i w • v) :
    iSupIndep p := by
  classical
  have aux (t : Finset ι) : ∀ i ∉ t, Disjoint (p i) (t.sup p) := by
    induction t using Finset.strongInduction with
    | H t ih =>
      intro i hi
      rcases t.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
      · simp
      obtain ⟨w, hw⟩ : ∃ w, χ i w ≠ χ j w := by
        by_contra! h
        exact hi (hχ (funext h) ▸ hj)
      have hmem {k v} (hv : v ∈ p k) : C w v = χ k w • v := (hp k v).1 hv w
      have hle : t.sup p ≤ Submodule.comap (C w - χ j w • LinearMap.id) ((t.erase j).sup p) :=
        Finset.sup_le fun k hk x hx => by
          rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
            hmem hx, ← sub_smul]
          by_cases hkj : k = j
          · simp [hkj]
          · exact Finset.le_sup (f := p) (Finset.mem_erase.2 ⟨hkj, hk⟩) (Submodule.smul_mem _ _ hx)
      rw [Submodule.disjoint_def]
      intro v hvi hvt
      have h3 : (χ i w - χ j w) • v ∈ (t.erase j).sup p := by
        simpa [hmem hvi, sub_smul] using hle hvt
      have h4 := ih (t.erase j) (Finset.erase_ssubset hj) i fun h => hi (Finset.mem_of_mem_erase h)
      have h5 : (χ i w - χ j w) • v = 0 :=
        Submodule.disjoint_def.1 h4 _ (Submodule.smul_mem _ _ hvi) h3
      rw [← inv_smul_smul₀ (sub_ne_zero.2 hw) v, h5, smul_zero]
  rw [iSupIndep_iff_supIndep]
  intro s
  rw [Finset.supIndep_iff_disjoint_erase]
  exact fun i _ => aux (s.erase i) i (Finset.notMem_erase i s)

end Bl.general_b_fact_second_ter_form
