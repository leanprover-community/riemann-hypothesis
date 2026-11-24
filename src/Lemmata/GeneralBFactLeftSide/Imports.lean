module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

namespace Bl.general_b_fact_left'''''

theorem goal1 {O A I : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Fintype I] [DecidableEq I] {B : I → Type} [(i : I) → AddCommGroup (B i)]
    [(i : I) → Module O (B i)] (ε : (i : I) → B i →ₗ[O] A) (T : (i : I) → Set (B i)) :
    Submodule.span O {X : A | ∃ F : (i : I) → B i,
      (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
    Submodule.span O {X : A | ∃ F : (i : I) → B i,
      (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
  · have aux : ∀ s : Finset I, ∀ F : (i : I) → B i,
        (∀ i ∈ s, F i ∈ Submodule.span O (T i)) → (∀ i ∉ s, F i ∈ T i) →
        ∏ i, ε i (F i) ∈ Submodule.span O {X : A | ∃ G : (i : I) → B i,
          (∀ i, G i ∈ T i) ∧ X = ∏ i, ε i (G i)} := fun s => by
      induction s using Finset.induction_on with
      | empty =>
        intro F _ h2
        exact Submodule.subset_span ⟨F, fun i => h2 i (Finset.notMem_empty i), rfl⟩
      | insert j s hj ih =>
        intro F h1 h2
        have hprod (x : B j) : ∏ i, ε i (Function.update F j x i) =
            ε j x * ∏ i ∈ Finset.univ \ {j}, ε i (F i) := by
          have h : (fun i => ε i (Function.update F j x i)) =
              Function.update (fun i => ε i (F i)) j (ε j x) :=
            funext fun i => Function.apply_update (fun k => (ε k : B k → A)) F j x i
          rw [h, Finset.prod_update_of_mem (Finset.mem_univ j)]
        have hmem : ∀ x ∈ Submodule.span O (T j),
            ε j x * ∏ i ∈ Finset.univ \ {j}, ε i (F i) ∈
              Submodule.span O {X : A | ∃ G : (i : I) → B i,
                (∀ i, G i ∈ T i) ∧ X = ∏ i, ε i (G i)} := fun x hx => by
          induction hx using Submodule.span_induction with
          | mem y hy =>
            rw [← hprod y]
            refine ih (Function.update F j y) (fun i hi => ?_) (fun i hi => ?_)
            · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
              exact h1 i (Finset.mem_insert_of_mem hi)
            · by_cases hij : i = j
              · subst hij; simpa using hy
              · rw [Function.update_of_ne hij]; exact h2 i (by simp [hij, hi])
          | zero => simp
          | add y z _ _ hy hz =>
            rw [map_add, add_mul]; exact Submodule.add_mem _ hy hz
          | smul r y _ hy =>
            rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ r hy
        simpa only [← hprod (F j), Function.update_eq_self] using
          hmem (F j) (h1 j (Finset.mem_insert_self j s))
    rintro _ ⟨F, hF, rfl⟩
    exact aux Finset.univ F (fun i _ => hF i) (fun i hi => absurd (Finset.mem_univ i) hi)
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun i => Submodule.subset_span (hF i), rfl⟩

end Bl.general_b_fact_left'''''
