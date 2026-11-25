module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol

@[expose] public section

open MeasureTheory Set TopologicalSpace

namespace GlobalTheory

theorem discreteSubgroup_countable_and_exists_strict_fundamentalDomain : ∀ {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ],
    Countable Γ ∧ ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ D := by
  intro G _ _ _ _ _ _ Γ _
  classical
  refine ⟨TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ?_⟩

  obtain ⟨U, hU, -, hUone⟩ :=
    IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty Γ (IsDiscrete.mk inferInstance)
  let P : Set G → Prop := fun W => ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ Γ → x = y
  have hPU : P U := by
    intro x hx y hy hxy
    have hne : ((fun z => (x * y⁻¹) * z) '' U ∩ U).Nonempty := ⟨x, ⟨y, hy, by simp⟩, hx⟩
    exact mul_inv_eq_one.1 (by simpa using hUone _ hxy hne)
  obtain ⟨V, hVU, hVo, hV1⟩ := mem_nhds_iff.1 hU
  have hPV : P V := fun x hx y hy hxy => hPU x (hVU hx) y (hVU hy) hxy
  have hPmul : ∀ g : G, P ((fun x => x * g) '' V) := by
    rintro g x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hxy
    rw [show a * g * (b * g)⁻¹ = a * b⁻¹ by group] at hxy
    rw [hPV a ha b hb hxy]
  let S : Set (Set G) := {W | W ∈ countableBasis G ∧ P W}
  have hcover : ∀ g : G, ∃ W ∈ S, g ∈ W := by
    intro g
    have hg : g ∈ (fun x => x * g) '' V := ⟨1, hV1, by simp⟩
    have ho : IsOpen ((fun x => x * g) '' V) :=
      (Homeomorph.isOpen_image (Homeomorph.mulRight g)).2 hVo
    obtain ⟨W, hWb, hgW, hWV⟩ := (isBasis_countableBasis G).exists_subset_of_mem_open hg ho
    exact ⟨W, ⟨hWb, fun x hx y hy hxy => hPmul g x (hWV hx) y (hWV hy) hxy⟩, hgW⟩
  have hSc : S.Countable := (countable_countableBasis G).mono fun W hW => hW.1
  obtain ⟨f, hf⟩ := hSc.exists_eq_range (by obtain ⟨W, hW, -⟩ := hcover 1; exact ⟨W, hW⟩)
  have hfS : ∀ n, f n ∈ S := fun n => hf ▸ mem_range_self n

  let Sat : ℕ → Set G := fun m => {x | ∃ γ : Γ, (γ : G) * x ∈ f m}
  have hSat : ∀ m, IsOpen (Sat m) := by
    intro m
    have : Sat m = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' f m := by
      ext x; simp [Sat]
    rw [this]
    exact isOpen_iUnion fun γ => ((isBasis_countableBasis G).isOpen (hfS m).1).preimage
      (continuous_const_mul _)
  let D : Set G := ⋃ n, (f n ∩ ⋂ m ∈ Finset.range n, (Sat m)ᶜ)
  have hmemD : ∀ x : G, x ∈ D ↔ ∃ n, x ∈ f n ∧ ∀ m < n, x ∉ Sat m := by
    intro x
    simp [D, mem_iUnion, mem_iInter, Finset.mem_range]
  refine ⟨D, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => ?_
    exact ((isBasis_countableBasis G).isOpen (hfS n).1).measurableSet.inter
      (Finset.measurableSet_biInter _ fun m _ => (hSat m).measurableSet.compl)
  · intro g
    have hex : ∃ n, ∃ γ : Γ, (γ : G) * g ∈ f n := by
      obtain ⟨W, hW, hgW⟩ := hcover g
      rw [hf] at hW
      obtain ⟨n, rfl⟩ := hW
      exact ⟨n, 1, by simpa using hgW⟩
    obtain ⟨γ, hγ⟩ := Nat.find_spec hex
    have hγD : (γ : G) * g ∈ D := by
      rw [hmemD]
      refine ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩
      obtain ⟨δ, hδ⟩ := hS
      exact Nat.find_min hex hm ⟨δ * γ, by simpa [mul_assoc] using hδ⟩
    refine ⟨γ, hγD, ?_⟩
    intro δ hδ
    rw [hmemD] at hδ
    obtain ⟨n, hn, hmin⟩ := hδ
    have hNn : Nat.find hex = n := by
      rw [Nat.find_eq_iff hex]
      refine ⟨⟨δ, hn⟩, fun m hm hpm => ?_⟩
      obtain ⟨ε, hε⟩ := hpm
      exact hmin m hm ⟨ε * δ⁻¹, by simpa [mul_assoc] using hε⟩
    subst n
    have hP := (hfS (Nat.find hex)).2 _ hγ _ hn (by simpa using (γ * δ⁻¹).2)
    exact (Subtype.ext (mul_right_cancel hP)).symm

end GlobalTheory
