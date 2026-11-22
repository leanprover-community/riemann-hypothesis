module

public import Mathlib

@[expose] public section

open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal

namespace GlobalTheory

section Existence

variable {G X : Type*} [Group G] [MulAction G X]

@[to_additive exists_measurableSet_addOrbitSection_of_discreteOrbits
]
theorem exists_measurableSet_orbitSection_of_discreteOrbits [Countable G] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableConstSMul G X] (hfix : ∀ g : G, MeasurableSet {x : X | g • x = x})
    (hdisc : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, g • x ∈ U → g • x = x) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  classical
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨B, hB⟩ := (hbc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ b := hB ▸ mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  let S : ℕ → Set X := fun n => B n ∩ ⋂ g : G, (((g • ·) ⁻¹' B n)ᶜ ∪ {x | g • x = x})
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (hBo n).measurableSet.inter <| MeasurableSet.iInter fun g =>
      ((measurable_const_smul g) (hBo n).measurableSet).compl.union (hfix g)
  have hSmem : ∀ n x, x ∈ S n ↔ x ∈ B n ∧ ∀ g : G, g • x ∈ B n → g • x = x := fun n x => by
    simp only [S, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, mem_preimage,
      mem_setOf_eq, imp_iff_not_or]
  have hS : ∀ x, ∃ n, x ∈ S n := fun x => by
    obtain ⟨U, hU, h⟩ := hdisc x
    obtain ⟨t, ht, hxt, htU⟩ := hb.mem_nhds_iff.1 hU
    have : t ∈ range B := hB ▸ mem_insert_of_mem _ ht
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, (hSmem n x).2 ⟨hxt, fun g hg => h g (htU hg)⟩⟩
  let T : ℕ → Set X := fun n => ⋃ g : G, (g • ·) ⁻¹' S n
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    MeasurableSet.iUnion fun g => (measurable_const_smul g) (hSm n)
  have hTmem : ∀ n x, x ∈ T n ↔ ∃ g : G, g • x ∈ S n := fun n x => by simp [T]
  refine ⟨⋃ n, S n \ ⋃ m, ⋃ (_ : m < n), T m, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hSm n).diff <|
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hTm m
  · intro x
    have hx : ∃ n, x ∈ T n := by
      obtain ⟨n, hn⟩ := hS x
      exact ⟨n, (hTmem n x).2 ⟨1, by simpa using hn⟩⟩
    obtain ⟨g, hg⟩ := (hTmem _ x).1 (Nat.find_spec hx)
    refine ⟨g, mem_iUnion.2 ⟨Nat.find hx, hg, fun h => ?_⟩⟩
    obtain ⟨m, hm, h⟩ := mem_iUnion₂.1 h
    obtain ⟨k, hk⟩ := (hTmem _ _).1 h
    exact Nat.find_min hx hm ((hTmem _ _).2 ⟨k * g, by rwa [mul_smul]⟩)
  · intro x hx g hg
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hx
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hg
    rcases lt_trichotomy m n with h | rfl | h
    · exact (hn' (mem_iUnion₂.2 ⟨m, h, (hTmem _ _).2 ⟨g, hm⟩⟩)).elim
    · exact ((hSmem _ _).1 hn).2 g ((hSmem _ _).1 hm).1
    · exact (hm' (mem_iUnion₂.2 ⟨n, h, (hTmem _ _).2 ⟨g⁻¹, by rwa [inv_smul_smul]⟩⟩)).elim

end Existence

section Comparison

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

end Comparison

section Quot

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

namespace IsAEOrbitSection

variable {D D' : Set X}

end IsAEOrbitSection

end Quot

section ProperlyDiscontinuous

variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]

variable {X}

end ProperlyDiscontinuous

section DiscreteSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]

@[to_additive countable_of_discrete_addSubgroup
]
theorem countable_of_discrete_subgroup : Countable Γ :=
  TopologicalSpace.separableSpace_iff_countable.1 inferInstance

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
@[to_additive exists_nhds_zero_inter_addSubgroup]
theorem exists_nhds_one_inter_subgroup : ∃ V ∈ 𝓝 (1 : G), ∀ g ∈ Γ, g ∈ V → g = 1 := by
  have h : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := (isOpen_discrete _).mem_nhds rfl
  rw [nhds_induced, mem_comap] at h
  obtain ⟨V, hV, h⟩ := h
  exact ⟨V, hV, fun g hg hgV => congrArg Subtype.val (h (a := ⟨g, hg⟩) hgV)⟩

variable [MeasurableSpace G] [BorelSpace G]

@[to_additive exists_isAddFundamentalDomain_addSubgroup
]
theorem exists_isFundamentalDomain_subgroup :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ D μ := by
  have := countable_of_discrete_subgroup Γ
  have hfree : ∀ (g : Γ) (x : G), g • x = x → g = 1 := fun g x h =>
    Subtype.ext (mul_eq_right.1 h)
  obtain ⟨V, hV, hV1⟩ := exists_nhds_one_inter_subgroup Γ
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Γ) (X := G)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {x : G | g • x = x} = ∅ := eq_empty_of_forall_notMem fun x hx => hg (hfree g x hx)
        simp [this])
    (fun x => by
      refine ⟨(· * x⁻¹) ⁻¹' V, (continuous_mul_const _).continuousAt.preimage_mem_nhds
        (by simpa using hV), fun g hg => ?_⟩
      have h1 : (g : G) ∈ V := by
        have : (g : G) * x * x⁻¹ ∈ V := hg
        simpa using this
      have : g = 1 := Subtype.ext (hV1 g g.2 h1)
      rw [this, one_smul])
  have h : ∀ x, ∃! g : Γ, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by rwa [mul_smul, inv_smul_smul])
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩

end DiscreteSubgroup

end GlobalTheory
