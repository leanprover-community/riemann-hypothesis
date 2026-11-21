import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

section Generic

variable {X : Type}

def cls (r : Setoid X) (q : Quotient r) : Set X := Quotient.mk r ⁻¹' {q}

theorem mem_cls {r : Setoid X} {q : Quotient r} {y : X} :
    y ∈ cls r q ↔ Quotient.mk r y = q := Iff.rfl

variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem support_out_finite (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (f : X → E)
    (hc : HasCompactSupport f) :
    (Function.support (fun q : Quotient r => f q.out)).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (cls r) hr (by
    intro x _; exact Set.mem_iUnion.2 ⟨Quotient.mk r x, rfl⟩)
  refine t.finite_toSet.subset ?_
  intro q hq
  obtain ⟨q', hq', hm⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have hqq : q = q' := (Quotient.out_eq q).symm.trans hm
  exact hqq ▸ hq'

theorem eq_sum_indicator (r : Setoid X) (f : X → E)
    (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (t : Finset (Quotient r)) (ht : Function.support (fun q : Quotient r => f q.out) ⊆ t) :
    f = fun x => ∑ q ∈ t, (cls r q).indicator (fun _ => f q.out) x := by
  classical
  funext x
  have hx : f x = f (Quotient.mk r x).out := hf _ _ (Quotient.out_eq _).symm
  simp only [Set.indicator_apply, mem_cls]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact hx
  · rw [hx]
    by_contra hne
    exact h (ht hne)

theorem integral_eq_finsum (r : Setoid X) (hr : ∀ q, IsOpen (cls r q)) (μ : Measure X)
    (f : X → E) (hf : ∀ x y, Quotient.mk r x = Quotient.mk r y → f x = f y)
    (hc : HasCompactSupport f)
    (hμ : (∀ q, μ (cls r q) < ⊤) ∨ (∀ q, μ (cls r q) = ⊤)) :
    ∫ x, f x ∂μ = ∑ᶠ q : Quotient r, (μ (cls r q)).toReal • f q.out := by
  classical
  have hfin := support_out_finite r hr f hc
  have ht : Function.support (fun q : Quotient r => f q.out) ⊆ (hfin.toFinset : Set _) := by
    simp
  have hsupp : Function.support (fun q : Quotient r => (μ (cls r q)).toReal • f q.out) ⊆
      (hfin.toFinset : Set _) := fun q hq => ht (fun h => hq (by simp [h]))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rcases hμ with hμ | hμ
  · conv_lhs => rw [eq_sum_indicator r f hf hfin.toFinset ht]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ ((hr q).measurableSet)]
      rfl
    · intro q _
      exact (integrable_indicator_iff (hr q).measurableSet).2 (integrableOn_const (hμ q).ne)
  · have h0 : ∀ q, (μ (cls r q)).toReal • f q.out = 0 := fun q => by simp [hμ q]
    simp only [h0, Finset.sum_const_zero]
    by_cases hz : ∀ q : Quotient r, f q.out = 0
    · have : f = 0 := funext fun x => (hf _ _ (Quotient.out_eq _).symm).trans (hz _)
      simp [this]
    · push Not at hz
      obtain ⟨q, hq⟩ := hz
      apply integral_undef
      intro hint
      have hlt := hint.measure_norm_ge_lt_top (ε := ‖f q.out‖) (norm_pos_iff.2 hq)
      have hsub : cls r q ⊆ {x | ‖f q.out‖ ≤ ‖f x‖} := fun x hx => by
        show ‖f q.out‖ ≤ ‖f x‖
        rw [hf x q.out (hx.trans (Quotient.out_eq q).symm)]
      exact absurd (hμ q) ((measure_mono hsub).trans_lt hlt).ne

end Generic

section Left

variable {G : Type} [Group G]


end Left


section Doset

variable {G : Type} [Group G]

def dcMap (K₀ : Subgroup G) (g : G) (k : K₀) : G ⧸ K₀ := ((k : G) * g : G)


theorem dcMap_eq_iff (K₀ : Subgroup G) (g : G) (k k' : K₀) :
    dcMap K₀ g k = dcMap K₀ g k' ↔
      k⁻¹ * k' ∈ (K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  simp only [dcMap, QuotientGroup.eq]
  simp [mul_assoc]


variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_conj_ne_zero (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G))
    (hc : IsCompact (K₀ : Set G)) (g : G) :
    (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ ≠ 0 := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hc
  have hopen : IsOpen (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) :
      Set K₀) := by
    have : (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) : Set K₀) =
        Subtype.val ⁻¹' ((fun x => g⁻¹ * x * g) ⁻¹' (K₀ : Set G)) := by
      ext k
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [this]
    exact (hK.preimage (by fun_prop)).preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Subgroup.index_ne_zero_of_finite


variable [MeasurableSpace G] [BorelSpace G]


end Doset




end Formalism.DoubleCosetMeasures.P
