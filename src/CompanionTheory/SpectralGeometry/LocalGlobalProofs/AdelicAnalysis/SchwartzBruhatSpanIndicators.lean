import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem compact_open_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {L₁ L₂ : AddSubgroup V} (h₁ : IsCompact (L₁ : Set V)) (o₁ : IsOpen (L₁ : Set V))
    (h₂ : IsCompact (L₂ : Set V)) :
    IsCompact ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) ∧ IsOpen ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left o₁⟩
  rw [AddSubgroup.add_normal]
  exact h₁.add h₂

theorem compact_subgroup_and_level :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  intro V _ _ _ χ μ h
  obtain ⟨hG, hT, -, -, -, -, hnb, hcov, -⟩ := h
  haveI := hG
  haveI := hT
  have cover : ∀ K : Set V, IsCompact K →
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L := by
    intro K hK
    refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧
      IsOpen (L : Set V) ∧ s ⊆ L) ?_ ?_ ?_ ?_
    · obtain ⟨L, c, o, -⟩ := hcov 0
      exact ⟨L, c, o, Set.empty_subset _⟩
    · rintro s t hst ⟨L, c, o, hL⟩
      exact ⟨L, c, o, hst.trans hL⟩
    · rintro s t ⟨L₁, c₁, o₁, h₁⟩ ⟨L₂, c₂, o₂, h₂⟩
      obtain ⟨c, o⟩ := compact_open_sup c₁ o₁ c₂
      refine ⟨L₁ ⊔ L₂, c, o, Set.union_subset ?_ ?_⟩
      · exact h₁.trans (SetLike.coe_subset_coe.2 le_sup_left)
      · exact h₂.trans (SetLike.coe_subset_coe.2 le_sup_right)
    · intro x _
      obtain ⟨L, c, o, hx⟩ := hcov x
      exact ⟨L, mem_nhdsWithin_of_mem_nhds (o.mem_nhds hx), L, c, o, subset_rfl⟩
  refine ⟨cover, ?_⟩
  rintro φ ⟨hlc, hcs⟩
  obtain ⟨L, c, o, hL⟩ := cover _ hcs
  have hzero : ∀ x, x ∉ L → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hL hm))
  have hg : IsLocallyConstant (fun p : V × V => (φ (p.1 + p.2), φ p.1)) :=
    (hlc.comp_continuous continuous_add).prodMk (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : V × V | φ (p.1 + p.2) = φ p.1} := hg {q : ℂ × ℂ | q.1 = q.2}
  have hsub : (L : Set V) ×ˢ ({0} : Set V) ⊆ {p : V × V | φ (p.1 + p.2) = φ p.1} := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    have hy' : y = 0 := hy
    simp [hy']
  obtain ⟨u, v, -, ov, hu, hv, huv⟩ := generalized_tube_lemma c isCompact_singleton hW hsub
  obtain ⟨L₀, c₀, o₀, h₀⟩ := hnb v (ov.mem_nhds (hv rfl))
  refine ⟨L, L₀ ⊓ L, c, o, ?_, ?_, inf_le_right, hzero, ?_⟩
  · have := c₀.inter_right c.isClosed
    simpa using this
  · simpa using o₀.inter o
  · intro x l hl
    have hl₀ : l ∈ L₀ := hl.1
    have hlL : l ∈ L := hl.2
    by_cases hx : x ∈ L
    · exact huv (Set.mk_mem_prod (hu hx) (h₀ hl₀))
    · rw [hzero x hx, hzero _ (fun hm => hx ?_)]
      simpa using L.sub_mem hm hlL

end GlobalTheory.CompanionTheory.SW.Core
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Span

theorem sb_eq_sum_coset_indicators :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ)
      (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V,
      IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) →
      ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x := by
  intro V _ _ _ χ μ h φ hφ L' hL' hinv
  classical
  haveI : IsTopologicalAddGroup V := h.1
  obtain ⟨t, ht⟩ := hφ.2.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L'})
    (fun a => hL'.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L'.zero_mem]⟩)
  let T : Finset (V ⧸ L') := t.image (QuotientAddGroup.mk : V → V ⧸ L')
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L', x - q.out ∈ L' ↔ q = (x : V ⧸ L') := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L').out) = φ x := by
    have hm : x - ((x : V ⧸ L')).out ∈ L' := (key _).2 rfl
    have := hinv ((x : V ⧸ L')).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L', φ q.out * Set.indicator {y | y - q.out ∈ L'} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L') then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L')
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L')).out ∈ L'} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L'} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa

end GlobalTheory.CompanionTheory.SW.Span
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem sb_eq_sum_rational_coset_indicators :
    ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type)
      [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)),
      NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) →
      ∀ φ : (ι → A F) → ℂ, SB φ →
        ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
          φ = ∑ a ∈ s, c a • indC N a := by
  intro F _ _ _ _ ι _ _ χ μ h hopen φ hφ
  classical
  obtain ⟨-, -, -, -, -, hdense, -, hU, -, hNopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hlev⟩ := GlobalTheory.CompanionTheory.SW.Core.compact_subgroup_and_level (ι → A F) χ μ h
  obtain ⟨L, L', -, -, -, oL', -, -, hinv⟩ := hlev φ hφ

  have h0 : (L' : Set (ι → A F)) ∈ 𝓝 (0 : ι → A F) := oL'.mem_nhds L'.zero_mem
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t, ht, hsub⟩ := h0
  have hU0 : (⋂ i, t i) ∈ 𝓝 (0 : A F) := Filter.iInter_mem.2 ht
  obtain ⟨N, hN, hNU⟩ := hU _ hU0
  have hle : latN F ι N ≤ L' := by
    intro x hx
    apply hsub
    intro i _
    obtain ⟨y, hy, e⟩ := hx i
    rw [e]
    exact Set.mem_iInter.1 (hNU y hy) i

  have happ : ∀ (a : ι → A F) (i : ι), ∃ b : F,
      ∃ y ∈ Oh F, a i - algebraMap F (A F) b = (N : A F) * y := by
    intro a i
    have ho : IsOpen {b : A F | ∃ y ∈ Oh F, a i - b = (N : A F) * y} :=
      (hNopen N hN).preimage (continuous_const.sub continuous_id)
    have hne : {b : A F | ∃ y ∈ Oh F, a i - b = (N : A F) * y}.Nonempty :=
      ⟨a i, 0, fun _ => zero_mem _, by simp⟩
    obtain ⟨b, hb⟩ := hdense.exists_mem_open ho hne
    exact ⟨b, hb⟩
  choose r hr using happ
  have hrl : ∀ a : ι → A F, a - toA (r a) ∈ latN F ι N := fun a i => hr a i
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.SW.Span.sb_eq_sum_coset_indicators (ι → A F) χ μ h φ hφ (latN F ι N)
    (hopen N hN) (fun x l hl => hinv x l (hle hl))
  have hind : ∀ (a x : ι → A F),
      Set.indicator {y | y - a ∈ latN F ι N} (fun _ => (1 : ℂ)) x = indC N (r a) x := by
    intro a x
    have hset : {y | y - a ∈ latN F ι N} = {y | y - toA (r a) ∈ latN F ι N} := by
      ext y
      have e : y - toA (r a) = (y - a) + (a - toA (r a)) := by abel
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact (AddSubgroup.add_mem_cancel_right _ (hrl a)).symm
    rw [hset]
    rfl
  refine ⟨N, hN, s.image r, fun b => ∑ a ∈ s with r a = b, φ a, ?_⟩
  funext x
  rw [hs x, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, hind, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image r) (g := r)
    (fun a ha => Finset.mem_image_of_mem r ha)]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

end GlobalTheory.CompanionTheory.SW.ThW
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_span_indicators : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type) [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)), NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ), φ = ∑ a ∈ s, c a • indC N a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators
end
