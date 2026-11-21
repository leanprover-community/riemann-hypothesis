import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionTheta

section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_mem_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.AdelicCoordSB.finprod_mem_SB | exact GlobalTheory.AdelicCoordSB.finprod_mem_SB | (intros; apply GlobalTheory.AdelicCoordSB.finprod_mem_SB <;> assumption)
end

section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroups_integers : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  first | exact @GlobalTheory.SBBox.exists_box_invariant | exact GlobalTheory.SBBox.exists_box_invariant | (intros; apply GlobalTheory.SBBox.exists_box_invariant <;> assumption)
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalBoxIndicator

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {S : Set X} (hcl : IsClopen S) (hco : IsCompact S) :
    Set.indicator S (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  classical
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

theorem indicator_box_translate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F _ _ κ _ B hBo hBO hBcof r
  refine ⟨fun v => ?_, ?_⟩
  · set c : κ → v.adicCompletion F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) with hc
    have hS : {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        = (Homeomorph.subRight c) ⁻¹' (Set.univ.pi fun _ => (B v : Set (v.adicCompletion F))) := by
      ext x
      simp [Set.mem_pi, hc]
    have hBc : IsCompact (B v : Set (v.adicCompletion F)) :=
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).of_isClosed_subset
        (AddSubgroup.isClosed_of_isOpen (B v) (hBo v)) (hBO v)
    have hT : IsClopen (Set.univ.pi fun _ : κ => (B v : Set (v.adicCompletion F))) :=
      ⟨isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (B v) (hBo v),
        isOpen_set_pi Set.finite_univ fun _ _ => hBo v⟩
    rw [hS]
    exact indicator_mem_SB (hT.preimage (Homeomorph.subRight c).continuous)
      ((Homeomorph.subRight c).isCompact_preimage.2 (isCompact_univ_pi fun _ => hBc))
  · have hr : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => (r i).2
    filter_upwards [hr, hBcof] with v hv hBv
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hBv, SetLike.mem_coe]
    constructor
    · intro h
      have := (v.adicCompletionIntegers F).add_mem _ _ h (hv i)
      simpa using this
    · intro h
      exact (v.adicCompletionIntegers F).sub_mem h (hv i)

end GlobalTheory.LocalBoxIndicator

end
end

section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_open_subgroups_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @GlobalTheory.LocalBoxIndicator.indicator_box_translate | exact GlobalTheory.LocalBoxIndicator.indicator_box_translate | (intros; apply GlobalTheory.LocalBoxIndicator.indicator_box_translate <;> assumption)
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BoxCosetSum

variable {F : Type} [Field F] [NumberField F]

theorem continuous_evalV' (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem eventually_evalV_mem_integers (x : FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ v in Filter.cofinite, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ v.adicCompletionIntegers F := x.2

theorem isOpen_box (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
  have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 hBf
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F |
      ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have e : {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} =
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} ∩
        ⋂ v ∈ hT.toFinset, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) ⁻¹' (B v : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.Finite.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun v => hBO v (h v), fun v _ => h v⟩
    · rintro ⟨h1, h2⟩ v
      by_cases hv : (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F
      · have : x v ∈ (B v : Set (v.adicCompletion F)) := by rw [hv]; exact h1 v
        exact this
      · exact h2 v hv
  rw [e]
  exact hO.inter (isOpen_biInter_finset fun v _ => (hBo v).preimage (continuous_evalV' v))

def boxSub (κ : Type) (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {u | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v}
  add_mem' := by
    intro a b ha hb i v
    simp only [Pi.add_apply, map_add]
    exact (B v).add_mem (ha i v) (hb i v)
  zero_mem' := by
    intro i v
    simp only [Pi.zero_apply, map_zero]
    exact (B v).zero_mem
  neg_mem' := by
    intro a ha i v
    simp only [Pi.neg_apply, map_neg]
    exact (B v).neg_mem (ha i v)

theorem mem_boxSub {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := Iff.rfl

theorem isOpen_boxSub (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have e : (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun u : κ → FiniteAdeleRing (𝓞 F) F => u i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
    ext u
    simp only [SetLike.mem_coe, mem_boxSub, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_box B hBo hBO hBf).preimage (continuous_apply i)

theorem finprod_indicator_eq (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by
  have key : ∀ v, ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}) ↔
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ B v := by
    intro v
    simp only [Set.mem_setOf_eq, Pi.sub_apply, map_sub]
  by_cases h : y - r ∈ boxSub κ B
  · rw [Set.indicator_of_mem (show y ∈ {z | z - r ∈ boxSub κ B} from h)]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [Set.indicator_of_mem ((key v).2 fun i => h i v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show y ∉ {z | z - r ∈ boxSub κ B} from h)]
    rw [mem_boxSub] at h
    push_neg at h
    obtain ⟨i0, v0, hv0⟩ := h
    apply finprod_eq_zero _ v0
    · rw [Set.indicator_of_notMem]
      rw [key v0]
      exact fun H => hv0 (H i0)
    · have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
        Filter.eventually_cofinite.1 hBf
      have hI : (⋃ i, {v | ¬ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ v.adicCompletionIntegers F}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (eventually_evalV_mem_integers ((y - r) i))
      refine (hT.union hI).subset ?_
      intro v hv
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
      apply hv
      dsimp only
      rw [Set.indicator_of_mem, Pi.one_apply]
      rw [key v]
      intro i
      have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := hc.2 i
      rw [← hc.1] at h2
      exact h2

theorem eq_sum_finprod_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ B hBo hBO hBf g hg hinv
  classical
  set U := boxSub κ B with hU
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_boxSub κ B hBo hBO hBf
  have hK : IsCompact (tsupport g) := hg
  have hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, finprod_indicator_eq κ B hBO hBf]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · rw [Set.indicator_of_mem (show x ∈ {z | z - r0 ∈ boxSub κ B} from hxr0), mul_one]
      have := hinv r0 (x - r0) hxr0
      rwa [add_sub_cancel] at this
    · intro r hr hne
      have hm : x ∉ {z | z - r ∈ boxSub κ B} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hm : x ∉ {z | z - r ∈ boxSub κ B} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.BoxCosetSum

end
end

section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_open_subgroups_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator | exact GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator | (intros; apply GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKEvAdm

theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl g hg
  classical
  obtain ⟨ei, ev, -, hvac, hpure⟩ := hev.loc
  obtain ⟨Bx, hBo, hBs, hBe, hinv⟩ := GlobalTheory.T.exists_open_subgroups_integers F _ g hg
  obtain ⟨R, hR⟩ := GlobalTheory.T.scaling_open_subgroups_finite F _ Bx hBo hBs hBe g hg.2 hinv
  let φ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n × Fin d → v.adicCompletion F) → ℂ :=
    fun r v => Set.indicator {x : Fin n × Fin d → v.adicCompletion F | ∀ i, x i - evalV F v (r i) ∈ Bx v} 1
  have hφSB : ∀ r v, φ r v ∈ SB _ := fun r => (GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).1
  have hφvac : ∀ r, ∀ᶠ v in cofinite, φ r v = M.vac v := fun r => by
    filter_upwards [(GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).2, hM.std] with v h1 h2
    exact h1.trans h2.symm
  let ψ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n₁ × Fin d₁ → v.adicCompletion F) → ℂ :=
    fun r v => ev v (φ r v)
  have hψSB : ∀ r v, ψ r v ∈ SB _ := fun r v => by
    rw [← (hvac v).2]; exact Submodule.mem_map_of_mem (hφSB r v)
  have hψint : ∀ r, ∀ᶠ v in cofinite,
      ψ r v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun r => by
    filter_upwards [hφvac r, hM₁.std] with v h1 h2
    show ev v (φ r v) = _
    rw [h1, (hvac v).1, h2]
  let g' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun r y => ∏ᶠ v, ψ r v fun i => evalV F v (y i)
  have hg'SB : ∀ r, g' r ∈ SB _ := fun r => GlobalTheory.T.restricted_product_mem_schwartz F _ (ψ r) (hψSB r) (hψint r)
  have hT : ∀ r, ∃ T : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f (g' r)) = T f := fun r => hl (g' r) (hg'SB r)
  choose T hT using hT
  have key : ∀ f : SInf F (Fin n × Fin d), pureA F f g = ∑ r ∈ R, g r • pure f (φ r) := by
    intro f
    funext x
    rw [Finset.sum_apply]
    conv_lhs => rw [hR]
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_left_comm]
    rfl
  have key2 : ∀ (f : SInf F (Fin n₁ × Fin d₁)) r, pure f (ψ r) = pureA F f (g' r) := fun f r => rfl
  refine ⟨∑ r ∈ R, g r • (T r).comp ei, fun f => ?_⟩
  have hL : l (e (pureA F (⇑f) g)) = ∑ r ∈ R, g r * T r (ei f) := by
    rw [key, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, map_smul, hpure f (φ r) (hφSB r) (hφvac r), key2, hT, smul_eq_mul]
  rw [LinearMap.comp_apply, hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rfl

end GlobalTheory.ThKEvAdm

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_composition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ThKEvAdm.comp_mem_adm | exact GlobalTheory.ThKEvAdm.comp_mem_adm | (intros; apply GlobalTheory.ThKEvAdm.comp_mem_adm <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  first | exact @GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero | exact GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero | (intros; apply GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem rho_zero_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin n) (Fin d₁) (AE F E))
    (hz : (M₁.co.e z).1 = 0) (Ψ : Fn F n d₁) : M₁.co.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d₁ → AF F) (Ψ : Fn F n d₁) :
    M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

end GlobalTheory.MixUniq

namespace GlobalTheory.MixUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (ι' : Matrix (Fin d) (Fin d₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι')ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n × Fin d₁ → AF F) :
    S Φ y = ev0 (Fin n × Fin d₁) (S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H' : Plane E d d₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr ψ w φ = M.co.rho ψ u (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 (Fin n × Fin d₁) ∘ₗ S) (schr ψ w Φ) = (ev0 (Fin n × Fin d₁) ∘ₗ S) Φ := by
  obtain ⟨u, hu, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI u hu _ h1, hS z Φ hΦ, rho_zero_first M₁ ψ z hz]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ T : Fn F n d →ₗ[ℂ] Fn F n d₁, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d₁)) →
        (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (T Φ)) →
        (∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ u Φ) = T Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁), l ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), T Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he T hTm hTh hTi hTa
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
  have hadmT : ev0 (Fin n × Fin d₁) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d) := hTa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  have hadmE : ev0 (Fin n × Fin d₁) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) :=
    GlobalTheory.T.eigen_intertwiner_composition F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hψ (Fin n × Fin d) L hiso hrk _ hadmT _ hadmE
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' T hTh hTi _ (hL t w hw) Φ hΦ)
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' e he.Heisenberg₂ he.inv _ (hL t w hw) Φ hΦ)
    ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ₀ hΦ₀, by
      rw [LinearMap.comp_apply, ← apply_eq_evaluation_zero M M₁ B.ψ H'.ι e he.Heisenberg₂ Φ₀ hΦ₀ y]; exact hy⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [apply_eq_evaluation_zero M M₁ B.ψ H'.ι T hTh Φ hΦ y, Pi.smul_apply, apply_eq_evaluation_zero M M₁ B.ψ H'.ι e he.Heisenberg₂ Φ hΦ y, smul_eq_mul]
  exact hc _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ)

end GlobalTheory.MixUniq
end
end
