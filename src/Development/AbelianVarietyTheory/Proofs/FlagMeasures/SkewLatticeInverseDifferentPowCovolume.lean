import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  intro V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v
  obtain ⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩ := h2 v.2
  obtain ⟨l₁, ⟨hl₁, hl₁D⟩, -⟩ := h1 (v.1 + s)
  have hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ := hl₁
  refine ⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩
  · have e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0) := by simp
    rw [e]; exact Λ.add_mem hs hl₁'
  · refine ⟨?_, ?_⟩
    · show v.1 + (s + l₁) ∈ D₁
      rw [← add_assoc]; exact hl₁D
    · exact hl₂D
  · rintro ⟨m₁, m₂⟩ ⟨hm, hmD⟩
    have hmD1 : v.1 + m₁ ∈ D₁ := hmD.1
    have hmD2 : v.2 + m₂ ∈ D₂ := hmD.2
    have e2 : m₂ = l₂ := (h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩
    subst e2
    have hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ := by
      have := Λ.sub_mem hm hs
      simpa using this
    have e1 : m₁ - s = l₁ := (h1 (v.1 + s)).unique
      ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩
    have : m₁ = s + l₁ := by rw [← e1]; abel
    rw [this]

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  atlas_forward_decl GlobalTheory.prod_fundamentalDomain_of_extension
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem addFundamentalDomains_measure_eq : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  intro V _ _ _ μ _ L _ D D' hD hD' hu hu'
  let G : AddSubgroup V := L.toAddSubgroup
  haveI : Countable G := inferInstanceAs (Countable L)
  have key : ∀ E : Set V, MeasurableSet E → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ E) →
      IsAddFundamentalDomain G E μ := by
    intro E hE hEu
    refine IsAddFundamentalDomain.mk' hE.nullMeasurableSet ?_
    intro x
    obtain ⟨l, ⟨hlL, hlE⟩, huniq⟩ := hEu x
    refine ⟨⟨l, hlL⟩, ?_, ?_⟩
    · show (l : V) + x ∈ E
      rwa [add_comm]
    · rintro ⟨g, hg⟩ hgE
      have hgE' : x + g ∈ E := by
        have : (g : V) + x ∈ E := hgE
        rwa [add_comm]
      exact Subtype.ext (huniq g ⟨hg, hgE'⟩)
  exact (key D hD hu).measure_eq (key D' hD' hu')

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  atlas_forward_decl GlobalTheory.addFundamentalDomains_measure_eq
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem exists_fundamentalDomain_snd_of_two_smul_mem {ι : Type} [Fintype ι]
    (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ] :
    Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ →
    (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) →
    ∃ D : Set (ι → ℝ), MeasurableSet D ∧
      ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  intro hspan h2
  let L₂ : Submodule ℤ (ι → ℝ) := Λ.map (LinearMap.snd ℤ (ι → ℝ) (ι → ℝ))
  have hmem : ∀ b, b ∈ L₂ ↔ ∃ a, (a, b) ∈ Λ := by
    intro b
    simp only [L₂, Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨⟨a, b'⟩, h, rfl⟩; exact ⟨a, h⟩
    · rintro ⟨a, h⟩; exact ⟨(a, b), h, rfl⟩
  have hin : ∀ x : L₂, ((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)) ∈ Λ := by
    intro x
    obtain ⟨a, ha⟩ := (hmem x).1 x.2
    exact h2 a x ha
  haveI : DiscreteTopology L₂ := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : L₂ => (⟨((0 : ι → ℝ), (2 : ℝ) • (x : ι → ℝ)), hin x⟩ : Λ)) ?_ ?_
    · exact Continuous.subtype_mk
        (by fun_prop) _
    · intro x y hxy
      have h := congrArg (fun z : Λ => (z : (ι → ℝ) × (ι → ℝ)).2) hxy
      simp only at h
      exact Subtype.ext (smul_right_injective _ (two_ne_zero) h)
  haveI : IsZLattice ℝ L₂ := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    intro y _
    have hy : ((0 : ι → ℝ), y) ∈ Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := LinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) hy
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨⟨a, b⟩, h, rfl⟩
    exact (hmem b).2 ⟨a, h⟩
  refine ⟨latticeDomain L₂, measurableSet_latticeDomain L₂, fun y => ?_⟩
  obtain ⟨⟨l, hl⟩, h1, h3⟩ := existsUnique_add_mem_latticeDomain L₂ y
  refine ⟨l, ⟨(hmem l).1 hl, h1⟩, ?_⟩
  rintro m ⟨hm, hm'⟩
  exact congrArg Subtype.val (h3 ⟨m, (hmem m).2 hm⟩ hm')

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' : ∀ {ι : Type} [Fintype ι] (Λ : Submodule ℤ ((ι → ℝ) × (ι → ℝ))) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set ((ι → ℝ) × (ι → ℝ))) = ⊤ → (∀ a b, (a, b) ∈ Λ → ((0 : ι → ℝ), (2 : ℝ) • b) ∈ Λ) → ∃ D : Set (ι → ℝ), MeasurableSet D ∧ ∀ y, ∃! l, l ∈ {b : ι → ℝ | ∃ a, (a, b) ∈ Λ} ∧ y + l ∈ D := by
  atlas_forward_decl GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

open NumberField.InfinitePlace

def cxPlaceEquiv (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    {w : InfinitePlace E // IsComplex w} ≃ InfinitePlace E :=
  Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w

def mixedCoords (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    mixedEmbedding.mixedSpace E ≃ₗ[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)) where
  toFun x := (fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).re,
    fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).im)
  invFun y := (fun w => absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)),
    fun w => ⟨y.1 w.1, y.2 w.1⟩)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
    · apply Complex.ext <;> rfl
  right_inv y := rfl

private theorem measurePreserving_mixedSpace_snd (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    MeasurePreserving (Prod.snd : mixedEmbedding.mixedSpace E → ({w : InfinitePlace E // IsComplex w} → ℂ))
      volume volume := by
  have : IsEmpty {w : InfinitePlace E // IsReal w} :=
    ⟨fun w => not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2⟩
  have h : (volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)) = Measure.dirac 0 := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨measurable_snd, ?_⟩
  show Measure.map Prod.snd ((volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)).prod volume) = volume
  rw [h, Measure.map_snd_prod]
  simp

theorem measurePreserving_mixedCoords (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    MeasurePreserving (mixedCoords E) volume volume := by
  have h2 := measurePreserving_piCongrLeft (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (cxPlaceEquiv E)
  have h3 := measurePreserving_pi (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h4 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)
    (fun _ => (volume : Measure ℝ)) (fun _ => (volume : Measure ℝ))
  have key := h4.comp (h3.comp (h2.comp (measurePreserving_mixedSpace_snd E)))
  have e : (⇑(mixedCoords E)) = ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)) ∘
      (fun a i => Complex.measurableEquivRealProd (a i)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cxPlaceEquiv E)) ∘ Prod.snd := by
    funext x
    ext w <;> rfl
  rw [e]
  exact key

theorem mixedCoords_mixedEmbedding (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (x : E) : mixedCoords E (mixedEmbedding E x) = (reV x, imV x) := by
  ext w <;> simp [mixedCoords, reV, imV, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem mixedSpace_reIm_coords : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)),
      MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  intro E _ _ hE
  have := hE
  exact ⟨(mixedCoords E).toContinuousLinearEquiv, by
    simpa using measurePreserving_mixedCoords E, fun x => by
    simpa using mixedCoords_mixedEmbedding E x⟩

end GlobalTheory.SnMass.SkewVol
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)), MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  atlas_forward_decl GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem fractionalIdeal_basis_transport (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W)
    (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W) (he : MeasurePreserving e volume μ)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W),
      (Submodule.span ℤ (Set.range b) : Set W) =
        (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧
      μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm
        (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(discr K : ℝ)|) := by
  set b₀ := mixedEmbedding.fractionalIdealLatticeBasis K J with hb₀
  refine ⟨_, inferInstance, b₀.map e.toLinearEquiv, ?_, ?_⟩
  · let f : mixedEmbedding.mixedSpace K →ₗ[ℤ] W := e.toLinearEquiv.toLinearMap.restrictScalars ℤ
    have hr : Set.range (b₀.map e.toLinearEquiv) = f '' Set.range b₀ := by
      rw [← Set.range_comp]; rfl
    have h0 : (Submodule.span ℤ (Set.range b₀) : Set (mixedEmbedding.mixedSpace K)) =
        mixedEmbedding K '' (J : Set K) := by
      ext x
      exact mixedEmbedding.mem_span_fractionalIdealLatticeBasis K J
    rw [hr, Submodule.span_image, Submodule.map_coe, h0, Set.image_image]
    rfl
  · have hfd : ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv) =
        e '' ZSpan.fundamentalDomain b₀ := (ZSpan.map_fundamentalDomain b₀ e.toLinearEquiv).symm
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : MeasurePreserving E volume μ := he
    have h1 : μ (ZSpan.fundamentalDomain (b₀.map e.toLinearEquiv)) =
        volume (ZSpan.fundamentalDomain b₀) := by
      rw [← hE.measure_preimage_equiv, hfd]
      congr 1
      exact Set.preimage_image_eq _ e.injective
    rw [h1]
    have hfin : volume (ZSpan.fundamentalDomain b₀) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded b₀).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, ← mixedEmbedding.covolume_idealLattice K J,
      ZLattice.covolume_eq_measure_fundamentalDomain _ _
        (mixedEmbedding.fundamentalDomain_idealLattice K J), measureReal_def]

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving : ∀ (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W), MeasurePreserving e volume μ → ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W), (Submodule.span ℤ (Set.range b) : Set W) = (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧ μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.ReCoords

theorem comap_bij (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2) :
    Function.Bijective fun w : InfinitePlace E => w.comap (algebraMap F E) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨InfinitePlace.comap_surjective (k := F) (K := E), ?_⟩
  have h1 := IsTotallyComplex.finrank E
  have h2' := IsTotallyReal.finrank F
  have h3 := Module.finrank_mul_finrank ℚ F E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, IsTotallyReal.nrComplexPlaces_eq_zero F]
  omega

theorem re_embedding_comap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace E) (y : F) :
    ((w.comap (algebraMap F E)).embedding y).re = (w.embedding (algebraMap F E y)).re := by
  have key : ∀ φ : E →+* ℂ, (((InfinitePlace.mk φ).comap (algebraMap F E)).embedding y).re = (φ (algebraMap F E y)).re := by
    intro φ
    rw [InfinitePlace.comap_mk]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap F E)) with h | h
    · rw [h]; rfl
    · rw [h]; simp [ComplexEmbedding.conjugate_coe_eq]
  have := key w.embedding
  rwa [InfinitePlace.mk_embedding] at this

theorem mixedSpace_reCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  intro F E _ _ _ _ _ σ h
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  haveI : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  let g : InfinitePlace E ≃ {v : InfinitePlace F // InfinitePlace.IsReal v} :=
    (Equiv.ofBijective _ (comap_bij F E h.2.2.1)).trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)).symm
  have hg : ∀ w, (g w).1 = w.comap (algebraMap F E) := fun w => rfl
  let L : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun x w => x.1 (g w)
      invFun := fun f => (fun v => f (g.symm v), 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => Prod.ext (funext fun v => by simp) (Subsingleton.elim _ _)
      right_inv := fun f => funext fun w => by simp }
  refine ⟨L.toContinuousLinearEquiv, ?_, ?_⟩
  · haveI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // InfinitePlace.IsComplex w} → ℂ)) := by
      rw [volume_pi, Measure.pi_of_empty]; infer_instance
    have h1 : MeasurePreserving (Prod.fst : mixedEmbedding.mixedSpace F → _) volume volume :=
      measurePreserving_fst
    have h2 := volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm
    have heq : (L.toContinuousLinearEquiv : mixedEmbedding.mixedSpace F → InfinitePlace E → ℝ) =
        (MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace E => ℝ) g.symm) ∘ Prod.fst := by
      funext x w
      simp [L, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rw [heq]
    exact h2.comp h1
  · intro y
    funext w
    show (mixedEmbedding F y).1 (g w) = _
    rw [mixedEmbedding.mixedEmbedding_apply_isReal, reV]
    rw [← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ y), InfinitePlace.embedding_of_isReal_apply, hg]
    exact re_embedding_comap w y

end GlobalTheory.SnMass.ReCoords
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  atlas_forward_decl GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem abs_discr_eq_abs_discr_sq_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
  intro F E _ _ _ _ _ σ hcm hu
  have hd := (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, hcm.2.2.1] at h1
  have h2 : (((discr E).natAbs : ℕ) : ℝ) = (((discr F).natAbs ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
  simpa [Nat.cast_natAbs] using h2

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem absNorm_dInv_eq_abs_discr_pow_inv :
    ∀ (K : Type) [Field K] [NumberField K] (j : ℕ),
      (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  intro K _ _ j

  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm (K := K),
    NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs]
  push_cast
  rw [inv_pow]

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr : ∀ (K : Type) [Field K] [NumberField K] (j : ℕ), (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  first | exact @GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | exact GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | (intros; apply GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  first | exact @GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified | exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified | (intros; apply GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

theorem ringEquiv_mem_one (e : E ≃+* E) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    e x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_one] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  have hy : IsIntegral ℤ (e (algebraMap (𝓞 E) E y)) :=
    (RingOfIntegers.isIntegral_coe y).map (e : E →+* E).toIntAlgHom
  exact ⟨⟨_, hy⟩, rfl⟩

theorem ringEquiv_mem_dual (e : E ≃+* E) {x : E}
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    e x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))] at hx ⊢
  intro a ha
  have ha' : e.symm a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at ha ⊢
    exact ringEquiv_mem_one e.symm ha
  have h := hx _ ha'
  let f : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := e) (fun q => map_ratCast e q)
  have key : Algebra.traceForm ℚ E (e x) a = Algebra.traceForm ℚ E x (e.symm a) := by
    simp only [Algebra.traceForm_apply]
    have : e x * a = f (x * e.symm a) := by
      rw [map_mul]
      show e x * a = e x * e (e.symm a)
      rw [RingEquiv.apply_symm_apply]
    rw [this, Algebra.trace_eq_of_algEquiv]
  rw [key]; exact h

theorem ringEquiv_mem_pow (e : E ≃+* E) (M : Submodule (𝓞 E) E) (hM : ∀ x ∈ M, e x ∈ M) :
    ∀ (j : ℕ) (x : E), x ∈ M ^ j → e x ∈ M ^ j := by
  intro j
  induction j with
  | zero => intro x hx; rw [pow_zero] at hx ⊢; exact ringEquiv_mem_one e hx
  | succ j ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Submodule.mul_mem_mul (ih m hm) (hM n hn)
    · rw [map_add]; exact Submodule.add_mem _ ha hb

theorem ringEquiv_mem_dInv (e : E ≃+* E) (j : ℕ) (x : E) (hx : x ∈ dInv E j) : e x ∈ dInv E j := by
  have hd : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  rw [dInv, hd, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow] at hx ⊢
  exact ringEquiv_mem_pow e _ (fun y hy => ringEquiv_mem_dual e hy) j x hx

theorem conj_mem_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  intro F E _ _ _ _ _ σ _ j x hx
  have hb : Function.Bijective ((σ : E →+* E).toRatAlgHom) := AlgHom.bijective _
  exact ringEquiv_mem_dInv (RingEquiv.ofBijective (σ : E →+* E) hb) j x hx

end GlobalTheory.SnMass.VolN
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.conj_mem_dInv
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

open scoped Pointwise

namespace GlobalTheory.SnMass.SkewDom

theorem im_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace E) (z : E) :
    (w.embedding (σ z)).im = -(w.embedding z).im := by
  rw [h.2.2.2 w.embedding z]; simp

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem mem_skewLat_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ x ∈ I, σ x ∈ I)
    {θ : 𝓞 E} (hθ : (θ : E) + σ θ = 1) (c : ℝ) (z : InfinitePlace E → ℝ) :
    z ∈ (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) ↔
      ∃ b ∈ {b | ∃ x ∈ I, imV x = b}, z = (2 * c) • b := by
  change (∃ y ∈ I, (σ : E →+* E) y = -y ∧ ∀ w, z w = c * (w.embedding y).im) ↔ _
  simp only [AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨y, hy, hs, hz⟩
    have hθy : (θ : E) * y ∈ I := by
      have := (I : Submodule (𝓞 E) E).smul_mem θ hy
      rwa [Algebra.smul_def] at this
    refine ⟨imV ((θ : E) * y), ⟨(θ : E) * y, hθy, rfl⟩, ?_⟩
    funext w
    have hy2 : y = (θ : E) * y - σ ((θ : E) * y) := by
      rw [map_mul, hs]; linear_combination (-y) * hθ
    rw [hz w, Pi.smul_apply, smul_eq_mul, imV]
    conv_lhs => rw [hy2]
    rw [map_sub, Complex.sub_im, im_sigma hcm]; ring
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x - σ x, (I : Submodule (𝓞 E) E).sub_mem hx (hI x hx), ?_, fun w => ?_⟩
    · rw [map_sub, sigma_sigma hcm]; ring
    · rw [Pi.smul_apply, smul_eq_mul, imV, map_sub, Complex.sub_im, im_sigma hcm]; ring

theorem skewDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  intro F E _ _ _ _ _ σ hcm I hI θ hθ c hc D m hD hU hm
  have hmem := mem_skewLat_iff hcm hI hθ c
  have h2c : (2 * c) ≠ 0 := by positivity
  refine ⟨(2 * c) • D, hD.const_smul₀ _, fun v => ?_, ?_⟩
  · obtain ⟨l, ⟨hl, hlD⟩, hu⟩ := hU ((2 * c)⁻¹ • v)
    refine ⟨(2 * c) • l, ⟨(hmem _).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
    · refine Set.mem_smul_set.2 ⟨_, hlD, ?_⟩
      rw [smul_add, smul_inv_smul₀ h2c]
    · rintro l' ⟨hl', hl'D⟩
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hl'
      obtain ⟨d, hd, hdv⟩ := Set.mem_smul_set.1 hl'D
      have hbd : (2 * c)⁻¹ • v + b = d := by
        rw [← inv_smul_smul₀ h2c d, hdv, smul_add, inv_smul_smul₀ h2c]
      rw [hu b ⟨hb, hbd ▸ hd⟩]
  · rw [Measure.addHaar_smul, hm, Module.finrank_fintype_fun_eq_card, abs_of_pos (by positivity)]

end GlobalTheory.SnMass.SkewDom
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  atlas_forward_decl GlobalTheory.SnMass.SkewDom.skewDom
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem covolQuotient_real (d : ℝ) (f t : ℕ) (hd : 1 ≤ d) :
    ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2) =
      ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) *
        ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) := by
  have hd0 : 0 < d := by linarith
  have hd0' : d ≠ 0 := hd0.ne'
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le

  have h1 : d ^ (1 / 2 - 2 * (t : ℝ)) = Real.sqrt d / d ^ (2 * t) := by
    rw [Real.rpow_sub hd0, Real.sqrt_eq_rpow]
    congr 1
    exact_mod_cast Real.rpow_natCast d (2 * t)
  rw [Real.sqrt_sq hd0.le, h1]
  calc ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * d
      = ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * (Real.sqrt d * Real.sqrt d) := by rw [hs]
    _ = _ := by
        rw [← pow_mul, show 2 * (2 * t) = 2 * t + 2 * t by ring, pow_add]
        field_simp

theorem covolQuotient_arith : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c →
    ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) =
      ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m →
    ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  intro d c f t m hd hc h
  have hd0 : 0 < d := by linarith
  have hY : 0 < (d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d :=
    mul_pos (mul_pos (inv_pos.mpr (pow_pos hd0 _)) (by norm_num)) (Real.sqrt_pos.mpr hd0)
  have hZ : 0 ≤ (2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hd0.le _)

  rw [covolQuotient_real d f t hd, ENNReal.ofReal_mul hY.le] at h
  have hm : m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) :=
    ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hY).ne' ENNReal.ofReal_ne_top).mp h).symm
  rw [hm, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) f)]
  congr 1
  have h2 : (2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f = 1 := by rw [← mul_pow]; norm_num
  calc (2 * c) ^ f * ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)))
      = ((2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f) * (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by ring
    _ = d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f := by rw [h2, one_mul]

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolumeQuotient_ofReal_identity : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c → ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) = ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m → ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  atlas_forward_decl GlobalTheory.covolQuotient_arith
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.SkewVol
theorem dom_of_basis {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Finite ι]
    (b : Module.Basis ι ℝ W) (v : W) :
    ∃! l, l ∈ (Submodule.span ℤ (Set.range b) : Set W) ∧ v + l ∈ ZSpan.fundamentalDomain b := by
  obtain ⟨⟨l, hl⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
  refine ⟨l, ⟨hl, by simpa [Submodule.vadd_def, add_comm] using h1⟩, ?_⟩
  rintro l' ⟨hl', h'⟩
  have := h2 ⟨l', hl'⟩ (by simpa [Submodule.vadd_def, add_comm] using h')
  simpa using congrArg Subtype.val this

theorem dInv_ne_zero (K : Type) [Field K] [NumberField K] (j : ℕ) : dInv K j ≠ 0 := by
  unfold dInv
  refine pow_ne_zero _ (inv_ne_zero ?_)
  exact FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem skew_covol_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  intro F E _ _ _ _ _ σ hCM hU t c hc
  have hTC : IsTotallyComplex E := hCM.2.1
  have hTR : IsTotallyReal F := hCM.1
  have hσw : ∀ (w : InfinitePlace E) (x : E), w.embedding (σ x) = star (w.embedding x) :=
    fun w x => hCM.2.2.2 w.embedding x
  have hre : ∀ x : E, reV (σ x) = reV x := fun x => funext fun w => by simp [reV, hσw]
  have him : ∀ x : E, imV (σ x) = -imV x := fun x => funext fun w => by simp [imV, hσw]
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex E hTC
  obtain ⟨ι, _, b, hbs, hbv⟩ := GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving E volume e he (Units.mk0 (dInv E (2 * t)) (dInv_ne_zero E _))
  obtain ⟨e1, he1, he1x⟩ := GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords F E σ hCM
  obtain ⟨ι1, _, b1, hb1s, hb1v⟩ :=
    GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving F volume e1 he1 (Units.mk0 (dInv F (2 * t)) (dInv_ne_zero F _))
  simp only [Units.val_mk0] at hbs hbv hb1s hb1v
  set Λ := Submodule.span ℤ (Set.range b) with hΛdef
  have hΛ : ∀ p, p ∈ Λ ↔ ∃ x ∈ dInv E (2 * t), (reV x, imV x) = p := by
    intro p
    rw [← SetLike.mem_coe, hbs]
    simp [hex]
  have hL1 : ∀ a, a ∈ (Submodule.span ℤ (Set.range b1) : Set (InfinitePlace E → ℝ)) ↔
      (a, (0 : InfinitePlace E → ℝ)) ∈ Λ := by
    intro a
    rw [hb1s, hΛ]
    simp only [Set.mem_image, Set.mem_setOf_eq, he1x, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU (2 * t) (algebraMap F E y)).2 ⟨y, hy, rfl⟩
      exact ⟨_, h.1, rfl, h.2⟩
    · rintro ⟨x, hx, rfl, h0⟩
      obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU _ _).1 ⟨hx, h0⟩
      exact ⟨y, hy, rfl⟩
  have hD1 : ∀ a, ∃! l, l ∈ {a : InfinitePlace E → ℝ | (a, (0 : InfinitePlace E → ℝ)) ∈ Λ.toAddSubgroup} ∧
      a + l ∈ ZSpan.fundamentalDomain b1 := by
    intro a
    obtain ⟨l, hl, hu⟩ := dom_of_basis b1 a
    exact ⟨l, ⟨(hL1 l).1 hl.1, hl.2⟩, fun l' hl' => hu l' ⟨(hL1 l').2 hl'.1, hl'.2⟩⟩
  have h2 : ∀ a y, (a, y) ∈ Λ → ((0 : InfinitePlace E → ℝ), (2 : ℝ) • y) ∈ Λ := by
    intro a y hay
    obtain ⟨x, hx, hxe⟩ := (hΛ _).1 hay
    rw [Prod.mk.injEq] at hxe
    refine (hΛ _).2 ⟨x - σ x, Submodule.sub_mem (dInv E (2 * t) : Submodule (𝓞 E) E) hx (GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx), ?_⟩
    have h1 : reV (x - σ x) = reV x - reV (σ x) := funext fun w => by simp [reV]
    have h1' : imV (x - σ x) = imV x - imV (σ x) := funext fun w => by simp [imV]
    rw [h1, h1', hre, him, ← hxe.2]
    refine Prod.ext ?_ ?_
    · simp
    · funext w; simp; ring
  have hsp : Submodule.span ℝ (Λ : Set ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ))) = ⊤ := by
    rw [hΛdef, Submodule.span_span_of_tower, b.span_eq]
  obtain ⟨D2, hD2m, hD2⟩ := GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' Λ hsp h2
  have hprod := GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension Λ.toAddSubgroup _ D2 hD1 hD2
  have heq := GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable ((volume : Measure (InfinitePlace E → ℝ)).prod (volume : Measure (InfinitePlace E → ℝ))) Λ _ _ ((ZSpan.fundamentalDomain_measurableSet b1).prod hD2m)
    (ZSpan.fundamentalDomain_measurableSet b) hprod (dom_of_basis b)
  rw [Measure.prod_prod, ← Measure.volume_eq_prod, hbv, hb1v] at heq
  have hL2 : ∀ y, (∃ a, (a, y) ∈ Λ) ↔ ∃ x ∈ dInv E (2 * t), imV x = y := by
    intro y
    simp only [hΛ, Prod.mk.injEq]
    constructor
    · rintro ⟨a, x, hx, -, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, x, hx, rfl, rfl⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' F E σ hCM hU
  have hfin := GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts F E σ hCM (dInv E (2 * t)) (fun x hx => GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx) θ hθ c hc D2 _
    hD2m (fun y => by simpa only [Set.mem_setOf_eq, hL2] using hD2 y) rfl
  have hd : (1 : ℝ) ≤ |(discr F : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero F)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hnc : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h
    exact h.symm
  have hnr : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension F E σ hCM hU, hnc, hnr] at heq
  rw [GlobalTheory.T.covolumeQuotient_ofReal_identity _ c _ t _ hd hc heq.symm] at hfin
  exact hfin

end GlobalTheory.SnMass.SkewVol
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewLattice_inverseDifferentPow_covolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  atlas_forward_decl GlobalTheory.SnMass.SkewVol.skew_covol_dInv
end
