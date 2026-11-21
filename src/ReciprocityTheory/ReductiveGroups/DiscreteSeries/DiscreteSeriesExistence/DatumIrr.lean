import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def dinj_jLin (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := uniformisationL2 ε Ψ v₀
  map_add' := datumEmbedding_add hP v₀
  map_smul' := datumEmbedding_smul hP v₀

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dinj_continuousOn_of_smoothOnGV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg₀U)] with g hg
  exact hfF g hg.2 hg.1

end


theorem uniformisationL2_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (uniformisationL2 ε Ψ v₀) := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat g ∈ UJset ε := fun g => g.2
  have hum : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hΨu : Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
    (dinj_continuousOn_of_smoothOnGV hP.2.2.1).comp_continuous hum hmem
  have hfc : ∀ v, Continuous (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) := by
    intro v
    simp only [jfun]
    exact continuous_const.inner (hΨu.clm_apply continuous_const)
  have hML : ∀ v, MemLp (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) 2
      (Formalism.REAL.muG ε) := by
    intro v
    have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
    have h0 := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
    have h2 := ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h0
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun g => ?_) h2
    simp [jfun] <;> rfl
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by unfold Formalism.REAL.muG; infer_instance
  have hz : ∀ v, uniformisationL2 ε Ψ v₀ v = 0 ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 := by
    intro v
    have hm := hML v
    have e1 : uniformisationL2 ε Ψ v₀ v = hm.toLp _ := by
      unfold uniformisationL2 toL2
      exact dif_pos hm
    rw [e1, Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h g
      have h5 := ((hfc v).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).mp
        (hm.coeFn_toLp.symm.trans h)
      exact congrFun h5 g
    · intro h
      exact hm.coeFn_toLp.trans (Filter.Eventually.of_forall fun g => h g)
  have hstab : ∀ (k : S7.KG ε) (v : T.V),
      (∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0) →
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ (T.op k v) (Formalism.MainNotions.S.umat g) = 0 := by
    intro k v hv g
    have hk := hP.1 1 k (Formalism.MainNotions.S.umat g) (hmem g)
    have ht1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    have ho1 : T.op 1 = 1 := by simp [S7.KType.op]
    rw [ht1, ho1, one_mul, one_mul] at hk
    let y : Formalism.REAL.UJ ε := (k : S7.UJ ε)
    have hy : Formalism.MainNotions.S.umat (g * y) = Formalism.MainNotions.S.umat g * S7.toMK k := rfl
    have h3 := hv (g * y)
    rw [hy] at h3
    simp only [jfun] at h3 ⊢
    rw [hk] at h3
    simpa using h3
  have hne : uniformisationL2 ε Ψ v₀ v₀ ≠ 0 := by
    intro h0
    have h6 : jfun Ψ v₀ v₀ 1 = 0 := (hz v₀).1 h0 1
    simp only [jfun, hP.2.1, ContinuousLinearMap.one_apply] at h6
    exact hv₀ (inner_self_eq_zero.mp h6)
  have hker : ∀ v, v ∈ LinearMap.ker (dinj_jLin hP v₀) ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 :=
    fun v => LinearMap.mem_ker.trans (hz v)
  rcases T.irred (LinearMap.ker (dinj_jLin hP v₀))
      (fun k v hv => (hker _).2 (hstab k v ((hker v).1 hv))) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    have hv : v₀ ∈ LinearMap.ker (dinj_jLin hP v₀) := by
      rw [h]
      exact Submodule.mem_top
    exact hne (LinearMap.mem_ker.1 hv)

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def jSm (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] smD ε (rreg ε) where
  toFun v := ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  map_add' v v' := Subtype.ext (datumEmbedding_add hP v₀ v v')
  map_smul' c v := Subtype.ext (datumEmbedding_smul hP v₀ c v)

theorem jSm_coe (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    ((jSm hP v₀ v : smD ε (rreg ε)) : L2 ε) = uniformisationL2 ε Ψ v₀ v := rfl

theorem datumV_eq_range (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    datumV ε Ψ v₀ = LinearMap.range (jSm hP v₀) := by
  ext x
  rw [mem_datumV_iff hP v₀ x, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩

theorem smE_jSm (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) :
    smE ε (rreg ε) a b (jSm hP v₀ v) = jSm hP v₀ (T.dτ (Matrix.single a b 1) v) :=
  Subtype.ext (rightDerivative_datum_embedding hP v₀ v hab)

theorem jSm_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (jSm hP v₀) := by
  intro v v' h
  apply uniformisationL2_injective hP hv₀
  have := congrArg (fun x : smD ε (rreg ε) => (x : L2 ε)) h
  simpa [jSm_coe] using this

theorem datumV_isKIrrHW (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam) (datumV ε Ψ v₀) := by
  rw [datumV_eq_range hP v₀]
  refine ⟨LinearMap.finiteDimensional_range _, ?_, ?_, ?_⟩
  · rintro a b hab x ⟨v, rfl⟩
    exact ⟨T.dτ (Matrix.single a b 1) v, (smE_jSm hP v₀ v hab).symm⟩
  · intro S' hS' hst
    have hW : ∀ a b, ε a = ε b → ∀ v ∈ S'.comap (jSm hP v₀),
        T.dτ (Matrix.single a b 1) v ∈ S'.comap (jSm hP v₀) := by
      intro a b hab v hv
      rw [Submodule.mem_comap] at hv ⊢
      rw [← smE_jSm hP v₀ v hab]
      exact hst a b hab _ hv
    rcases HW.KType.dτ_irred T _ hW with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := hS' hx
      have hv : v ∈ S'.comap (jSm hP v₀) := hx
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro x ⟨v, rfl⟩
      have hv : v ∈ S'.comap (jSm hP v₀) := by rw [h]; trivial
      exact hv
  · refine ⟨jSm hP v₀ T.w, ⟨T.w, rfl⟩, ?_, ?_, ?_⟩
    · intro h0
      apply HW.KType.w_ne_zero T
      apply jSm_injective hP hv₀
      rw [h0, map_zero]
    · intro a
      rw [smE_jSm hP v₀ T.w rfl, T.w_wt a, map_smul]
    · intro a b _ hab
      rw [smE_jSm hP v₀ T.w hab, T.w_hw a b ‹_› hab, map_zero]

end ReciprocityTheory.ChartRestriction.DS
end
end
