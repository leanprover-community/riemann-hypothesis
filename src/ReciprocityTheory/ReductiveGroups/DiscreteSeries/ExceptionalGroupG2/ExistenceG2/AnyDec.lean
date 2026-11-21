import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RangeDatumEmbedding
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamEquivData

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section One

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

variable {lam : Fin n → ℝ}

theorem lowKMultOne_of_cas (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcas : CasOnSmooth ε lam σ)
    (S S' : Submodule ℂ H) (hS : Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S)
    (hS' : Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S') : S = S' := by
  obtain ⟨V, hV, hV0, hVK, hc⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS hcas
  obtain ⟨-, -, hσ, hirr, -⟩ := hDS
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have htop := data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0
  rw [data_lowK_eq hgap hσ hD hV hc hVK S (htop ▸ le_top) hS,
    data_lowK_eq hgap hσ hD hV hc hVK S' (htop ▸ le_top) hS']

private theorem exists_linearIsometryEquiv_of_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : Submodule ℂ H) (hC : C = ⊤) : ∃ W : C ≃ₗᵢ[ℂ] H, ∀ y : C, W y = y :=
  ⟨LinearIsometryEquiv.ofSurjective C.subtypeₗᵢ
    (fun y => ⟨⟨y, by rw [hC]; exact Submodule.mem_top⟩, rfl⟩), fun _ => rfl⟩

theorem equiv_sigLam_of_cas (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcas : CasOnSmooth ε lam σ)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = σ g (U x) := by
  obtain ⟨V, hV, hV0, hVK, hc⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS hcas
  obtain ⟨-, -, hσ, hirr, -⟩ := hDS
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have htop := data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0
  obtain ⟨U, hU⟩ := sigLam_equiv_data hgap hP hv₀ hσ hD hV hc hVK hV0
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_of_eq_top _ htop
  refine ⟨U.trans W, fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, hW]
  exact hU g hg x

end One

private theorem exists_coe_linearIsometryEquiv_of_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : Submodule ℂ H) (hC : C = ⊤) : ∃ W : C ≃ₗᵢ[ℂ] H, ∀ y : C, W y = y :=
  ⟨LinearIsometryEquiv.ofSurjective C.subtypeₗᵢ
    (fun y => ⟨⟨y, by rw [hC]; exact Submodule.mem_top⟩, rfl⟩), fun _ => rfl⟩

theorem dsUnique_of_cas {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hcas : CasOnSmooth ε lam σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hDS' : Formalism.MainNotions.S.IsDS ε lam σ')
    (hcas' : CasOnSmooth ε lam σ') :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  obtain ⟨V, hV, hV0, hVK, hc⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS hcas
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS' hcas'
  obtain ⟨-, -, hσ, hirr, -⟩ := hDS
  obtain ⟨-, -, hσ', hirr', -⟩ := hDS'
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hD' := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ'
  obtain ⟨W, hW⟩ := exists_coe_linearIsometryEquiv_of_eq_top _ (data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0)
  obtain ⟨W', hW'⟩ := exists_coe_linearIsometryEquiv_of_eq_top _ (data_closGen_eq_top hgap hσ' hD' hV' hc' hVK' hirr' hV0')
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ hD hV hc hVK hV0 hσ' hD' hV' hc' hVK' hV0'
  have hWs : ∀ z : H, ((W.symm z : closGen (ReciprocityTheory.ChartRestriction.DS.smE ε σ) V) : H) = z := fun z => by
    rw [← hW]; exact W.apply_symm_apply z
  refine ⟨(W.symm.trans U).trans W', fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, hW']
  exact hU g hg _ _ (by rw [hWs, hWs])

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Datum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem cfa_no_of_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hvog : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S →
      Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hne w hw hkhw
  by_contra hw0
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hSf : FiniteDimensional ℂ (layer ε E V 1) := finiteDimensional_layer hV.1 1
  have hSk : IsKStableSub ε E (layer ε E V 1) := layer_kStable hE hV.2.1 1
  obtain ⟨S', -, -, hS'⟩ := exists_irr_sub_of_khw hE hU _ hSf hSk hw hw0 hkhw
  have hK' := kStable_of_isKStableSub hσ hD S' hS'.1 hS'.2.1
  have hKT := isKTypeOf_of_isKIrrHW hσ hD hS' hK'
    (fun μ x hx hx0 hμ => weights_le_of_irr_hw hE hU hS' hx hx0 hμ)
  have h1 := hvog _ _ hKT
  have h2 := vNormSq_lowK_sub_root_lt hgap.1 hab hne
  rw [mir_lowK_eq] at h1 h2
  linarith

end Datum

section Arbitrary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem cf_datum_of_copies (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcV : CasOnCopies ε lam σ) :
    ∃ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V ∧ V ≠ ⊥ ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) ∧
      (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) ∧ closGen (smE ε σ) V = ⊤ := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨V, hV, hV0, hVK, -⟩ := exists_datum_of_isKTypeOf hσ hS
  have hV' : IsKIrrHW ε (smE ε σ) (lowK ε lam) V := hV
  have hD := isDerivedOn_smE hσ
  have hc := hcV V hV' hVK
  exact ⟨V, hV', hV0, hVK, hc, data_closGen_eq_top hgap hσ hD hV' hc hVK hDS.2.2.2.1 hV0⟩

theorem casOnSmooth_of_datum (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) {V : Submodule ℂ (smD ε σ)}
    (hV : IsKIrrHW ε (smE ε σ) (lowK ε lam) V) (hV0 : V ≠ ⊥)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hc : ∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) : CasOnSmooth ε lam σ := by
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  intro v hv
  let v' : smD ε σ := ⟨v, (mem_smD_iff ε σ v).2 hv⟩
  have hvv : (v' : H) = v := rfl
  rw [← hvv, casU_eq_casimir hD v', ← sub_eq_zero]
  have hperp : ((casimir (smE ε σ) v' : smD ε σ) : H) - ((casVal lam : ℝ) : ℂ) • (v' : H) ∈
      ((genSub (smE ε σ) V).map (smD ε σ).subtype)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hu
    have hcx : ((casimir (smE ε σ) x : smD ε σ) : H) = ((casVal lam : ℝ) : ℂ) • (x : H) := by
      rw [← casU_eq_casimir hD x]
      exact data_casU hgap hσ hD hV hc hVK x hx
    have hsym := cf_inner_casimir hU x v'
    rw [Submodule.coe_inner, Submodule.coe_inner, hcx] at hsym
    rw [Submodule.subtype_apply, inner_sub_right, ← hsym, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, sub_self]
  have htop' : ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure = ⊤ := htop
  rw [Submodule.topologicalClosure_eq_top_iff.1 htop'] at hperp
  exact (Submodule.mem_bot ℂ).1 hperp

theorem casOnSmooth_of_copies (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcV : CasOnCopies ε lam σ) :
    CasOnSmooth ε lam σ := by
  obtain ⟨V, hV, hV0, hVK, hc, -⟩ := cf_datum_of_copies hDS hgap hcV
  exact casOnSmooth_of_datum hgap hDS.2.2.1 hDS.2.2.2.1 hV hV0 hVK hc

end Arbitrary

theorem isDS_props_of_copies {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ}
    (hh : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hbig : 2 * (n : ℝ) < h)
    (hall : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → CasOnCopies ε lam σ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hDS : Formalism.MainNotions.S.IsDS ε lam σ) :
    CasOnSmooth ε lam σ ∧
      (∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
        Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S') ∧
      (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} :
        Submodule ℂ H)) ∧
      (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
        ∀ v ∈ S, IsSmoothVecU ε σ v) ∧
      ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ' →
        ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hbig⟩
  have hcas := casOnSmooth_of_copies hDS hgap (hall H σ hDS)
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨V, hV, -, hVK, hc, htop⟩ := cf_datum_of_copies hDS hgap (hall H σ hDS)
  have hD := isDerivedOn_smE hσ
  refine ⟨hcas, fun S S' hS hS' => lowKMultOne_of_cas hDS hgap hcas S S' hS hS', fun μ => ?_,
    fun S hSf hSK v hv => ?_, fun H' _ _ _ σ' hDS' => ?_⟩
  · have hadm := data_admissible hgap hσ hD hV hc hVK μ
    rw [htop] at hadm
    have hset : {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} =
        {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} := by
      ext S
      simp
    rw [hset] at hadm
    exact hadm
  · have hle : S ≤ closGen (smE ε σ) V := by rw [htop]; exact le_top
    have hmem := data_kfin_le hgap hσ hD hV hc hVK S hle hSf hSK hv
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.1 hmem
    exact (mem_smD_iff ε σ _).1 x.2
  · exact dsUnique_of_cas hgap hDS hcas hDS' (casOnSmooth_of_copies hDS' hgap (hall H' σ' hDS'))

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Datum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem cf_no_of_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hvog : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S →
      Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hne w hw hkhw
  exact cfa_no_of_vogan hgap hσ hD hV hVK hvog a b hab hne w hw hkhw

theorem casOnDatum_of_isDS (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  exact casimir_eq_casVal_of_no hgap.1 hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV
    (cf_no_of_vogan hgap hσ hD hV hVK hDS.2.2.2.2.2.2)

end Datum

section Arbitrary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem casOnSmooth_of_isDS (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) : CasOnSmooth ε lam σ := by
  exact casOnSmooth_of_copies hDS hgap
    (fun V hV hVK => casOnDatum_of_isDS hDS hgap (isDerivedOn_smE hDS.2.2.1) hV hVK)

theorem equiv_sigLam_of_isDS (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = σ g (U x) := by
  exact equiv_sigLam_of_cas hDS hgap (casOnSmooth_of_isDS hDS hgap) hP hv₀

end Arbitrary

theorem isDS_props_of_gap :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → 2 * (n : ℝ) < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ →
        CasOnSmooth ε lam σ ∧
        (∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
          Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S') ∧
        (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} :
          Submodule ℂ H)) ∧
        (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
          ∀ v ∈ S, IsSmoothVecU ε σ v) ∧
        ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
          (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ' →
          ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  intro n ε lam hlam h hh hbig H _ _ _ σ hDS
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hbig⟩
  exact isDS_props_of_copies hlam hh hbig (fun H' _ _ _ σ' hDS' V hV hVK =>
    casOnDatum_of_isDS hDS' hgap (isDerivedOn_smE hDS'.2.2.1) hV hVK) H σ hDS

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

end Gen

section Main

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem anyF (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) :
    ∃ j : T.V →L[ℂ] H, (∀ v, ‖j v‖ = ‖v‖) ∧
      (∀ (k : S7.KG ε) (v : T.V), σ (S7.toMK k) (j v) = j (T.op k v)) ∧
      LinearMap.range (j : T.V →ₗ[ℂ] H) = Formalism.MainNotions.S.lowKSub ε lam σ ∧
      ∀ g ∈ UJset ε, (ContinuousLinearMap.adjoint j).comp ((σ g).comp j) = Ψ g := by
  have hw : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hDS hgap hP hw
  have hc0 := datumEmbedding_highest_ne_zero hgap hP hw
  set c : ℝ := ‖uniformisationL2 ε Ψ T.w T.w‖ with hc
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc0)
  let jl : T.V →ₗ[ℂ] H := ((c : ℂ)⁻¹) • (U.toLinearEquiv.toLinearMap ∘ₗ datumEmbedding hP T.w)
  let j : T.V →L[ℂ] H := LinearMap.toContinuousLinearMap jl
  have hjv : ∀ v, j v = ((c : ℂ)⁻¹) • U (datumEmbedding hP T.w v) := fun v => rfl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  have hkey : ∀ g ∈ UJset ε, ∀ v v', inner ℂ (j v') (σ g (j v)) = inner ℂ v' (Ψ g v) := by
    intro g hg v v'
    rw [hjv, hjv, map_smul, ← hU g hg, inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have e := formulaF_sigLam hgap hP hw hg v v'
    rw [show datumEmbedding hP T.w v = (⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩ : Hlam ε Ψ T.w) from rfl,
      show datumEmbedding hP T.w v' = (⟨uniformisationL2 ε Ψ T.w v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ T.w) from rfl, e]
    rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
    rw [hc]
  have hiso : ∀ v, ‖j v‖ = ‖v‖ := by
    intro v
    have e := hkey 1 h1 v v
    rw [hDS.2.2.1.1.1, hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    have e2 : ‖j v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, e]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e2
  have hK : ∀ (k : S7.KG ε) v, σ (S7.toMK k) (j v) = j (T.op k v) := by
    intro k v
    rw [hjv, hjv, map_smul, ← hU _ (ffa_toMK_mem k)]
    congr 2
    apply Subtype.ext
    rw [sigLam_coe hgap hP hw (ffa_toMK_mem k)]
    exact rightRegular_datumEmbedding hP T.w v k
  have hrange : LinearMap.range (j : T.V →ₗ[ℂ] H) =
      (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap := by
    show LinearMap.range jl = _
    rw [LinearMap.range_smul _ _ (inv_ne_zero hcne), LinearMap.range_comp, range_datumEmbedding]
  have hintU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.toLinearMap (sigLam ε Ψ T.w g x) =
      σ g (U.toLinearEquiv.toLinearMap x) := by
    intro g hg x
    rw [mir_Kset_eq] at hg
    exact hU g (UnitaryGroupOfForm.K_mem_UJ hg) x
  have hintS : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.symm.toLinearMap (σ g x) =
      sigLam ε Ψ T.w g (U.toLinearEquiv.symm.toLinearMap x) := by
    intro g hg x
    apply U.injective
    have e := hintU g hg (U.toLinearEquiv.symm x)
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at e ⊢
    rw [e]
    simp
  have hlow : Formalism.MainNotions.S.lowKSub ε lam σ = (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap := by
    have hdef : Formalism.MainNotions.S.lowKSub ε lam σ =
        sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} := rfl
    have hset : {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} =
        {(lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap} := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hS
        have h2 := (sigLam_lowK hgap hP hw).2 _
          ((isKTypeOf_map_iff _ U.toLinearEquiv.symm.injective hintS _ S).1 hS)
        rw [← h2, ← Submodule.map_comp]
        ext x
        simp
      · rintro rfl
        exact (isKTypeOf_map_iff _ U.toLinearEquiv.injective hintU _ _).1 (sigLam_lowK hgap hP hw).1
    rw [hdef, hset, sSup_singleton]
  refine ⟨j, hiso, hK, hrange.trans hlow.symm, fun g hg => ?_⟩
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, hkey g hg v v']


end Main

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
