import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul

section
noncomputable section

open Finset Matrix WithLp

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}

def diagι (φ : V₁ →ₗ[ℂ] V₂) : V₁ →ₗ[ℂ] sD D₁ D₂ :=
  ofP ∘ₗ (V₁.subtype.prod (V₂.subtype ∘ₗ φ))

theorem diagι_apply (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    diagι φ v = ofP ((v : D₁), ((φ v : V₂) : D₂)) := rfl

theorem coe_diagι (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    ((diagι φ v : sD D₁ D₂) : WithLp 2 (H₁ × H₂)) =
      toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂)) := rfl

def diagSub (φ : V₁ →ₗ[ℂ] V₂) : Submodule ℂ (sD D₁ D₂) := LinearMap.range (diagι φ)

theorem sE_diagι (φ : V₁ →ₗ[ℂ] V₂) (hst : IsKStableSub ε E₁ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    sE E₁ E₂ a b (diagι φ v) = diagι φ ⟨E₁ a b v, hst a b hab _ v.2⟩ := by
  rw [diagι_apply, diagι_apply]
  simp only [sE, lift_ofP]
  rw [hcomm a b hab v]

theorem diagSub_isKIrrHW (φ : V₁ →ₗ[ℂ] V₂) {Λ : Fin n → ℝ} (hV₁ : IsKIrrHW ε E₁ Λ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩ : V₂) : D₂)) :
    IsKIrrHW ε (sE E₁ E₂) Λ (diagSub φ) := by
  unfold IsKIrrHW
  have : FiniteDimensional ℂ V₁ := hV₁.1
  have hstab : IsKStableSub ε (sE E₁ E₂) (diagSub φ) := by
    intro a b hab x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    rw [sE_diagι φ hV₁.2.1 hcomm hab v]
    exact LinearMap.mem_range_self _ _
  refine ⟨inferInstanceAs (FiniteDimensional ℂ (LinearMap.range (diagι φ))), hstab, ?_, ?_⟩
  · intro S' hS' hS'st
    let T : Submodule ℂ D₁ := (S'.comap (diagι φ)).map V₁.subtype
    have hTle : T ≤ V₁ := by
      intro u hu
      obtain ⟨v, -, rfl⟩ := Submodule.mem_map.mp hu
      exact v.2
    have hTst : IsKStableSub ε E₁ T := by
      intro a b hab u hu
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩, ?_, rfl⟩
      show diagι φ _ ∈ S'
      rw [← sE_diagι φ hV₁.2.1 hcomm hab v]
      exact hS'st a b hab _ hv
    rcases hV₁.2.2.1 T hTle hTst with hT | hT
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp (hS' hx)
      have hvT : (v : D₁) ∈ T := Submodule.mem_map.mpr ⟨v, hx, rfl⟩
      rw [hT, Submodule.mem_bot] at hvT
      have hv0 : v = 0 := (Submodule.coe_eq_zero).mp hvT
      rw [hv0, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      intro x hx
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
      have hvT : (v : D₁) ∈ T := by
        rw [hT]
        exact v.2
      obtain ⟨v', hv', hvv'⟩ := Submodule.mem_map.mp hvT
      have hv'v : v' = v := Subtype.ext hvv'
      rw [← hv'v]
      exact hv'
  · obtain ⟨w, hwV, hw0, hK⟩ := hV₁.2.2.2
    obtain ⟨hwa, hwb⟩ := hK
    refine ⟨diagι φ ⟨w, hwV⟩, LinearMap.mem_range_self _ _, ?_, ?_⟩
    · intro h
      apply hw0
      have h1 := congrArg (fun x => (toP x).1) h
      simpa [diagι_apply, toPrimitive_ofPrimitive] using h1
    · refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
      · rw [sE_diagι φ hV₁.2.1 hcomm (a := a) (b := a) rfl, ← map_smul]
        congr 1
        exact Subtype.ext (hwa a)
      · rw [sE_diagι φ hV₁.2.1 hcomm hε]
        have h0 : (⟨E₁ a b w, hV₁.2.1 a b hε _ hwV⟩ : V₁) = 0 := Subtype.ext (hwb a b hab hε)
        rw [h0, map_zero]

theorem casimir_diagSub (φ : V₁ →ₗ[ℂ] V₂) {c : ℂ}
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = c • v) (hc₂ : ∀ v ∈ V₂, casimir E₂ v = c • v) :
    ∀ x ∈ diagSub φ, casimir (sE E₁ E₂) x = c • x := by
  intro x hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
  rw [casimir_sE, diagι_apply]
  simp only [lift_ofP]
  rw [hc₁ _ v.2, hc₂ _ (φ v).2, ← Prod.smul_mk, map_smul]

end USum

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rigid_universal {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} (hσ₁ : IsURepOn (UJset ε) σ₁)
    {D₁ : Submodule ℂ H₁} {E₁ : Fin n → Fin n → Module.End ℂ D₁} (hD₁ : IsDerivedOn ε σ₁ D₁ E₁)
    {V₁ : Submodule ℂ D₁} (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (hσ₂ : IsURepOn (UJset ε) σ₂)
    {D₂ : Submodule ℂ H₂} {E₂ : Fin n → Fin n → Module.End ℂ D₂} (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    {V₂ : Submodule ℂ D₂} (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v)
    (hgap : StdGap ε lam) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    (hφI : ∀ v v' : V₁, inner ℂ (((φ v' : V₂) : D₂) : H₂) (((φ v : V₂) : D₂) : H₂) =
      inner ℂ ((v' : D₁) : H₁) ((v : D₁) : H₁)) :
    ∀ g ∈ UJset ε, ∀ v v' : V₁,
      inner ℂ (((φ v' : V₂) : D₂) : H₂) (σ₂ g (((φ v : V₂) : D₂) : H₂)) =
        inner ℂ ((v' : D₁) : H₁) (σ₁ g ((v : D₁) : H₁)) := by
  have : FiniteDimensional ℂ V₁ := hV₁.1
  have hσ := USum.isURepOn_sσ hσ₁ hσ₂
  have hD := USum.isDerivedOn_sσ hD₁ hD₂
  have hcomm := fun a b (hab : ε a = ε b) (v : V₁) =>
    USum.phi_E_comm hD₁ hD₂ hV₁.2.1 hVK₁ φ hφK hab v
  have hV := USum.diagSub_isKIrrHW φ hV₁ hcomm
  have hc := USum.casimir_diagSub (E₁ := E₁) (E₂ := E₂) φ hc₁ hc₂
  have hVK : ∀ k ∈ Kset ε, ∀ x ∈ USum.diagSub φ, ∃ w ∈ USum.diagSub φ,
      (w : WithLp 2 (H₁ × H₂)) = USum.sσ σ₁ σ₂ k x := by
    rintro k hk _ ⟨v, rfl⟩
    obtain ⟨w₁, hw₁, e⟩ := hVK₁ k hk _ v.2
    refine ⟨USum.diagι φ ⟨w₁, hw₁⟩, ⟨_, rfl⟩, ?_⟩
    rw [USum.coe_diagι, USum.coe_diagι]
    show _ = WithLp.toLp 2 (σ₁ k ((v : D₁) : H₁), σ₂ k (((φ v : V₂) : D₂) : H₂))
    rw [← e, ← hφK k hk v ⟨w₁, hw₁⟩ e]
  let R : WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := USum.sop 1 (-1)
  let j' : USum.diagSub φ →ₗ[ℂ] WithLp 2 (H₁ × H₂) :=
    R.toLinearMap ∘ₗ (USum.sD D₁ D₂).subtype ∘ₗ (USum.diagSub φ).subtype
  have hj : ∀ k ∈ Kset ε, ∀ v w : USum.diagSub φ,
      (((w : USum.sD D₁ D₂)) : WithLp 2 (H₁ × H₂)) = USum.sσ σ₁ σ₂ k ((v : USum.sD D₁ D₂) : _) →
      j' w = USum.sσ σ₁ σ₂ k (j' v) := by
    intro k _ v w h
    show USum.sop 1 (-1) ((w : USum.sD D₁ D₂) : WithLp 2 (H₁ × H₂)) =
      USum.sop (σ₁ k) (σ₂ k) (USum.sop 1 (-1) ((v : USum.sD D₁ D₂) : WithLp 2 (H₁ × H₂)))
    rw [h]
    exact USum.sop_neg_comm _ _ _
  have horth : ∀ v v' : USum.diagSub φ, inner ℂ (j' v') ((v : USum.sD D₁ D₂) : WithLp 2 (H₁ × H₂)) = 0 := by
    rintro ⟨_, ⟨v, rfl⟩⟩ ⟨_, ⟨v', rfl⟩⟩
    show inner ℂ (WithLp.toLp 2 (((v' : D₁) : H₁), -(((φ v' : V₂) : D₂) : H₂)))
      (WithLp.toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂))) = 0
    rw [USum.inner_sum]
    simp only [inner_neg_left, hφI]
    exact add_neg_cancel _
  intro g hg v v'
  have key := rigid_orth hgap hσ hD hV hc hVK j' hj horth g hg
    ⟨USum.diagι φ v, ⟨v, rfl⟩⟩ ⟨USum.diagι φ v', ⟨v', rfl⟩⟩
  change inner ℂ (WithLp.toLp 2 (((v' : D₁) : H₁), -(((φ v' : V₂) : D₂) : H₂)))
    (USum.sop (σ₁ g) (σ₂ g) (WithLp.toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂)))) = 0 at key
  rw [USum.inner_sum, USum.sop_apply] at key
  simp only [inner_neg_left] at key
  rw [← sub_eq_add_neg, sub_eq_zero] at key
  exact key.symm

end ReciprocityTheory.ChartRestriction.DS
end
end
