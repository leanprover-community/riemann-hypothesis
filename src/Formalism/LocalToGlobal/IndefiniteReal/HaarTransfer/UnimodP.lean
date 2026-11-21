import Mathlib

section
namespace Formalism.IndefR.Leaf

open MeasureTheory

def HaarRightInvProd : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂],
    (∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ μ : Measure G₂, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → μ.IsMulRightInvariant

def HaarRightInvPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)]
    [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)],
    (∀ i, ∀ μ : Measure (G i), μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (∀ i, G i), μ.IsHaarMeasure → μ.IsMulRightInvariant

def HaarRightInvTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (_e : G ≃ₜ* H),
    (∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ ν : Measure H, ν.IsHaarMeasure → ν.IsMulRightInvariant

end Formalism.IndefR.Leaf
end

section
namespace Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory

theorem prodStatement_holds : HaarRightInvProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ μ hμ
  have : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  have : (Measure.haar : Measure G₂).IsMulRightInvariant := h₂ _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂))]
  infer_instance

theorem piStatement_holds : HaarRightInvPi := by
  intro ι _ G _ _ _ _ _ _ _ _ h μ hμ
  have : ∀ i, (Measure.haar : Measure (G i)).IsMulRightInvariant := fun i => h i _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ (Measure.pi fun i => (Measure.haar : Measure (G i)))]
  infer_instance

theorem transferStatement_holds : HaarRightInvTransfer := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ e h ν hν
  have hμ : (ν.map e.symm).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν e.symm
  have hr : (ν.map e.symm).IsMulRightInvariant := h _ hμ
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hν' : ν = (ν.map e.symm).map e := by
    rw [Measure.map_map he hes]
    have : (e : G → H) ∘ e.symm = id := funext fun x => e.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  rw [hν', Measure.map_map (measurable_mul_const g) he]
  have hc : (fun x => x * g) ∘ (e : G → H) = (e : G → H) ∘ (fun x => x * e.symm g) := by
    funext x; simp [map_mul]
  rw [hc, ← Measure.map_map he (measurable_mul_const _), hr.map_mul_right_eq_self (e.symm g)]

end Formalism.IndefR.Leaf.Proofs
end
