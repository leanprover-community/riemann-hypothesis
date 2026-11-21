import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionCountCuspOfTrivialIdempotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain
import Mathlib

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace

section Cont

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace H] in
theorem rrc_inner (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (a b : H) : ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(π g : H →ₗ[ℂ] H), hn g⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace H] in
theorem rrc_bound (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (v u : H) : ‖⟪π g v, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ := by
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [hn]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H] [Group G] in
theorem rrc_aesm (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) (v u : H) :
    AEStronglyMeasurable (fun g => ⟪π g v, u⟫_ℂ) μ := by
  have h := Complex.continuous_conj.comp_aestronglyMeasurable (hm u v)
  refine h.congr (Eventually.of_forall fun g => ?_)
  exact inner_conj_symm _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H] in
theorem rrc_intOn (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v u : H) : IntegrableOn (fun g => ⟪π g v, u⟫_ℂ) k μ :=
  IntegrableOn.of_bound hk (rrc_aesm hm v u).restrict (‖v‖ * ‖u‖) (Eventually.of_forall fun g => rrc_bound hn g v u)

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure] in

theorem rrc_exists_vec (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v : H) : ∃ w : H, ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ := by
  have hint := fun u => rrc_intOn hn hm hk v u
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun u => ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul _ _ }
  have hb : ∀ u, ‖L u‖ ≤ (‖v‖ * μ.real k) * ‖u‖ := fun u => by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) hk (fun g _ => rrc_bound hn g v u)
    calc ‖L u‖ ≤ ‖v‖ * ‖u‖ * μ.real k := this
      _ = (‖v‖ * μ.real k) * ‖u‖ := by ring
  refine ⟨(InnerProductSpace.toDual ℂ H).symm (L.mkContinuous _ hb), fun u => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [CompleteSpace H] in
theorem rrc_translate (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    {k : Set G} {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) (u : H) :
    ⟪π h w, u⟫_ℂ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := by
  have e1 : π h (π h⁻¹ u) = u := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
  have e2 : ∀ g, ⟪π g v, π h⁻¹ u⟫_ℂ = ⟪π (h * g) v, u⟫_ℂ := fun g => by
    rw [← rrc_inner hn h, e1, hmul]; rfl
  have e3 : (fun g => h * g) ⁻¹' (h • k) = k := by
    ext g; simp [Set.mem_smul_set_iff_inv_smul_mem]
  have e4 := (measurePreserving_mul_left μ h).setIntegral_preimage_emb (measurableEmbedding_mulLeft h)
    (fun g => ⟪π g v, u⟫_ℂ) (h • k)
  rw [e3] at e4
  calc ⟪π h w, u⟫_ℂ = ⟪π h w, π h (π h⁻¹ u)⟫_ℂ := by rw [e1]
    _ = ⟪w, π h⁻¹ u⟫_ℂ := rrc_inner hn h _ _
    _ = ∫ g in k, ⟪π g v, π h⁻¹ u⟫_ℂ ∂μ := hw _
    _ = ∫ g in k, ⟪π (h * g) v, u⟫_ℂ ∂μ := by simp only [e2]
    _ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := e4

omit [LocallyCompactSpace G] [SecondCountableTopology G] [CompleteSpace H] in
theorem rrc_norm_le (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : IsCompact k) {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) :
    ‖π h w - w‖ ≤ ‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
  have hkm : MeasurableSet k := hk.measurableSet
  have hk' : IsCompact (h • k) := hk.smul h
  have hkm' : MeasurableSet (h • k) := hk'.measurableSet
  have key : ∀ u, ‖⟪π h w - w, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
    intro u
    rw [inner_sub_left, rrc_translate hmul hone hn hw h u, hw u]
    have a1 := integral_inter_add_sdiff (f := fun g => ⟪π g v, u⟫_ℂ) hkm (rrc_intOn hn hm hk'.measure_lt_top v u)
    have a2 := integral_inter_add_sdiff (f := fun g => ⟪π g v, u⟫_ℂ) hkm' (rrc_intOn hn hm hk.measure_lt_top v u)
    rw [inter_comm] at a2
    rw [← a1, ← a2, add_sub_add_left_eq_sub]
    have b1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := h • k \ k)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hk'.measure_lt_top) (fun g _ => rrc_bound hn g v u)
    have b2 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := k \ h • k)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hk.measure_lt_top) (fun g _ => rrc_bound hn g v u)
    calc _ ≤ ‖∫ g in h • k \ k, ⟪π g v, u⟫_ℂ ∂μ‖ + ‖∫ g in k \ h • k, ⟪π g v, u⟫_ℂ ∂μ‖ := norm_sub_le _ _
      _ ≤ ‖v‖ * ‖u‖ * μ.real (h • k \ k) + ‖v‖ * ‖u‖ * μ.real (k \ h • k) := add_le_add b1 b2
      _ = _ := by ring
  have h2 := key (π h w - w)
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ‖((‖π h w - w‖ : ℝ) : ℂ) ^ 2‖ = ‖π h w - w‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, norm_norm]
  have h2' : ‖π h w - w‖ ^ 2 ≤ ‖v‖ * ‖π h w - w‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
    rw [← h3]; exact h2
  by_cases h0 : ‖π h w - w‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖π h w - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖π h w - w‖ * ‖π h w - w‖ ≤ ‖π h w - w‖ * (‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k))) := by
      calc _ = ‖π h w - w‖ ^ 2 := by ring
        _ ≤ _ := h2'
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos


def rrc_C (π : G → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {x | Tendsto (fun h => π h x) (𝓝 1) (𝓝 x)}
  add_mem' := fun {a b} ha hb => by
    have := Tendsto.add ha hb
    simpa only [mem_ofPred_eq, map_add] using this
  zero_mem' := by
    simp only [mem_ofPred_eq, map_zero]
    exact tendsto_const_nhds
  smul_mem' := fun c a ha => by
    have := Tendsto.const_smul ha c
    simpa only [mem_ofPred_eq, map_smul] using this



end Cont

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def RepInf (X : CData) : Prop := ∀ F : X.L2, Continuous fun g : X.I.Ginf => X.R (g, 1) F


end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma



end Formalism.MainNotions.LeviCoordinates

end
end
