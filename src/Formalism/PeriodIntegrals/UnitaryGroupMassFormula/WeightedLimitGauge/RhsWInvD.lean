import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvR

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  let _ := TopologicalSpace.metrizableSpaceMetric Y
  have hemb : IsEmbedding ((↑) : Y → UniformSpace.Completion Y) :=
    (UniformSpace.Completion.isUniformEmbedding_coe Y).isEmbedding
  have hdense : DenseRange ((↑) : Y → UniformSpace.Completion Y) :=
    UniformSpace.Completion.denseRange_coe
  have hopen : IsOpen (range ((↑) : Y → UniformSpace.Completion Y)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, rfl⟩
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨V, hVK, hVo, hyV⟩ := mem_nhds_iff.1 hKy
    obtain ⟨U, hUo, hUV⟩ := hemb.isInducing.isOpen_iff.1 hVo
    refine ⟨U, ?_, hUo, ?_⟩
    · have hcl : IsClosed (((↑) : Y → UniformSpace.Completion Y) '' K) :=
        (hK.image hemb.continuous).isClosed
      calc U ⊆ closure (U ∩ range ((↑) : Y → UniformSpace.Completion Y)) :=
            hdense.open_subset_closure_inter hUo
        _ ⊆ closure (((↑) : Y → UniformSpace.Completion Y) '' K) := by
            apply closure_mono
            rintro _ ⟨hz, ⟨z, rfl⟩⟩
            refine ⟨z, hVK ?_, rfl⟩
            rw [← hUV]
            exact hz
        _ = ((↑) : Y → UniformSpace.Completion Y) '' K := hcl.closure_eq
        _ ⊆ range ((↑) : Y → UniformSpace.Completion Y) := image_subset_range _ _
    · show y ∈ ((↑) : Y → UniformSpace.Completion Y) ⁻¹' U
      rw [hUV]
      exact hyV
  have : PolishSpace (range ((↑) : Y → UniformSpace.Completion Y)) := hopen.polishSpace
  exact hemb.toHomeomorph.isClosedEmbedding.polishSpace

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by
  have hc : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
    continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
  exact (hf.comp hc.measurable).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using this

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) ∘ Quotient.mk'') =
      fun g => ∫⁻ h, f (g * (h : G)) ∂ν := by
    funext g
    exact avg_out H ν f g
  rw [this]
  exact meas_avg H ν hf

theorem lint_eq (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] [IsFiniteMeasure ν]
    (μ : Measure G) [SFinite μ] (hr : ∀ k : H, μ.map (· * (k : G)) = μ) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ν univ * ∫⁻ g, f g ∂μ =
      ∫⁻ q, (∫⁻ h, f (q.out * (h : G)) ∂ν) ∂(μ.map (QuotientGroup.mk : G → G ⧸ H)) := by
  rw [lintegral_map (meas_avg_q H ν hf) measurable_quotient_mk'']
  have e1 : ∀ g : G, ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := avg_out H ν f
  rw [lintegral_congr e1]
  have hmeas2 : AEMeasurable (Function.uncurry fun (g : G) (h : H) => f (g * (h : G))) (μ.prod ν) := by
    have hc2 : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
      continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
    exact (hf.comp hc2.measurable).aemeasurable
  rw [lintegral_lintegral_swap hmeas2]
  have : ∀ h : H, ∫⁻ g, f (g * (h : G)) ∂μ = ∫⁻ g, f g ∂μ := fun h => by
    rw [← lintegral_map hf (measurable_mul_const (h : G)), hr h]
  rw [lintegral_congr this, lintegral_const, mul_comm]

variable {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

def iotaQ (H : Subgroup G) (p : G → X) (q : G ⧸ H) : X := p q.out

theorem desc_uniq (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsMulLeftInvariant]
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (p : G → X) (hp : Continuous p)
    (hpH : ∀ g g' : G, p g = p g' ↔ g⁻¹ * g' ∈ H) (μ₁ μ₂ : Measure G) [SFinite μ₁] [SFinite μ₂]
    (h₁ : ∀ k : H, μ₁.map (· * (k : G)) = μ₁) (h₂ : ∀ k : H, μ₂.map (· * (k : G)) = μ₂)
    (hm : μ₁.map p = μ₂.map p) : μ₁ = μ₂ := by
  classical
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hfin⟩
  haveI : IsClosed (H : Set G) := hH
  haveI : PolishSpace G := polish_of_lcsc G
  haveI : PolishSpace (G ⧸ H) := polish_of_lcsc _
  haveI : BorelSpace (G ⧸ H) := CosetSpace.borelSpace
  have hmk : ∀ g : G, iotaQ H p (g : G ⧸ H) = p g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
    show p (g : G ⧸ H).out = p g
    rw [hk]
    refine ((hpH g (g * k)).2 ?_).symm
    rw [inv_mul_cancel_left]
    exact k.2
  have hcomp : (iotaQ H p ∘ (QuotientGroup.mk : G → G ⧸ H)) = p := funext hmk
  have hιc : Continuous (iotaQ H p) := by
    rw [(QuotientGroup.isQuotientMap_mk H).continuous_iff, hcomp]
    exact hp
  have hinj : Function.Injective (iotaQ H p) := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact (hpH _ _).1 h
  have hemb : MeasurableEmbedding (iotaQ H p) := hιc.measurableEmbedding hinj
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ H) := measurable_quotient_mk''
  have hq : μ₁.map (QuotientGroup.mk : G → G ⧸ H) = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := by
    calc μ₁.map (QuotientGroup.mk : G → G ⧸ H)
        = ((μ₁.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) :=
          (hemb.comap_map _).symm
      _ = (μ₁.map p).comap (iotaQ H p) := by rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = (μ₂.map p).comap (iotaQ H p) := by rw [hm]
      _ = ((μ₂.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) := by
          rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := hemb.comap_map _
  ext S hS
  have hf : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hS
  have e1 := lint_eq H ν μ₁ h₁ _ hf
  have e2 := lint_eq H ν μ₂ h₂ _ hf
  rw [hq, ← e2, lintegral_indicator_one hS, lintegral_indicator_one hS] at e1
  exact (ENNReal.mul_right_inj h0 hfin).1 e1

end Abstract

end PI.RhsWLim.W.RI
end
end

section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

instance : T2Space (HU.Gp k r) := inferInstanceAs (T2Space {x : Mt k r // x ∈ HU.amb k r})

instance : LocallyCompactSpace (HU.Gp k r) :=
  show LocallyCompactSpace {x : Mt k r // x ∈ HU.amb k r} from
    HU.amb_closed.isClosedEmbedding_subtypeVal.locallyCompactSpace

def stabH (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Subgroup (HU.Gp k r) where
  carrier := {g | Matrix.of (HU.inc g) *ᵥ z' = z'}
  mul_mem' {a b} ha hb := by
    show (Matrix.of (HU.inc a) * Matrix.of (HU.inc b) : Mat k r) *ᵥ z' = z'
    rw [← Matrix.mulVec_mulVec]
    rw [show Matrix.of (HU.inc b) *ᵥ z' = z' from hb]
    exact ha
  one_mem' := by
    show (1 : Mat k r) *ᵥ z' = z'
    exact Matrix.one_mulVec z'
  inv_mem' {a} ha := by
    show (Matrix.of (HU.inc a) : Mat k r)⁻¹ *ᵥ z' = z'
    exact inv_fix (HU.uwb_unit (HU.inc_mem a)) ha

theorem continuous_orbV_inc (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) := (orbV_cont z').comp HU.inc_cont

theorem stabH_closed (z' : Fin (2 * r + k + 1) → ℂ) : IsClosed ((stabH k r z' : Subgroup (HU.Gp k r)) : Set (HU.Gp k r)) :=
  isClosed_eq (continuous_orbV_inc z') continuous_const

def jH (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Mt k r := HU.inc h.1

theorem jH_memb (z' : Fin (2 * r + k + 1) → ℂ) : MeasurableEmbedding (jH (k := k) (r := r) z') :=
  HU.inc_memb.comp (MeasurableEmbedding.subtype_coe (stabH_closed z').measurableSet)

theorem jH_mem (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Matrix.of (jH z' h) ∈ UWset k r z' :=
  ⟨(HU.inc_mem h.1).1, (HU.inc_mem h.1).2, h.2⟩

theorem range_jH (z' : Fin (2 * r + k + 1) → ℂ) :
    range (jH (k := k) (r := r) z') = {x | Matrix.of x ∈ UWset k r z'} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact jH_mem z' h
  · intro hx
    exact ⟨⟨⟨x, ⟨hx.1, hx.2.1⟩⟩, hx.2.2⟩, rfl⟩

theorem map_jH {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).map (jH z') = μW' := by
  rw [(jH_memb z').map_comap, range_jH]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hW.2.2.1)

theorem nuH_left {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable (fun h : stabH k r z' => g * h) := (continuous_const_mul g).measurable
  have e : (jH z' ∘ fun h : stabH k r z' => g * h) = lmulM (Matrix.of (jH z' g)) ∘ jH z' := funext fun h => rfl
  calc (μW'.comap (jH z')).map (fun h => g * h)
      = (((μW'.comap (jH z')).map (fun h => g * h)).map (jH z')).comap (jH z') := ((jH_memb z').comap_map _).symm
    _ = (((μW'.comap (jH z')).map (jH z')).map (lmulM (Matrix.of (jH z' g)))).comap (jH z') := by
        rw [Measure.map_map (jH_memb z').measurable hg, e,
          ← Measure.map_map (HU.lmulM_cont _).measurable (jH_memb z').measurable]
    _ = ((μW'.comap (jH z')).map (jH z')).comap (jH z') := by
        rw [map_jH hW, hW.2.2.2 _ (jH_mem z' g)]
    _ = μW'.comap (jH z') := (jH_memb z').comap_map _

theorem pull_right {z' : Fin (2 * r + k + 1) → ℂ} (ν : Measure (Mt k r))
    (hc : ν {x | Matrix.of x ∉ UWb k r} = 0) (hr : ∀ b ∈ UWset k r z', ν.map (rmulM b) = ν)
    (g : stabH k r z') : (HU.pull ν).map (· * (g : HU.Gp k r)) = HU.pull ν := by
  have hg : Measurable (fun h : HU.Gp k r => h * (g : HU.Gp k r)) := (continuous_mul_const _).measurable
  have e : (HU.inc ∘ fun h : HU.Gp k r => h * (g : HU.Gp k r)) = rmulM (Matrix.of (jH z' g)) ∘ HU.inc :=
    funext fun h => rfl
  calc (HU.pull ν).map (· * (g : HU.Gp k r))
      = (((HU.pull ν).map (· * (g : HU.Gp k r))).map HU.inc).comap HU.inc := (HU.inc_memb.comap_map _).symm
    _ = (((HU.pull ν).map HU.inc).map (rmulM (Matrix.of (jH z' g)))).comap HU.inc := by
        rw [Measure.map_map HU.inc_memb.measurable hg, e,
          ← Measure.map_map (rmulM_cont _).measurable HU.inc_memb.measurable]
    _ = ((HU.pull ν).map HU.inc).comap HU.inc := by
        rw [HU.map_pull ν hc, hr _ (jH_mem z' g)]
    _ = HU.pull ν := HU.inc_memb.comap_map _

theorem orb_fib (z' : Fin (2 * r + k + 1) → ℂ) (g g' : HU.Gp k r) :
    orbV k r z' (HU.inc g) = orbV k r z' (HU.inc g') ↔ g⁻¹ * g' ∈ stabH k r z' := by
  have hu := HU.uwb_unit (HU.inc_mem g)
  show (Matrix.of (HU.inc g) : Mat k r) *ᵥ z' = Matrix.of (HU.inc g') *ᵥ z' ↔
    ((Matrix.of (HU.inc g) : Mat k r)⁻¹ * Matrix.of (HU.inc g')) *ᵥ z' = z'
  constructor
  · intro h
    rw [← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem descUniq : DescUniq := by
  intro k r z' μW' hW hfin ν₁ ν₂ hσ₁ hσ₂ hc₁ hc₂ hr₁ hr₂ hm
  have : SigmaFinite μW' := hW.1
  have hl := nuH_left hW
  have hmass : (μW'.comap (jH z')) univ = μW' univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z').measurable MeasurableSet.univ, preimage_univ]
  have h0 : (μW'.comap (jH z')) univ ≠ 0 := by
    rw [hmass]
    exact fun h => hW.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hf : (μW'.comap (jH z')) univ ≠ ⊤ := by rw [hmass]; exact hfin
  have : SigmaFinite (HU.pull ν₁) := HU.pull_sigmaFinite ν₁
  have : SigmaFinite (HU.pull ν₂) := HU.pull_sigmaFinite ν₂
  have hpm : ∀ ν : Measure (Mt k r), ν {x | Matrix.of x ∉ UWb k r} = 0 →
      (HU.pull ν).map (fun g => orbV k r z' (HU.inc g)) = ν.map (orbV k r z') := by
    intro ν hc
    have e : (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) = orbV k r z' ∘ HU.inc := rfl
    rw [e, ← Measure.map_map (orbV_cont z').measurable HU.inc_memb.measurable, HU.map_pull ν hc]
  have key := desc_uniq (stabH k r z') (stabH_closed z') (μW'.comap (jH z')) h0 hf
    (fun g => orbV k r z' (HU.inc g)) (continuous_orbV_inc z') (orb_fib z') (HU.pull ν₁) (HU.pull ν₂)
    (pull_right ν₁ hc₁ hr₁) (pull_right ν₂ hc₂ hr₂) (by rw [hpm ν₁ hc₁, hpm ν₂ hc₂, hm])
  rw [← HU.map_pull ν₁ hc₁, ← HU.map_pull ν₂ hc₂, key]

theorem rhsWInv_of_orb (hO : OrbInv) : RhsWInv := rhsWInv_of descUniq rInvNu hO

end PI.RhsWLim.W.RI
end
end
