import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Metric
open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

def vecL (z : (Σ _ : Unit, Fin 2) → ℂ) : Fin 2 → ℂ := fun i => z ⟨(), i⟩

def projL (z : (Σ _ : Unit, Fin 2) → ℂ) : CP 1 :=
  if h : vecL z ≠ 0 then Projectivization.mk ℂ (vecL z) h else CP.chartInv 0 0

theorem vecL_ne_zero {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ∈ mcPts (mCoordIdeal yLine)) : vecL z ≠ 0 := by
  obtain ⟨i, hi⟩ := mem_mcPts_line.1 hz
  exact fun h => hi (congrFun h i)

theorem lineSections (x : CP 1) : ∃ U : Set (CP 1), IsOpen U ∧ x ∈ U ∧ ∃ s : CP 1 → (Σ _ : Unit, Fin 2) → ℂ,
    (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal yLine) ∧ projL (s y) = y) ∧
      ∀ p, cpAtlas.HoloOn U fun y => s y p := by
  refine ⟨CP.chartDomain (CP.chartIndex x), CP.isOpen_chartDomain _, CP.mem_chartDomain_chartIndex x,
    fun y p => CP.chartVec (CP.chartIndex x) (CP.chartCoord (CP.chartIndex x) y) p.2, fun y hy => ?_, fun p => ?_⟩
  · have hne := CP.chartVec_ne_zero (CP.chartIndex x) (CP.chartCoord (CP.chartIndex x) y)
    refine ⟨mem_mcPts_line.2 ⟨CP.chartIndex x, by simp⟩, ?_⟩
    unfold projL
    split_ifs with h
    · exact CP.chartInv_chartCoord _ hy
    · exact absurd hne h
  · intro j w hw
    have hw2 : CP.chartVec j w (CP.chartIndex x) ≠ 0 := hw.2
    exact (analyticAt_chartVec_apply (CP.chartIndex x) p.2 _).comp
      (analyticOnNhd_transition j (CP.chartIndex x) w hw2)

def lineModel : CxModel (mCoordIdeal yLine) 1 where
  Xc := CP 1
  atlas := cpAtlas
  proj := projL
  surj x := by
    induction x using Projectivization.ind with
    | h v hv =>
      refine ⟨fun p => v p.2, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        exact mem_mcPts_line.2 ⟨i, hi⟩
      · unfold projL
        split_ifs with h
        · rfl
        · exact absurd hv h
  fibre z hz z' hz' := by
    unfold projL
    rw [dif_pos (vecL_ne_zero hz), dif_pos (vecL_ne_zero hz'), Projectivization.mk_eq_mk_iff]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨fun _ => (a⁻¹ : ℂˣ), fun _ => Units.ne_zero _, ?_⟩
      funext p
      obtain ⟨⟨⟩, i⟩ := p
      have := congrFun ha i
      simp only [vecL, Pi.smul_apply, Units.smul_def, smul_eq_mul] at this
      simp only [torusSmul]
      rw [← this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨Units.mk0 (c ())⁻¹ (inv_ne_zero (hc ())), ?_⟩
      funext i
      simp [vecL, torusSmul, Units.smul_mk0, inv_mul_cancel_left₀ (hc ())]
  cont := by
    refine continuousOn_iff_continuous_restrict.2 ?_
    have hc : Continuous fun z : mcPts (mCoordIdeal yLine) =>
        Projectivization.mk' ℂ (⟨vecL z.1, vecL_ne_zero z.2⟩ : {v : Fin 2 → ℂ // v ≠ 0}) :=
      GroundTheory.Heights₂.Heights.ProjTopology.continuous_mk'.comp (Continuous.subtype_mk
        (f := fun z : mcPts (mCoordIdeal yLine) => vecL z.1) (by
          show Continuous fun z : mcPts (mCoordIdeal yLine) => fun i : Fin 2 => z.1 ⟨(), i⟩
          exact continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val) _)
    convert hc using 1
    funext z
    show projL z.1 = _
    unfold projL
    rw [dif_pos (vecL_ne_zero z.2)]
    rfl
  sections := lineSections

def refOne : HermLine (PBlk 2) := HermLine.ofWeight (fun _ => 0) fun _ _ _ => rfl

theorem refOne_h (z : (Σ _ : Unit, Fin 2) → ℂ) : refOne.h z = 1 := by simp [refOne, HermLine.ofWeight]

theorem refOne_smooth : IsSmoothHerm refOne := by
  have : refOne.h = fun _ => 1 := funext refOne_h
  unfold IsSmoothHerm
  rw [this]
  exact contDiffOn_const

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem th_ref_line (x y : CP 1) : ∃ U : Set (CP 1), IsOpen U ∧ y ∈ U ∧ U ⊆ Set.univ ∧
    ∃ s : CP 1 → (Σ _ : Unit, Fin 2) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal yLine) ∧ projL (s y') = y') ∧
      (∀ p, cpAtlas.HoloOn U fun y' => s y' p) ∧ ∃ G : CP 1 → ℂ, cpAtlas.HoloOn U G ∧
        ∀ y' ∈ U, (0 : ℝ) - Real.log (refOne.h (s y')) = (G y').re := by
  obtain ⟨U, hU, hy, s, hs, hh⟩ := lineSections y
  exact ⟨U, hU, hy, Set.subset_univ _, s, hs, hh, fun _ => 0, holoOn_zero' _ _, fun y' _ => by simp [refOne_h]⟩

def lineReg : LogLogRegularisationSetting lineModel (lineData II hII).Xo (muLine (lineHodge II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  R := cpReg
  th_ref x y _ := th_ref_line x y
  Yo_sub x _ := by
    obtain ⟨z, hz, hzx⟩ := lineModel.surj x
    exact ⟨z, ⟨⟨hz, fun h => absurd h (Set.notMem_empty _)⟩, hz⟩, hzx⟩
  ph_eq z hz _ := by
    show (0 : ℝ) = _
    rw [muLine_h (mem_mcPts_line.1 hz.2), refOne_h, Real.log_one, sub_zero]
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  K _ := 0
  e1 t := t
  e1_ge _ _ := le_rfl

def lineBReg : BoundedRegularisationSetting lineModel (lineData II hII).Xo
    (lineHodge II hII).aMu (cuspCorrected (lineHodge II hII) (gaussCusp II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  B := cpBounded
  th_ref x y _ := th_ref_line x y
  ph_eq z hz := by
    show (0 : ℝ) = _
    rw [cuspCorrected, phMu_line (mem_mcPts_line.1 hz.2), cuspWeight_gauss, refOne_h, Real.log_one]
    ring
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  e1 t := t
  e1_ge _ _ := le_rfl

theorem cpBounded_phReg (ρ : ReciprocityTheory.AnForm.A.Mollifier 1) (t : ℝ) (j : Fin cpBounded.N) (x : CP 1) :
    cpBounded.phReg ρ t j x = 0 := by
  simp [BoundedPshData.phReg, BoundedPshData.smoothed, BoundedPshData.u,
    GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, ReciprocityTheory.AnForm.A.molli, cpBounded, cpCharts]

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Ties

variable {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}

structure LogLogRegularisationSetting.IsTied {A : HermLine ι} (S : LogLogRegularisationSetting M Xo A) : Prop where
  e1_tendsto_zero : Tendsto S.e1 (𝓝[>] 0) (𝓝 0)
  K_tendsto : Tendsto S.K (𝓝[>] 0) atTop
  K_ge : ∀ᶠ t in 𝓝[>] 0, S.R.Clog * Real.log (Real.log t⁻¹) ≤ S.K t
  compare : ∀ᶠ t in 𝓝[>] 0, ∀ j k : Fin S.R.N, ∀ x ∈ S.R.mid j ∩ S.R.mid k,
    |S.R.phReg S.ρ (S.K t) t j x - S.R.phReg S.ρ (S.K t) t k x| ≤ S.e1 t

structure BoundedRegularisationSetting.IsTied {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ} (S : BoundedRegularisationSetting M Xo a w) : Prop where
  e1_tendsto_zero : Tendsto S.e1 (𝓝[>] 0) (𝓝 0)
  compare : ∀ᶠ t in 𝓝[>] 0, ∀ j k : Fin S.B.N, ∀ x ∈ S.B.mid j ∩ S.B.mid k,
    |S.B.phReg S.ρ t j x - S.B.phReg S.ρ t k x| ≤ S.e1 t

end Ties

open Classical in

def smoothRepConj (P : Ideal (MRing ι)) (A : HermLine ι) : HermLine ι :=
  if h : ∃ A' : HermLine ι, A'.a = A.a ∧ IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ ∀ z ∈ mcPts P, A'.h z = A.h z then
    h.choose
  else smoothRep P A

theorem smoothRepConj_h {P : Ideal (MRing ι)} (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    (smoothRepConj P A).h z = A.h z := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.2.2.2 z hz
  · exact smoothRep_h A hz

theorem smoothRepConj_a (P : Ideal (MRing ι)) (A : HermLine ι) : (smoothRepConj P A).a = A.a := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.1
  · exact smoothRep_a P A

theorem smoothRepConj_conj {P : Ideal (MRing ι)} (A : HermLine ι)
    (h : ∃ A' : HermLine ι, A'.a = A.a ∧ IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ ∀ z ∈ mcPts P, A'.h z = A.h z) :
    IsConjInvariantH (smoothRepConj P A) := by
  classical
  unfold smoothRepConj
  rw [dif_pos h]
  exact h.choose_spec.2.2.1

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

section Numbers

variable (H : HodgeData D)

def cuspCorr {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu H z + Cd.cuspWeight z / 2

variable {w : ((Σ k, ι k) → ℂ) → ℝ}

def MUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) : HermLine ι :=
  smoothRepConj (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg H B + (p : ℤ) • D.a') fun z =>
      (S.ref.h z * Real.exp (S.bregWeight t' (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)

def topMUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => MUc H S B p q t') / (q : ℝ) ^ (D.n + 1)

def geomDegMUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) : ℝ :=
  geomDeg (mCoordIdeal D.y) (MUc H S B p q t') D.n / (q : ℝ) ^ D.n

def htMUc {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t' : ℝ) (W : Ideal (MRing ι)) : ℝ :=
  II K ι W 1 ![MUc H S B p q t'] / ((q : ℝ) * degC W)

end Numbers

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem cpReg_trunc_of_nonneg {K : ℝ} (hK : 0 ≤ K) (j : Fin cpReg.N) : cpReg.trunc K j = fun _ => 0 := by
  funext y
  have hc : (fun y => max (cpReg.u j y) (-K)) = fun _ => (0 : ℝ) :=
    funext fun y => by
      simp only [RegChartData.u, GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, cpReg, cpCharts]
      simp [hK]
  unfold RegChartData.trunc ReciprocityTheory.AnForm.A.limsupExt
  rw [hc]
  split_ifs
  · exact limsup_zero_real _
  · rfl

theorem cpReg_phReg_of_nonneg (ρ : ReciprocityTheory.AnForm.A.Mollifier 1) {K : ℝ} (hK : 0 ≤ K) (t : ℝ) (j : Fin cpReg.N)
    (x : CP 1) : cpReg.phReg ρ K t j x = 0 := by
  simp only [RegChartData.phReg, RegChartData.smoothed, ReciprocityTheory.AnForm.A.molli]
  rw [cpReg_trunc_of_nonneg hK]
  simp [cpReg, cpCharts]

def lineRegT : LogLogRegularisationSetting lineModel (lineData II hII).Xo (muLine (lineHodge II hII)) :=
  { lineReg II hII with K := fun t => t⁻¹ }

theorem lineRegT_tied : (lineRegT II hII).IsTied where
  e1_tendsto_zero := tendsto_id.mono_left nhdsWithin_le_nhds
  K_tendsto := tendsto_inv_nhdsGT_zero
  K_ge := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    show cpReg.Clog * Real.log (Real.log t⁻¹) ≤ t⁻¹
    have : cpReg.Clog = 0 := rfl
    rw [this, zero_mul]
    exact inv_nonneg.2 (le_of_lt ht)
  compare := by
    filter_upwards [self_mem_nhdsWithin] with t ht j k x _
    have h0 : ∀ (j' : Fin (lineRegT II hII).R.N) (x' : lineModel.Xc),
        (lineRegT II hII).R.phReg (lineRegT II hII).ρ ((lineRegT II hII).K t) t j' x' = 0 :=
      fun j' x' => cpReg_phReg_of_nonneg _ (inv_nonneg.2 (le_of_lt ht)) t j' x'
    rw [h0, h0, sub_zero, abs_zero]
    exact le_of_lt ht

def lineBRegC : BoundedRegularisationSetting lineModel (lineData II hII).Xo
    (lineHodge II hII).aMu (cuspCorr (lineHodge II hII) (gaussCusp II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  B := cpBounded
  th_ref x y _ := th_ref_line x y
  ph_eq z hz := by
    show (0 : ℝ) = _
    rw [cuspCorr, phMu_line (mem_mcPts_line.1 hz.2), cuspWeight_gauss, refOne_h, Real.log_one]
    ring
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  e1 t := t
  e1_ge _ _ := le_rfl

theorem lineBRegC_tied : (lineBRegC II hII).IsTied where
  e1_tendsto_zero := tendsto_id.mono_left nhdsWithin_le_nhds
  compare := by
    filter_upwards [self_mem_nhdsWithin] with t ht j k x _
    have h0 : ∀ (j' : Fin (lineBRegC II hII).B.N) (x' : lineModel.Xc),
        (lineBRegC II hII).B.phReg (lineBRegC II hII).ρ t j' x' = 0 :=
      fun j' x' => cpBounded_phReg _ t j' x'
    rw [h0, h0, sub_zero, abs_zero]
    exact le_of_lt ht

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
