import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyRecursion

section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MomOne

open PI.UpqRep

section L2

variable {X Ω : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_sq_eq (f : Ω → X) : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem memLp_of_lt_top {f : Ω → X} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≠ ⊤) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  rw [lintegral_sq_eq] at h
  exact lt_top_iff_ne_top.2 fun e => h (by rw [e]; simp)

theorem exists_linear_sq {V : Type} [AddCommGroup V] [Module ℂ V] (T : V → Ω → X)
    (hadd : ∀ v w, T (v + w) =ᵐ[μ] T v + T w) (hsm : ∀ (a : ℂ) v, T (a • v) =ᵐ[μ] a • T v)
    (hL : ∀ v, MemLp (T v) 2 μ) :
    ∃ F : V →ₗ[ℂ] Lp X 2 μ, ∀ v, ∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂μ = ENNReal.ofReal (‖F v‖ ^ 2) := by
  refine ⟨⟨⟨fun v => (hL v).toLp _, fun v w => ?_⟩, fun a v => ?_⟩, fun v => ?_⟩
  · rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (hadd v w)
  · simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (hsm a v)
  · show _ = ENNReal.ofReal (‖(hL v).toLp _‖ ^ 2)
    rw [Lp.norm_toLp, lintegral_sq_eq, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hL v).2.ne]

end L2

section core

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem proj_comm (hτ : IsURepOn (UJset ε) τ) (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (hM : IsKStableOn ε τ M) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (x : H) :
    M.starProjection (τ g x) = τ g (M.starProjection x) := by
  obtain ⟨⟨r1, r2⟩, r3, -⟩ := hτ
  have hg' := Kset_star ε hg
  have hgU := GlobalTheory.CayleyChoice.Kset_sub hg
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hM g hg _ (M.starProjection_apply_mem x)) ?_
  intro w hw
  have hs : τ g (τ (star g) w) = w := by
    have := r2 g hgU _ (GlobalTheory.CayleyChoice.Kset_sub hg')
    rw [Matrix.mem_unitaryGroup_iff.1 hg.1, r1] at this
    simpa using (congrArg (fun A : H →L[ℂ] H => A w) this).symm
  have hin := (LinearMap.norm_map_iff_inner_map_map ((τ g : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 (r3 g hgU)
    (x - M.starProjection x) (τ (star g) w)
  simp only [ContinuousLinearMap.coe_coe] at hin
  rw [← map_sub, ← hs, hin]
  exact Submodule.starProjection_inner_eq_zero x _ (hM _ hg' w hw)

theorem isWtOn_smul {Λ : Fin n → ℝ} {v : H} (hv : IsWtOn (Kset ε) τ Λ v) (a : ℂ) :
    IsWtOn (Kset ε) τ Λ (a • v) := by
  intro θ hθ
  rw [map_smul, hv θ hθ, smul_comm]

theorem norm_normalise {v : H} (hv : v ≠ 0) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
  rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

theorem form_le_of_highest (hτ : IsURepOn (UJset ε) τ) (Λ : Fin n → ℝ) (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hVs : IsKStableOn ε τ V) (hV : V ≤ sSup {S | IsKTypeOf ε τ Λ S}) (N : H → ℝ)
    (hpar : ∀ x ∈ V, ∀ y ∈ V, N (x + y) + N (x - y) = 2 * N x + 2 * N y)
    (hsm : ∀ (a : ℂ), ∀ x ∈ V, N (a • x) = ‖a‖ ^ 2 * N x) (hcont : Continuous fun v : V => N v)
    (hinv : ∀ g ∈ Kset ε, ∀ x ∈ V, N (τ g x) = N x) (C : ℝ)
    (hw : ∀ S : Submodule ℂ H, S ≤ V → IsKStableOn ε τ S →
      (∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Kset ε) τ μ v → CDom ε μ Λ) →
      ∀ v ∈ S, ‖v‖ = 1 → IsWtOn (Kset ε) τ Λ v → N v ≤ C) :
    ∀ w ∈ V, ‖w‖ = 1 → N w ≤ C := by
  intro w hwV hw1
  obtain ⟨v0, hv0, hmax⟩ := (isCompact_sphere (0 : V) 1).exists_isMaxOn
    ⟨⟨w, hwV⟩, by simpa using hw1⟩ hcont.continuousOn
  have hv1 : ‖(v0 : H)‖ = 1 := by simpa using hv0
  set c := N v0 with hc
  have hunit : ∀ x ∈ V, ‖x‖ = 1 → N x ≤ c := fun x hx h1 =>
    hmax (a := ⟨x, hx⟩) (by simpa using h1)
  have hN0 : N 0 = 0 := by simpa using hsm 0 0 V.zero_mem
  have hle : ∀ x ∈ V, N x ≤ c * ‖x‖ ^ 2 := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0, hN0]
    · have h1 := hunit _ (V.smul_mem _ hx) (norm_normalise h0)
      rw [hsm _ x hx, Complex.norm_real, norm_inv, norm_norm, inv_pow] at h1
      have hp : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 h0) 2
      rwa [inv_mul_le_iff₀ hp, mul_comm] at h1
  let M : Submodule ℂ H :=
    { carrier := {x | x ∈ V ∧ N x = c * ‖x‖ ^ 2}
      zero_mem' := ⟨V.zero_mem, by simp [hN0]⟩
      add_mem' := by
        rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
        refine ⟨V.add_mem hx hy, le_antisymm (hle _ (V.add_mem hx hy)) ?_⟩
        have h1 := hpar x hx y hy
        have h2 := hle _ (V.sub_mem hx hy)
        have h3 := parallelogram_law_with_norm ℂ x y
        have h4 : c * ‖x + y‖ ^ 2 + c * ‖x - y‖ ^ 2 = 2 * (c * ‖x‖ ^ 2) + 2 * (c * ‖y‖ ^ 2) := by
          simp only [sq] at h3 ⊢
          linear_combination c * h3
        linarith
      smul_mem' := by
        rintro a x ⟨hx, ex⟩
        refine ⟨V.smul_mem a hx, ?_⟩
        rw [hsm a x hx, ex, norm_smul]; ring }
  have hMV : M ≤ V := fun x hx => hx.1
  haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMV
  have hMs : IsKStableOn ε τ M := by
    rintro g hg x ⟨hx, ex⟩
    exact ⟨hVs g hg x hx, by rw [hinv g hg x hx, ex, hτ.2.1 g (GlobalTheory.CayleyChoice.Kset_sub hg)]⟩
  set P : H →ₗ[ℂ] H := (M.starProjection : H →ₗ[ℂ] H) with hP
  have hPc : ∀ g ∈ Kset ε, ∀ x, P (τ g x) = τ g (P x) := fun g hg x => proj_comm hτ M hMs hg x
  have hPM : ∀ x, P x ∈ M := fun x => M.starProjection_apply_mem x
  have hker : ∀ S : Submodule ℂ H, IsKStableOn ε τ S → IsKStableOn ε τ (S ⊓ LinearMap.ker P) := by
    rintro S hS g hg x ⟨hx, hx0⟩
    refine ⟨hS g hg x hx, ?_⟩
    have hx0' : P x = 0 := hx0
    show P (τ g x) = 0
    rw [hPc g hg, hx0', map_zero]
  have hex : ∃ S, IsKTypeOf ε τ Λ S ∧ S ⊓ LinearMap.ker P = ⊥ := by
    by_contra hne
    push Not at hne
    have h1 : sSup {S | IsKTypeOf ε τ Λ S} ≤ LinearMap.ker P := by
      refine sSup_le fun S hS => ?_
      have := (hS.2.2.1 _ inf_le_left (hker S hS.2.1)).resolve_left (hne S hS)
      rw [← this]; exact inf_le_right
    have h2 : P v0 = 0 := h1 (hV v0.2)
    have h3 : P v0 = v0 := Submodule.starProjection_eq_self_iff.2 ⟨v0.2, by rw [hv1]; simp [hc]⟩
    rw [h3] at h2
    rw [h2] at hv1
    simp at hv1
  obtain ⟨S, ⟨-, hSs, -, ⟨v, hvS, hv0', hvw⟩, hcd⟩, hinj⟩ := hex
  have hz : ∀ x ∈ S, P x = 0 → x = 0 := fun x hx h0 => by
    have : x ∈ S ⊓ LinearMap.ker P := ⟨hx, h0⟩
    rwa [hinj, Submodule.mem_bot] at this
  have hPv : P v ≠ 0 := fun h0 => hv0' (hz v hvS h0)
  have hmapM : S.map P ≤ M := by
    rintro _ ⟨x, -, rfl⟩; exact hPM x
  have hu : ((‖P v‖⁻¹ : ℝ) : ℂ) • P v ∈ S.map P := Submodule.smul_mem _ _ ⟨v, hvS, rfl⟩
  have key := hw (S.map P) (hmapM.trans hMV) ?_ ?_ _ hu (norm_normalise hPv) (isWtOn_smul ?_ _)
  · have e := (hmapM hu).2
    rw [norm_normalise hPv, one_pow, mul_one] at e
    rw [e] at key
    exact (hunit w hwV hw1).trans key
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨τ g x, hSs g hg x hx, hPc g hg x⟩
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hwt
    refine hcd μ x hx (by rintro rfl; simp at h0) fun θ hθ => ?_
    rw [← sub_eq_zero]
    refine hz _ (S.sub_mem (hSs _ hθ x hx) (S.smul_mem _ hx)) ?_
    rw [map_sub, map_smul, hPc _ hθ, hwt θ hθ, sub_self]
  · intro θ hθ
    rw [← hPc _ hθ, hvw θ hθ, map_smul]

theorem lintegral_le_of_highest {X Ω : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [MeasurableSpace Ω]
    {m : Measure Ω} (hτ : IsURepOn (UJset ε) τ) (Λ : Fin n → ℝ) (D : Submodule ℂ H)
    (hD : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε τ S → S ≤ D) (T : H → Ω → X)
    (hadd : ∀ v ∈ D, ∀ w ∈ D, T (v + w) =ᵐ[m] T v + T w) (hsm : ∀ (a : ℂ), ∀ v ∈ D, T (a • v) =ᵐ[m] a • T v)
    (hme : ∀ v ∈ D, AEStronglyMeasurable (T v) m)
    (hinv : ∀ g ∈ Kset ε, ∀ v ∈ D, ∫⁻ x, ENNReal.ofReal (‖T (τ g v) x‖ ^ 2) ∂m =
      ∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂m) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε τ S →
      (∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Kset ε) τ μ v → CDom ε μ Λ) →
      ∀ v ∈ S, ‖v‖ = 1 → IsWtOn (Kset ε) τ Λ v → ∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂m ≤ ENNReal.ofReal C)
    (w : H) (hwL : w ∈ sSup {S | IsKTypeOf ε τ Λ S}) (hw1 : ‖w‖ = 1) :
    ∫⁻ x, ENNReal.ofReal (‖T w x‖ ^ 2) ∂m ≤ ENNReal.ofReal C := by
  let W : Submodule ℂ H :=
    { carrier := {x | x ∈ D ∧ MemLp (T x) 2 m}
      zero_mem' := ⟨D.zero_mem, by
        have := hsm 0 0 D.zero_mem
        rw [zero_smul, zero_smul] at this
        exact (memLp_congr_ae this).2 MemLp.zero⟩
      add_mem' := by
        rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
        exact ⟨D.add_mem hx hy, (memLp_congr_ae (hadd x hx y hy)).2 (ex.add ey)⟩
      smul_mem' := by
        rintro a x ⟨hx, ex⟩
        exact ⟨D.smul_mem a hx, (memLp_congr_ae (hsm a x hx)).2 (ex.const_smul a)⟩ }
  have hLW : sSup {S | IsKTypeOf ε τ Λ S} ≤ W := by
    refine sSup_le fun S hS => ?_
    obtain ⟨hfd, hSs, hirr, ⟨v, hvS, hv0, hvw⟩, hcd⟩ := hS
    have hSD := hD S hfd hSs
    have hst : IsKStableOn ε τ (S ⊓ W) := by
      rintro g hg x ⟨hx, hxD, hxL⟩
      have hgx := hSs g hg x hx
      refine ⟨hgx, hSD hgx, memLp_of_lt_top (hme _ (hSD hgx)) ?_⟩
      rw [hinv g hg x hxD, lintegral_sq_eq]
      exact ENNReal.pow_ne_top hxL.2.ne
    rcases hirr _ inf_le_left hst with e | e
    · exfalso
      have hu := S.smul_mem ((‖v‖⁻¹ : ℝ) : ℂ) hvS
      have : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ S ⊓ W := ⟨hu, hSD hu, memLp_of_lt_top (hme _ (hSD hu))
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (hw S hfd hSs hcd _ hu (norm_normalise hv0) (isWtOn_smul hvw _)))⟩
      rw [e, Submodule.mem_bot] at this
      have h1 := norm_normalise hv0
      rw [this] at h1
      simp at h1
    · rw [← e]; exact inf_le_right
  obtain ⟨V₀, ⟨hfd, hst⟩, hwV⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Kset ε) τ
    (F := {S | IsKTypeOf ε τ Λ S}) (fun S hS => ⟨hS.1, hS.2.1⟩) hwL
  set V : Submodule ℂ H := V₀ ⊓ sSup {S | IsKTypeOf ε τ Λ S} with hVdef
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (inf_le_left : V ≤ V₀)
  have hVs : IsKStableOn ε τ V := by
    rintro g hg x ⟨hx, hxL⟩
    refine ⟨hst g hg x hx, ?_⟩
    have : sSup {S | IsKTypeOf ε τ Λ S} ≤
        (sSup {S | IsKTypeOf ε τ Λ S} : Submodule ℂ H).comap ((τ g : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
      sSup_le fun S hS y hy => (le_sSup hS : S ≤ sSup {S | IsKTypeOf ε τ Λ S}) (hS.2.1 g hg y hy)
    exact this hxL
  have hVW : V ≤ W := inf_le_right.trans hLW
  obtain ⟨F, hF⟩ := exists_linear_sq (μ := m) (fun v : V => T v)
    (fun v w => hadd _ (hVW v.2).1 _ (hVW w.2).1) (fun a v => hsm a _ (hVW v.2).1) (fun v => (hVW v.2).2)
  set N : H → ℝ := fun v => (∫⁻ x, ENNReal.ofReal (‖T v x‖ ^ 2) ∂m).toReal with hN
  have hNF : ∀ (v : H) (hv : v ∈ V), N v = ‖F ⟨v, hv⟩‖ ^ 2 := fun v hv => by
    have := hF ⟨v, hv⟩
    simp only [hN]
    rw [this, ENNReal.toReal_ofReal (by positivity)]
  have key := form_le_of_highest hτ Λ V hVs inf_le_right N ?_ ?_ ?_ ?_ C ?_ w ⟨hwV, hwL⟩ hw1
  · have hwV' : w ∈ V := ⟨hwV, hwL⟩
    rw [hNF w hwV'] at key
    exact (hF ⟨w, hwV'⟩).trans_le (ENNReal.ofReal_le_ofReal key)
  · intro x hx y hy
    rw [hNF x hx, hNF y hy, hNF _ (V.add_mem hx hy), hNF _ (V.sub_mem hx hy)]
    have h3 := parallelogram_law_with_norm ℂ (F ⟨x, hx⟩) (F ⟨y, hy⟩)
    rw [← map_add, ← map_sub] at h3
    simp only [sq] at h3 ⊢
    exact h3.trans (by ring)
  · intro a x hx
    rw [hNF x hx, hNF _ (V.smul_mem a hx), ← mul_pow, ← norm_smul, ← map_smul]
    rfl
  · have : (fun v : V => N v) = fun v => ‖F v‖ ^ 2 := funext fun v => hNF v v.2
    rw [this]
    exact (F.continuous_of_finiteDimensional.norm).pow 2
  · intro g hg x hx
    simp only [hN]
    rw [hinv g hg x (hVW hx).1]
  · intro S hSV hSs hcd v hv h1 hwt
    exact ENNReal.toReal_le_of_le_ofReal hC (hw S (Submodule.finiteDimensional_of_le hSV) hSs hcd v hv h1 hwt)

end core

end GlobalTheory.MomOne
end
end

section
noncomputable section

namespace GlobalTheory.MomOne

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem single_moment_le (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (len : Fin (r + 1) → Ω → ℝ)
    (Ph : Ω → ℝ) (A Rr : ℝ) (hm : ∀ a, AEMeasurable (len a) ν) (hpos : ∀ a, ∀ᵐ x ∂ν, 0 < len a x)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (hmass : ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1) (hA : 0 ≤ A)
    (hR : 1 ≤ Rr)
    (h1 : ∀ q' ≤ (r + 1) * q, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q') * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q'))
    (h2 : ∀ a : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q') * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q'))) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (len a x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ q) := by
  choose l hlm hlp hle using fun a => GlobalTheory.MomentHolder.exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r q l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q hq)
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q hq)
      filter_upwards [hall] with x hx
      rw [hx, hx]) a
  rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0 _ ((hlm a).pow_const _), hsq] at hup
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hup.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hall] with x hx
    rw [hx]
  · rw [mul_pow, ← pow_mul Rr]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
    have := Nat.mul_le_mul_left (2 * q) (Nat.lt_succ_iff.1 a.isLt)
    calc 2 * q * a.val ≤ 2 * q * r := this
      _ = 2 * r * q := by ring

variable {k r : ℕ}

theorem lenA_mul_unitary (z : Fin (2 * r + k + 1) → ℂ) (x : Mx k r) {g : Mx k r}
    (hg : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lenA k r z (x * g) a = lenA k r z x a := by
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg
  have h2 : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hg
  have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv h1
  let L : EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    Matrix.toEuclideanLin (star g)
  have hL : ∀ v, WithLp.toLp 2 (star g *ᵥ v) = L (WithLp.toLp 2 v) := fun v => rfl
  have hiso : Isometry L := by
    refine AddMonoidHomClass.isometry_of_norm L ((LinearMap.norm_map_iff_inner_map_map L).2 fun v w => ?_)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    show (star g *ᵥ w.ofLp) ⬝ᵥ star (star g *ᵥ v.ofLp) = _
    rw [Matrix.star_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, star_star, h2, Matrix.vecMul_one, dotProduct_comm]
  unfold lenA
  simp only [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec, hL]
  rw [← Set.image_image L, ← Submodule.map_span, Submodule.map_coe, Metric.infDist_image hiso]

theorem lintegral_rmul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ)
    (hF : ContinuousOn F (GG k r)) (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, ENNReal.ofReal (F (Matrix.of x * g)) ∂νq = ∫⁻ x, ENNReal.ofReal (F (Matrix.of x)) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) A := hF
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hm.ennreal_ofReal (fun s hs x hx => by
    rw [hval x hx]
    exact congrArg ENNReal.ofReal
      ((hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx))) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => congrArg ENNReal.ofReal (hval x hx))))
  exact congrArg ENNReal.ofReal (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {Q g : Mx k r} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hg : g ∈ PI.UpqRep.Kset ε) :
    Q⁻¹ * g * Q ∈ GG k r ∧ Q⁻¹ * g * Q ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
  have q1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ.2
  have q2 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hQ.2
  have qi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hJ : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := GlobalTheory.CayleyChoice.Kset_sub hg
  have hH : Qᴴ * PI.UpqRep.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  rw [qi]
  refine ⟨?_, Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hQ.2) hg.1) hQ.2⟩
  show (Qᴴ * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qᴴ * g * Q) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hH]
  calc (Qᴴ * g * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q) * (Qᴴ * g * Q)
      = Qᴴ * (gᴴ * (Q * Qᴴ) * PI.UpqRep.Jm ε * (Q * Qᴴ) * g) * Q := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [q2, Matrix.mul_one, Matrix.mul_one, hJ]

theorem lev_zero_of_wt (hH : Hyps) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDS ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hR Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hR Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := GlobalTheory.isMod_smooth_of_isDS hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem norm_sq_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (t : ℝ) (q : ℕ) {d : ℝ}
    (hd : 0 ≤ d) (v : Wp) : ‖((t ^ q * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t ^ (2 * q) * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hd]
  ring

theorem oneLength_moment_lowestType_largeGap (hH : Hyps) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν : Fin (2 * r + k + 1) → ℤ) (q : ℕ)
    (hν : n1 ν + (r + 1) * q ≤ q0) (hq : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w)
    (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
      ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ q) := by
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hA' := mul_nonneg hA (by positivity : (0 : ℝ) ≤ (b ^ 2) ^ (2 * r))
  have hnum := GlobalTheory.MomNum.mom_num k r lam u b bv ga h q0 _ hNum hT
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have key := lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((lenA k r z (Matrix.of x) a ^ q * Real.sqrt (dg ν) : ℝ) : ℂ) • l ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ q) (pow_nonneg (hA'.trans hnum) q) ?_ w hwL hw1
  · simpa only [norm_sq_scaled _ _ hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add, hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((((hlen a).pow_const q).mul_const _).aestronglyMeasurable)).smul (hmeas (l ν) hBeL.1 v hv)
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := conj_back hQ hg
    simp only [norm_sq_scaled _ _ hdg.le]
    have := lintegral_rmul hSide (fun x => lenA k r z x a ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ x v)‖ ^ 2))
      (((GlobalTheory.LengthCont.lenA_continuousOn k r z hSide.1 hT a).pow _).mul (continuousOn_const.mul
        ((GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (l ν) hBeL.1.1 hBeL.1.2.1 hBeL.1.2.2.2
          v hv).1.norm.pow 2))) ?_ hgG
    · rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs a
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      rw [e, hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [norm_sq_scaled _ _ hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    by_cases hnz : NzOn (R ν) (l ν)
    · have hLev := lev_zero_of_wt hH hk hDS hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
      have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
      have hmain := single_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r q (fun a x => lenA k r z (Matrix.of x) a)
        (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)
        (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
        hlen
        (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
        (((hmeas (l ν) hBeL.1 v hvs).norm.aemeasurable.pow_const 2).const_mul _)
        (fun x => mul_nonneg hdg.le (by positivity))
        (by
          have := ((GlobalTheory.MomMass.mom_mass hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 v hvs
          simpa only [one_mul, hv1, one_pow, ENNReal.ofReal_one] using this)
        hA (one_le_pow₀ hb)
        (fun q' hq' => by
          have := GlobalTheory.Moment.moment_first_length hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE
            q' ν (by omega) 0 (by omega) ⟨v, hvs⟩ hLev
          simpa only [hv1', one_pow, mul_one] using this)
        (fun a q' hq' => by
          have := GlobalTheory.RatioMoment.ratio_moment hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
            0 q' (by omega) a ⟨v, hvs⟩ hLev
          simpa only [hv1', one_pow, mul_one] using this) a
      exact hmain.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hA' hnum _))
    · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
        intro v hv
        by_contra hne
        exact hnz ⟨v, hv, hne⟩
      refine le_of_eq_of_le ?_ bot_le
      rw [bot_eq_zero, ← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [hz _ (hsm _ hx v hvs)]
      simp

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem moment_one : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν (q : ℕ), n1 ν + (r + 1) * q ≤ q0 → (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν q hν hq w hw a =>
    oneLength_moment_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν q hν hq w hw a

end main

end GlobalTheory.MomOne
end
end
