import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveCptBoundedTime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorAdjoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjGelfValOfIsHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariant
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.PairAdj

section General

variable {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (μ : Measure Γ) [μ.IsMulRightInvariant] [μ.IsInvInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [IsTopologicalGroup Γ] [T2Space Γ] [SecondCountableTopology Γ] [BorelSpace Γ] [Group Γ] [TopologicalSpace Γ] in

theorem inner_integral_left {μ : Measure Γ} {A : Γ → V} (hA : Integrable A μ) (c : V) :
    ⟪∫ y, A y ∂μ, c⟫_ℂ = ∫ y, ⟪A y, c⟫_ℂ ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hA c, ← integral_conj]
  simp only [inner_conj_symm]

theorem pair_general (K : Γ → V →L[ℂ] V) (F H : Γ → V) (hK : Continuous K) (hF : Continuous F)
    (hH : Continuous H) (cK : HasCompactSupport K) (cF : HasCompactSupport F) (cH : HasCompactSupport H) :
    ∫ x, ⟪∫ y, ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y)) ∂μ, H x⟫_ℂ ∂μ
      = ∫ x, ⟪F x, ∫ y, K y (H (x * y)) ∂μ⟫_ℂ ∂μ := by
  have hadj : Continuous fun y : Γ => ContinuousLinearMap.adjoint (K y⁻¹) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := V)).continuous.comp (hK.comp continuous_inv)

  have i1 : ∀ x, Integrable (fun y => ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y))) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hadj.clm_apply (hF.comp (continuous_const.mul continuous_id))) ?_
    have c1 : HasCompactSupport fun y => F (x * y) := cF.comp_homeomorph (Homeomorph.mulLeft x)
    refine c1.mono (fun y hy => ?_)
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0, map_zero])
  have i2 : ∀ x, Integrable (fun y => K y (H (x * y))) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hK.clm_apply (hH.comp (continuous_const.mul continuous_id))) ?_
    refine cK.mono (fun y hy => ?_)
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0]; simp)

  have jA : Integrable (Function.uncurry fun x y : Γ => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c1 : Continuous fun p : Γ × Γ => F (p.1 * p.2⁻¹) :=
        hF.comp (continuous_fst.mul continuous_snd.inv)
      have c2 : Continuous fun p : Γ × Γ => K p.2 (H p.1) :=
        (hK.comp continuous_snd).clm_apply (hH.comp continuous_fst)
      exact c1.inner c2
    · refine HasCompactSupport.intro (cH.isCompact.prod cK.isCompact) (fun p hp => ?_)
      have : H p.1 = 0 ∨ K p.2 = 0 := by
        by_contra hc
        push_neg at hc
        exact hp ⟨subset_tsupport _ hc.1, subset_tsupport _ hc.2⟩
      rcases this with h0 | h0 <;> simp [Function.uncurry, h0]
  have jB : Integrable (Function.uncurry fun x y : Γ => ⟪F x, K y (H (x * y))⟫_ℂ) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c2 : Continuous fun p : Γ × Γ => K p.2 (H (p.1 * p.2)) :=
        (hK.comp continuous_snd).clm_apply (hH.comp (continuous_fst.mul continuous_snd))
      exact (hF.comp continuous_fst).inner c2
    · refine HasCompactSupport.intro (cF.isCompact.prod cK.isCompact) (fun p hp => ?_)
      have : F p.1 = 0 ∨ K p.2 = 0 := by
        by_contra hc
        push_neg at hc
        exact hp ⟨subset_tsupport _ hc.1, subset_tsupport _ hc.2⟩
      rcases this with h0 | h0 <;> simp [Function.uncurry, h0]
  calc ∫ x, ⟪∫ y, ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y)) ∂μ, H x⟫_ℂ ∂μ
      = ∫ x, ∫ y, ⟪F (x * y⁻¹), K y (H x)⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [inner_integral_left (i1 x) (H x),
          ← integral_inv_eq_self (fun y => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) μ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [inv_inv]
        exact ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ∫ y, ∫ x, ⟪F (x * y⁻¹), K y (H x)⟫_ℂ ∂μ ∂μ := integral_integral_swap jA
    _ = ∫ y, ∫ x, ⟪F x, K y (H (x * y))⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [← integral_mul_right_eq_self (fun x => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) y]
        simp only [mul_inv_cancel_right]
    _ = ∫ x, ∫ y, ⟪F x, K y (H (x * y))⟫_ℂ ∂μ ∂μ := (integral_integral_swap jB).symm
    _ = ∫ x, ⟪F x, ∫ y, K y (H (x * y)) ∂μ⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact integral_inner (i2 x) (F x)

end General

variable {n : ℕ}

instance instSC : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Mat n)).symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Mat n)).secondCountableTopology

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  change y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem pairAdj : LgFacts → Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f h : Mat n → E.V), KReg k → ContinuousOn f (GLs n) → ContinuousOn h (GLs n) → Cpt f → Cpt h → (haveI := FiniteDimensional.complete ℂ E.V; ∫ x : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x.val, h x.val⟫_ℂ ∂μ = ∫ x : G n, ⟪f x.val, act μ E k h x.val⟫_ℂ ∂μ) := by
  intro hL hU n _ _ μ _ E k f h hk hf hh cf ch
  haveI := FiniteDimensional.complete ℂ E.V
  haveI : μ.IsMulRightInvariant := (hU n μ).1
  haveI : μ.IsInvInvariant := (hU n μ).2
  have hc : ∀ R, IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1
  haveI : SigmaFinite μ := ⟨⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun _ => trivial,
    fun m => (hc m).measure_lt_top,
    Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (exists_nat_ge (lg y.val))⟩⟩⟩
  have cont : ∀ {W : Type} [TopologicalSpace W] {φ : Mat n → W}, ContinuousOn φ (GLs n) →
      Continuous fun y : G n => φ y.val := fun hφ =>
    hφ.comp_continuous Units.continuous_val val_mem_GLs
  have supp : ∀ {W : Type} [TopologicalSpace W] [Zero W] {φ : Mat n → W},
      (∃ R, ∀ y ∈ GLs n, R < lg y → φ y = 0) → HasCompactSupport fun y : G n => φ y.val := by
    rintro W _ _ φ ⟨R, hR⟩
    exact HasCompactSupport.intro (hc R) fun y hy => hR _ (val_mem_GLs y) (not_le.1 hy)
  have key := pair_general μ (fun y : G n => k y.val) (fun x => f x.val) (fun x => h x.val)
    (cont hk.1) (cont hf) (cont hh) (supp hk.2) (supp cf) (supp ch)
  simp only [Matrix.coe_units_inv, Units.val_mul] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult.PairAdj
end
end

section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

variable {n : ℕ}

theorem isOpen_GLs_dens (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage h

theorem mul_unitary_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    y * k.1 ∈ GLs n := by
  have h1 : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have h2 : k.1.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse h1
  have h3 : y.det ≠ 0 := hy
  change (y * k.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h3 h2

theorem inner_rho_inv (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (a v : E.V) :
    ⟪E.ρ k⁻¹ a, v⟫_ℂ = ⟪a, E.ρ k v⟫_ℂ := by
  let L : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ a) = a := by
    have : (E.ρ k * E.ρ k⁻¹) a = a := by
      rw [← map_mul, mul_inv_cancel, map_one]; rfl
    simpa using this
  have h2 := L.inner_map_map (E.ρ k⁻¹ a) v
  have h3 : L (E.ρ k⁻¹ a) = a := h1
  have h4 : L v = E.ρ k v := rfl
  rw [h3, h4] at h2
  exact h2.symm

theorem section_orth_cpt_zero : KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : Mat n → E.V), ContinuousOn A (GLs n) →
    (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, A (y * k₂.1) = E.ρ k₂⁻¹ (A y)) →
    (∀ h ∈ CE E, Cpt h → ∫ y : G n, ⟪A y.val, h y.val⟫_ℂ ∂μ = 0) → ∀ y ∈ GLs n, A y = 0 := by
  intro hK n _ _ μ _ E A hA hEq hOrth y hy
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  let e : E.V := A y
  let κ : Mat n → (E.V →L[ℂ] E.V) := fun z => (innerSL ℂ (A z)).smulRight e
  have hκ : ∀ z v, κ z v = ⟪A z, v⟫_ℂ • e := fun z v => by simp [κ]
  have hcont : ContinuousOn κ (GLs n) := by
    have h1 : Continuous fun a : E.V => (innerSL ℂ a).smulRight e :=
      ((ContinuousLinearMap.smulRightL ℂ E.V E.V).flip e).continuous.comp (innerSL ℂ).continuous
    exact h1.comp_continuousOn hA
  have hequi : ∀ z ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, κ (z * k₂.1) = κ z * E.ρ k₂ := by
    intro z hz k₂
    ext v
    rw [ContinuousLinearMap.mul_apply, hκ, hκ, hEq z hz k₂, inner_rho_inv]
  have hact : ∀ f ∈ CE E, Cpt f → (∀ z ∈ GLs n, z ∉ GLs n → f z = 0) → act μ E κ f 1 = 0 := by
    intro f hf hc _
    have h0 := hOrth f hf hc
    unfold act
    simp only [one_mul, hκ]
    rw [integral_smul_const, h0, zero_smul]
  have hz := hK n μ E κ (GLs n) (isOpen_GLs_dens n) subset_rfl
    (fun z hz k => mul_unitary_mem_GLs hz k) hcont hequi hact y hy
  have h1 : ⟪A y, A y⟫_ℂ • e = 0 := by
    rw [← hκ, hz]; rfl
  rcases smul_eq_zero.1 h1 with h | h
  · exact inner_self_eq_zero.1 h
  · exact h

end GlobalTheory.CompanionTheory.WaveMult
end
end

section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_center_expansion : ∀ (n m : ℕ), ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ), (∀ cc : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = ∑ i, c i * ((w i).map (GlobalTheory.Dec.gelfVal cc)).prod) ∧ (RCalc → ∀ (s : Bool) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, gelT s m f x = ∑ i, c i • zOp ((w i).map (fun j => (s, j))) f x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | exact GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | (intros; apply GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants <;> assumption)
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Sym

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_add Rd_smul differentiableAt_of_smooth Rd_contDiffOn isOpen_GLs)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Expand

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Expand

section Pairing

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrable_of_cpt (hL : LgFacts) {F : Mat n → ℂ} (hc : ContinuousOn F (GLs n)) (hF : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hF
  have hc' : Continuous fun y : G n => F y.val :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  refine hc'.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem cpt_inner_left {u v : Mat n → V} (hu : Cpt u) : Cpt fun y => ⟪u y, v y⟫_ℂ := by
  obtain ⟨R, hR⟩ := hu
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem integrable_inner (hL : LgFacts) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n))
    (hv : ContDiffOn ℝ ∞ v (GLs n)) (hc : Cpt fun y => ⟪u y, v y⟫_ℂ) :
    Integrable (fun y : G n => ⟪u y.val, v y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (F := fun y => ⟪u y, v y⟫_ℂ) (hu.inner ℂ hv).continuousOn hc

end Pairing

end GlobalTheory.CompanionTheory.WaveK.Sym
end
end

section
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WordAdj

open GlobalTheory.CompanionTheory.WaveK.Sym (integrable_inner cpt_inner_left)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

section Ops

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (X : Mat n) : ∀ y ∈ GLs n, R < lg y → Rd X u y = 0 := by
  intro y hy hR
  unfold LgFacts at hL
  have hc : ContinuousOn lg (GLs n) := (hL n).2.2.2.1.continuousOn
  have ho : IsOpen (GLs n) := by
    unfold GLs
    exact isOpen_ne_fun (by fun_prop) continuous_const
  have hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hc.isOpen_inter_preimage ho isOpen_Ioi
  have hev : u =ᶠ[nhds y] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds ⟨hy, hR⟩) fun z hz => hu z hz.1 hz.2
  unfold Rd
  rw [hev.fderiv_eq]
  simp

theorem Eu_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (a b : Fin n) : ∀ y ∈ GLs n, R < lg y → Eu s a b u y = 0 := by
  intro y hy hR
  have h1 := Rd_van hL hu (single a b 1) y hy hR
  have h2 := Rd_van hL hu (single a b Complex.I) y hy hR
  unfold Eu
  cases s <;> simp [h1, h2]

theorem Epow_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (m : ℕ) (a b : Fin n) : ∀ y ∈ GLs n, R < lg y → Epow s m a b u y = 0 := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, hu y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => Eu_van hL (ih c b) s a c y hy hR

theorem gel_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (m : ℕ) : ∀ y ∈ GLs n, R < lg y → gel s m u y = 0 := by
  intro y hy hR
  unfold gel
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => Epow_van hL hu s m a a y hy hR

theorem cpt_zOp (hL : LgFacts) (w : List (Bool × ℕ)) {u : Mat n → V} (hu : Cpt u) :
    Cpt (zOp w u) := by
  unfold Cpt at hu ⊢
  obtain ⟨R, hR⟩ := hu
  refine ⟨R, ?_⟩
  induction w with
  | nil => exact hR
  | cons p w ih => exact gel_van hL ih p.1 p.2

theorem zOp_contDiffOn (w : List (Bool × ℕ)) {u : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w u) (GLs n) := by
  induction w with
  | nil => exact hu
  | cons p w ih => exact GlobalTheory.CompanionTheory.RCalc.gel_contDiffOn p.1 p.2 ih

theorem zOp_append (w w' : List (Bool × ℕ)) (u : Mat n → V) :
    zOp (w ++ w') u = zOp w (zOp w' u) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    show gel p.1 p.2 (zOp (w ++ w') u) = gel p.1 p.2 (zOp w (zOp w' u))
    rw [ih]

end Ops

private theorem isHecke_div_and_resEtaPow_div (n : ℕ) (s : Bool) (m : ℕ) : ∃ (M : ℕ) (e : Fin M → ℂ) (v : Fin M → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal [(s, m)] χ) = ∑ j, e j * zVal (v j) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ = ∑ j, e j * ∫ y : G n, ⟪f y.val, zOp (v j) h y.val⟫_ℂ ∂μ) := by
  obtain ⟨M, d, w, hv, ho⟩ := GlobalTheory.T.gelfand_operator_center_expansion n m
  refine ⟨M, fun j => (-1) ^ m * d j, fun j => (w j).map (fun k => (!s, k)), ?_, ?_⟩
  · intro χ hχ
    have h1 : zVal [(s, m)] χ = GlobalTheory.Dec.gelfVal (χ s) m := by simp [zVal]
    rw [h1, conj_gelfVal_of_isHerm n χ hχ s m]
    have h3 : ∀ j, zVal ((w j).map (fun k => (!s, k))) χ = ((w j).map (GlobalTheory.Dec.gelfVal (χ (!s)))).prod := by
      intro j
      simp [zVal, List.map_map, Function.comp_def]
    rw [Finset.sum_congr rfl (fun j _ => by rw [h3 j, mul_assoc]), ← Finset.mul_sum, ← hv (χ (!s)), ← mul_assoc, ← mul_pow]
    simp
  · intro hL hR _ _ μ _ V _ _ _ f h hf hh cf ch
    rw [GlobalTheory.T.gelfand_operator_adjoint hL hR n μ V s m f h hf hh cf ch]
    have hpt : ∀ y : G n, ⟪f y.val, GlobalTheory.CompanionTheory.WaveMult.gelT (!s) m h y.val⟫_ℂ = ∑ j, d j * ⟪f y.val, zOp ((w j).map (fun k => (!s, k))) h y.val⟫_ℂ := by
      intro y
      rw [ho hR (!s) h hh y.val (val_mem_GLs y), inner_sum]
      simp only [inner_smul_right]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun j _ => (integrable_inner μ hL hf (zOp_contDiffOn _ hh) (cpt_inner_left cf)).const_mul (d j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring

private theorem isPair_and_isPair_of_isTriple {M N : ℕ} (F : Fin M → Fin N → ℂ) : ∑ k : Fin (M * N), F (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = ∑ j, ∑ i, F j i :=
  (Equiv.sum_comp finProdFinEquiv.symm (fun q => F q.1 q.2)).trans (Fintype.sum_prod_type _)

theorem word_adjoint : ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i) h y.val⟫_ℂ ∂μ) := by
  intro n w
  induction w with
  | nil =>
    refine ⟨1, fun _ => 1, fun _ => [], ?_, ?_⟩
    · intro χ _
      simp [zVal]
    · intro _ _ _ _ μ _ V _ _ _ f h _ _ _ _
      simp [zOp]
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    obtain ⟨N, c, w₁, hz, hi⟩ := ih
    obtain ⟨M, e, v, hz1, hi1⟩ := isHecke_div_and_resEtaPow_div n s m
    refine ⟨M * N, fun k => e (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2,
      fun k => w₁ (finProdFinEquiv.symm k).2 ++ v (finProdFinEquiv.symm k).1, ?_, ?_⟩
    · intro χ hχ
      have hs := isPair_and_isPair_of_isTriple (fun j i => e j * c i * zVal (w₁ i ++ v j) χ)
      beta_reduce at hs
      rw [hs]
      have h1 : zVal ((s, m) :: w) χ = zVal [(s, m)] χ * zVal w χ := zVal_append [(s, m)] w χ
      rw [h1, map_mul, hz1 χ hχ, hz χ hχ, Finset.sum_mul_sum]
      simp only [zVal_append]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    · intro hL hR _ _ μ _ V _ _ _ f h hf hh cf ch
      have hs := isPair_and_isPair_of_isTriple (fun j i => e j * c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i ++ v j) h y.val⟫_ℂ ∂μ)
      beta_reduce at hs
      rw [hs]
      have hwf := zOp_contDiffOn w hf
      have cwf := cpt_zOp hL w cf
      have step1 : ∫ y : G n, ⟪zOp ((s, m) :: w) f y.val, h y.val⟫_ℂ ∂μ =
          ∑ j, e j * ∫ y : G n, ⟪zOp w f y.val, zOp (v j) h y.val⟫_ℂ ∂μ :=
        hi1 hL hR μ V (zOp w f) h hwf hh cwf ch
      rw [step1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hi hL hR μ V f (zOp (v j) h) hf (zOp_contDiffOn _ hh) cf (cpt_zOp hL _ ch), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zOp_append]
      ring

end GlobalTheory.CompanionTheory.WaveMult.WordAdj
end
end

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_pairing_adjoint : ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i) h y.val⟫_ℂ ∂μ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint
end

section
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WaveSymm

theorem one_dim (Φ A B : ℝ → ℝ → ℂ)
    (h1 : ∀ T r, HasDerivAt (fun r => Φ r (T - r)) (A r (T - r) - B r (T - r)) r)
    (h2 : ∀ t s r, A (t + r) (s + r) - B (t + r) (s + r) = A t s - B t s)
    (h3 : ∀ t s r, A (t + r) (s - r) + B (t + r) (s - r) = A t s + B t s)
    (hA : ∀ s, A 0 s = 0) (hB : ∀ t, B t 0 = 0) (T : ℝ) : Φ T 0 = Φ 0 T := by
  have hq : ∀ t s, (A t s - B t s) + (A s t - B s t) = 0 := by
    intro t s
    have e1 := h2 (t - s) 0 s
    have e2 := h2 0 (t - s) s
    have e3 := h3 0 (t - s) (t - s)
    simp only [sub_add_cancel, zero_add, sub_self] at e1 e2 e3
    rw [e1, e2]
    rw [hB, hA] at e3 ⊢
    linear_combination e3
  have hd : ∀ r, HasDerivAt (fun r => Φ r (T - r) - Φ (T - r) (T - (T - r))) 0 r := by
    intro r
    have a1 := h1 T r
    have a2 := HasDerivAt.comp_const_sub (f := fun r => Φ r (T - r)) T r (h1 T (T - r))
    have a3 : HasDerivAt (fun r => Φ r (T - r) - Φ (T - r) (T - (T - r)))
        (A r (T - r) - B r (T - r) - -(A (T - r) (T - (T - r)) - B (T - r) (T - (T - r)))) r := a1.sub a2
    have e : A r (T - r) - B r (T - r) - -(A (T - r) (T - (T - r)) - B (T - r) (T - (T - r))) = 0 := by
      rw [sub_sub_cancel]
      linear_combination hq r (T - r)
    rwa [e] at a3
  have hc := is_const_of_deriv_eq_zero (f := fun r => Φ r (T - r) - Φ (T - r) (T - (T - r)))
    (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) 0 T
  simp only [sub_zero, sub_self] at hc
  linear_combination (-1 / 2 : ℂ) * hc

variable {n : ℕ}

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  have h : IsUnit (y.val.det) := (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
  exact h.ne_zero

theorem continuous_val : Continuous (fun y : G n => y.val) := Units.continuous_val

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_vanish (hL : LgFacts) (f : G n → ℂ) (hf : Continuous f) (R : ℝ)
    (h : ∀ y : G n, R < lg y.val → f y = 0) : Integrable f μ := by
  have hK : IsCompact {y : G n | lg y.val ≤ R} := ((hL n).2.2.2.2.1 R)
  refine hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun y hy => h y ?_)
  simpa using hy

theorem hasDerivAt_integral (hL : LgFacts) (c c' : ℝ → Mat n → ℂ)
    (hc : ContinuousOn (Function.uncurry c) (Set.univ ×ˢ GLs n))
    (hc' : ContinuousOn (Function.uncurry c') (Set.univ ×ˢ GLs n))
    (hd : ∀ r, ∀ y ∈ GLs n, HasDerivAt (fun r => c r y) (c' r y) r)
    (hs : ∀ B : ℝ, ∃ R : ℝ, ∀ r, |r| ≤ B → ∀ y ∈ GLs n, R < lg y → c r y = 0 ∧ c' r y = 0) (r : ℝ) :
    HasDerivAt (fun r => ∫ y : G n, c r y.val ∂μ) (∫ y : G n, c' r y.val ∂μ) r := by
  obtain ⟨R, hR⟩ := hs (|r| + 1)
  have hK : IsCompact {y : G n | lg y.val ≤ R} := ((hL n).2.2.2.2.1 R)
  have cont2 : ∀ {f : ℝ → Mat n → ℂ}, ContinuousOn (Function.uncurry f) (Set.univ ×ˢ GLs n) →
      Continuous (fun p : ℝ × G n => f p.1 p.2.val) := by
    intro f hf
    exact hf.comp_continuous (continuous_fst.prodMk (continuous_val.comp continuous_snd))
      fun p => ⟨Set.mem_univ _, val_mem_GLs p.2⟩
  have contc := cont2 hc
  have contc' := cont2 hc'
  have cont1 : ∀ {f : ℝ → Mat n → ℂ}, Continuous (fun p : ℝ × G n => f p.1 p.2.val) → ∀ x,
      Continuous (fun y : G n => f x y.val) := by
    intro f hf x
    exact hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := r - 1) (b := r + 1)).prod hK).exists_bound_of_continuousOn
    contc'.continuousOn
  have hball : ∀ x ∈ Metric.ball r 1, |x| ≤ |r| + 1 ∧ x ∈ Set.Icc (r - 1) (r + 1) := by
    intro x hx
    have hx' : |x - r| < 1 := by simpa [Real.dist_eq] using hx
    have := abs_lt.mp hx'
    refine ⟨?_, by constructor <;> linarith [this.1, this.2]⟩
    calc |x| = |(x - r) + r| := by ring_nf
      _ ≤ |x - r| + |r| := abs_add_le _ _
      _ ≤ |r| + 1 := by linarith
  have hfar : ∀ y : G n, R < lg y.val → ∀ x, |x| ≤ |r| + 1 → c x y.val = 0 ∧ c' x y.val = 0 :=
    fun y hy x hx => hR x hx _ (val_mem_GLs y) hy
  have hr0 : |r| ≤ |r| + 1 := by linarith
  have hbound : Integrable ({y : G n | lg y.val ≤ R}.indicator fun _ => C) μ := by
    refine IntegrableOn.integrable_indicator ?_ hK.measurableSet
    exact integrableOn_const hK.measure_lt_top.ne
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun r (y : G n) => c r y.val)
    (F' := fun r (y : G n) => c' r y.val) (s := Metric.ball r 1) (bound := {y : G n | lg y.val ≤ R}.indicator fun _ => C)
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall fun x => (cont1 contc x).aestronglyMeasurable)
    (integrable_of_vanish μ hL _ (cont1 contc r) R fun y hy => (hfar y hy r hr0).1)
    (cont1 contc' r).aestronglyMeasurable ?_ hbound ?_).2
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    by_cases hy : lg y.val ≤ R
    · rw [Set.indicator_of_mem (by exact hy)]
      exact hC (x, y) ⟨(hball x hx).2, hy⟩
    · rw [Set.indicator_of_notMem (by exact hy), (hfar y (not_le.mp hy) x (hball x hx).1).2]
      simp
  · exact Filter.Eventually.of_forall fun y x _ => hd x _ (val_mem_GLs y)

end Int

theorem smooth_deriv_gen {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℝ → X → V) {S : Set X} (hS : IsOpen S) (h : ContDiffOn ℝ ∞ (Function.uncurry a) (Set.univ ×ˢ S)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t y => deriv (fun s => a s y) t) (Set.univ ×ˢ S) ∧
      ∀ t, ∀ y ∈ S, HasDerivAt (fun s => a s y) (deriv (fun s => a s y) t) t := by
  have hO : IsOpen ((Set.univ : Set ℝ) ×ˢ S) := isOpen_univ.prod hS
  have hf : ∀ t, ∀ y ∈ S, HasDerivAt (fun s => a s y) (fderiv ℝ (Function.uncurry a) (t, y) ((1 : ℝ), (0 : X))) t := by
    intro t y hy
    have hd : HasFDerivAt (Function.uncurry a) (fderiv ℝ (Function.uncurry a) (t, y)) (t, y) :=
      ((h.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : X)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact hd.comp_hasDerivAt t hl
  constructor
  · have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry a)) (Set.univ ×ˢ S) :=
      ContDiffOn.fderiv_of_isOpen h hO (by simp)
    have h2 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (Function.uncurry a) p ((1 : ℝ), (0 : X))) (Set.univ ×ˢ S) :=
      h1.clm_apply contDiffOn_const
    refine h2.congr ?_
    rintro ⟨t, y⟩ ⟨-, hy⟩
    exact (hf t y hy).deriv
  · intro t y hy
    rw [(hf t y hy).deriv]
    exact hf t y hy

section Time

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun y : Mat n => y.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

def dt (a : ℝ → Mat n → V) : ℝ → Mat n → V := fun t y => deriv (fun s => a s y) t

def Sm (a : ℝ → Mat n → V) : Prop := ContDiffOn ℝ ∞ (Function.uncurry a) (Set.univ ×ˢ GLs n)

def Sp (a : ℝ → Mat n → V) : Prop := ∀ B : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ B → ∀ y ∈ GLs n, R < lg y → a t y = 0

theorem hasDerivAt_dt {a : ℝ → Mat n → V} (h : Sm a) (t : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun s => a s y) (dt a t y) t :=
  (smooth_deriv_gen a (isOpen_GLs n) h).2 t y hy

theorem sm_dt {a : ℝ → Mat n → V} (h : Sm a) : Sm (dt a) :=
  (smooth_deriv_gen a (isOpen_GLs n) h).1

theorem sm_at {a : ℝ → Mat n → V} (h : Sm a) (t : ℝ) : ContDiffOn ℝ ∞ (a t) (GLs n) := by
  have h1 : ContDiff ℝ ∞ (fun y : Mat n => (t, y)) := contDiff_const.prodMk contDiff_id
  have h2 := ContDiffOn.comp (g := Function.uncurry a) (f := fun y : Mat n => (t, y)) (s := GLs n)
    (t := Set.univ ×ˢ GLs n) h h1.contDiffOn fun y hy => ⟨Set.mem_univ _, hy⟩
  exact h2

theorem sp_dt {a : ℝ → Mat n → V} (h : Sp a) : Sp (dt a) := by
  intro B
  obtain ⟨R, hR⟩ := h (|B| + 1)
  refine ⟨R, fun t ht y hy hl => ?_⟩
  have hlt : |t| < |B| + 1 := by linarith [le_abs_self B]
  have h1 : ∀ᶠ s in nhds t, |s| < |B| + 1 :=
    (continuous_abs.tendsto t).eventually (gt_mem_nhds hlt)
  have h2 : (fun s => a s y) =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [h1] with s hs using hR s hs.le y hy hl
  change deriv (fun s => a s y) t = 0
  rw [h2.deriv_eq]
  simp

theorem contOn_shift {a : ℝ → Mat n → V} (h : Sm a) (t α : ℝ) :
    ContinuousOn (fun p : ℝ × Mat n => a (t + α * p.1) p.2) (Set.univ ×ˢ GLs n) := by
  have h1 : Continuous (fun p : ℝ × Mat n => (t + α * p.1, p.2)) := by fun_prop
  exact ContinuousOn.comp (ContDiffOn.continuousOn h) h1.continuousOn fun p hp => ⟨Set.mem_univ _, hp.2⟩

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_inner (hL : LgFacts) {f h : Mat n → V} (hf : ContinuousOn f (GLs n)) (hh : ContinuousOn h (GLs n))
    (R : ℝ) (hv : ∀ y ∈ GLs n, R < lg y → ⟪f y, h y⟫_ℂ = 0) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ := by
  refine integrable_of_vanish μ hL _ ?_ R fun y hy => hv _ (val_mem_GLs y) hy
  exact (hf.comp_continuous continuous_val val_mem_GLs).inner (hh.comp_continuous continuous_val val_mem_GLs)

def Pr (a b : ℝ → Mat n → V) (t s : ℝ) : ℂ := ∫ y : G n, ⟪a t y.val, b s y.val⟫_ℂ ∂μ

theorem Pr_hasDeriv (hL : LgFacts) {a b : ℝ → Mat n → V} (ha : Sm a) (hb : Sm b) (hsa : Sp a) (hsb : Sp b)
    (t s α β r : ℝ) :
    HasDerivAt (fun r => Pr μ a b (t + α * r) (s + β * r))
      ((α : ℂ) * Pr μ (dt a) b (t + α * r) (s + β * r) + (β : ℂ) * Pr μ a (dt b) (t + α * r) (s + β * r)) r := by
  have c1 : ContinuousOn (fun p : ℝ × Mat n => ⟪a (t + α * p.1) p.2, b (s + β * p.1) p.2⟫_ℂ) (Set.univ ×ˢ GLs n) :=
    (contOn_shift ha t α).inner (contOn_shift hb s β)
  have c2 : ContinuousOn (fun p : ℝ × Mat n => (α : ℂ) * ⟪dt a (t + α * p.1) p.2, b (s + β * p.1) p.2⟫_ℂ +
      (β : ℂ) * ⟪a (t + α * p.1) p.2, dt b (s + β * p.1) p.2⟫_ℂ) (Set.univ ×ˢ GLs n) :=
    (continuousOn_const.mul ((contOn_shift (sm_dt ha) t α).inner (contOn_shift hb s β))).add
      (continuousOn_const.mul ((contOn_shift ha t α).inner (contOn_shift (sm_dt hb) s β)))
  have key := hasDerivAt_integral μ hL (fun r y => ⟪a (t + α * r) y, b (s + β * r) y⟫_ℂ)
    (fun r y => (α : ℂ) * ⟪dt a (t + α * r) y, b (s + β * r) y⟫_ℂ + (β : ℂ) * ⟪a (t + α * r) y, dt b (s + β * r) y⟫_ℂ)
    c1 c2 ?_ ?_ r
  · have e : ∫ y : G n, ((α : ℂ) * ⟪dt a (t + α * r) y.val, b (s + β * r) y.val⟫_ℂ +
        (β : ℂ) * ⟪a (t + α * r) y.val, dt b (s + β * r) y.val⟫_ℂ) ∂μ =
        (α : ℂ) * Pr μ (dt a) b (t + α * r) (s + β * r) + (β : ℂ) * Pr μ a (dt b) (t + α * r) (s + β * r) := by
      obtain ⟨Ra, hRa⟩ := hsa |t + α * r|
      obtain ⟨Rb, hRb⟩ := hsb |s + β * r|
      have i1 := integrable_inner μ hL (sm_at (sm_dt ha) (t + α * r)).continuousOn (sm_at hb (s + β * r)).continuousOn Rb
        (fun y hy hl => by rw [hRb _ le_rfl y hy hl, inner_zero_right])
      have i2 := integrable_inner μ hL (sm_at ha (t + α * r)).continuousOn (sm_at (sm_dt hb) (s + β * r)).continuousOn Ra
        (fun y hy hl => by rw [hRa _ le_rfl y hy hl, inner_zero_left])
      rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
      rfl
    rw [← e]
    exact key
  · intro r y hy
    have l1 : HasDerivAt (fun r : ℝ => t + α * r) α r := by
      simpa using ((hasDerivAt_id r).const_mul α).const_add t
    have l2 : HasDerivAt (fun r : ℝ => s + β * r) β r := by
      simpa using ((hasDerivAt_id r).const_mul β).const_add s
    have da0 : HasDerivAt (fun τ => a τ y) (dt a (t + α * r) y) ((fun r : ℝ => t + α * r) r) :=
      hasDerivAt_dt ha (t + α * r) hy
    have db0 : HasDerivAt (fun τ => b τ y) (dt b (s + β * r) y) ((fun r : ℝ => s + β * r) r) :=
      hasDerivAt_dt hb (s + β * r) hy
    have da : HasDerivAt (fun r => a (t + α * r) y) (α • dt a (t + α * r) y) r :=
      HasDerivAt.scomp (g₁ := fun τ => a τ y) (h := fun r : ℝ => t + α * r) r da0 l1
    have db : HasDerivAt (fun r => b (s + β * r) y) (β • dt b (s + β * r) y) r :=
      HasDerivAt.scomp (g₁ := fun τ => b τ y) (h := fun r : ℝ => s + β * r) r db0 l2
    refine (da.inner ℂ db).congr_deriv ?_
    rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  · intro B
    obtain ⟨Ra, hRa⟩ := hsa (|t| + |α| * |B|)
    obtain ⟨Rb, hRb⟩ := hsb (|s| + |β| * |B|)
    refine ⟨max Ra Rb, fun r hr y hy hl => ?_⟩
    have hrB : |r| ≤ |B| := hr.trans (le_abs_self B)
    have b1 : |t + α * r| ≤ |t| + |α| * |B| := by
      calc |t + α * r| ≤ |t| + |α * r| := abs_add_le _ _
        _ = |t| + |α| * |r| := by rw [abs_mul]
        _ ≤ _ := by gcongr
    have b2 : |s + β * r| ≤ |s| + |β| * |B| := by
      calc |s + β * r| ≤ |s| + |β * r| := abs_add_le _ _
        _ = |s| + |β| * |r| := by rw [abs_mul]
        _ ≤ _ := by gcongr
    have z1 := hRa _ b1 y hy (lt_of_le_of_lt (le_max_left _ _) hl)
    have z2 := hRb _ b2 y hy (lt_of_le_of_lt (le_max_right _ _) hl)
    simp [z1, z2]

end Time

section Gel

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  have : fderiv ℝ (0 : Mat n → V) g = 0 := by
    change fderiv ℝ (fun _ : Mat n => (0 : V)) g = 0
    simp
  simp [Rd, this]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c b : Fin n) (f : Mat n → V) : Epow s 1 c b f = Eu s c b f := by
  simp only [Epow]
  rw [Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem EpowT_one (s : Bool) (c b : Fin n) (f : Mat n → V) : EpowT s 1 c b f = Eu s b c f := by
  simp only [EpowT]
  rw [Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) : gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  unfold gel
  refine Finset.sum_congr rfl fun a _ => ?_
  change (∑ c, Eu s a c (Epow s 1 c a f)) = _
  simp only [Epow_one]

theorem gelT_eq_gel (s : Bool) (f : Mat n → V) : gelT s 2 f = gel s 2 f := by
  have h : gelT s 2 f = ∑ a, ∑ c, Eu s c a (Eu s a c f) := by
    unfold gelT
    refine Finset.sum_congr rfl fun a _ => ?_
    change (∑ c, Eu s c a (EpowT s 1 c a f)) = _
    simp only [EpowT_one]
  rw [h, gel_two, Finset.sum_comm]

end Gel

section Om

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Eu_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := ((hR n).1 V f hf).1
  exact ((h _).add ((h _).const_smul _)).const_smul _

theorem gel_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) :
    ContDiffOn ℝ ∞ (gel s 2 f) (GLs n) := by
  have e : gel s 2 f = fun x => ∑ a, ∑ c, Eu s a c (Eu s c a f) x := by
    funext x
    rw [gel_two]
    simp [Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ => Eu_smooth hR (Eu_smooth hR hf s c a) s a c

variable [CompleteSpace V] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem Om_symm (hL : LgFacts) (hR : RCalc) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Om f y.val, h y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪f y.val, Om h y.val⟫_ℂ ∂μ := by
  have I : ∀ s : Bool, ∫ y : G n, ⟪gel s 2 f y.val, h y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪f y.val, gel (!s) 2 h y.val⟫_ℂ ∂μ := by
    intro s
    have := GlobalTheory.T.gelfand_operator_adjoint hL hR n μ V s 2 f h hf hh cf ch
    rw [gelT_eq_gel] at this
    simpa using this
  obtain ⟨Rf, hRf⟩ := cf
  obtain ⟨Rh, hRh⟩ := ch
  have i1 : ∀ s, Integrable (fun y : G n => ⟪gel s 2 f y.val, h y.val⟫_ℂ) μ := fun s =>
    integrable_inner μ hL (gel_smooth hR hf s).continuousOn hh.continuousOn Rh
      (fun y hy hl => by rw [hRh y hy hl, inner_zero_right])
  have i2 : ∀ s, Integrable (fun y : G n => ⟪f y.val, gel s 2 h y.val⟫_ℂ) μ := fun s =>
    integrable_inner μ hL hf.continuousOn (gel_smooth hR hh s).continuousOn Rf
      (fun y hy hl => by rw [hRf y hy hl, inner_zero_left])
  have e1 : ∫ y : G n, ⟪Om f y.val, h y.val⟫_ℂ ∂μ =
      2 * (∫ y : G n, ⟪gel true 2 f y.val, h y.val⟫_ℂ ∂μ + ∫ y : G n, ⟪gel false 2 f y.val, h y.val⟫_ℂ ∂μ) := by
    rw [← integral_add (i1 true) (i1 false), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Om, inner_add_left, inner_smul_left]
    ring
  have e2 : ∫ y : G n, ⟪f y.val, Om h y.val⟫_ℂ ∂μ =
      2 * (∫ y : G n, ⟪f y.val, gel true 2 h y.val⟫_ℂ ∂μ + ∫ y : G n, ⟪f y.val, gel false 2 h y.val⟫_ℂ ∂μ) := by
    rw [← integral_add (i2 true) (i2 false), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Om, inner_add_right, inner_smul_right]
    ring
  rw [e1, e2, I true, I false]
  simp only [Bool.not_true, Bool.not_false]
  ring

end Om

section Wave

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem dt_dt {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) (t : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (dt u) t y = Om (u t) y := by
  rw [← hu.2.2.1 t y hy, iteratedDeriv_succ, iteratedDeriv_one]
  rfl

theorem dt_zero {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {y : Mat n} (hy : y ∈ GLs n) :
    dt u 0 y = 0 := hu.2.2.2 y hy

theorem wave_pairing_second_time_derivative (hL : LgFacts) (hR : RCalc) {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v)
    (su : Sp u) (sv : Sp v) (t s : ℝ) : Pr μ (dt (dt u)) v t s = Pr μ u (dt (dt v)) t s := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨Ru, hRu⟩ := su |t|
  obtain ⟨Rv, hRv⟩ := sv |s|
  have h := Om_symm μ hL hR (sm_at (a := u) hu.1 t) (sm_at (a := v) hv.1 s) ⟨Ru, hRu t le_rfl⟩ ⟨Rv, hRv s le_rfl⟩
  unfold Pr
  calc ∫ y : G n, ⟪dt (dt u) t y.val, v s y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪Om (u t) y.val, v s y.val⟫_ℂ ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          simp only [dt_dt hu t (val_mem_GLs y)])
    _ = ∫ y : G n, ⟪u t y.val, Om (v s) y.val⟫_ℂ ∂μ := h
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => by
          simp only [dt_dt hv s (val_mem_GLs y)])

theorem line_const (hL : LgFacts) (hR : RCalc) {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v)
    (su : Sp u) (sv : Sp v) (β : ℝ) (hβ : β * β = 1) (t s r : ℝ) :
    Pr μ (dt u) v (t + 1 * r) (s + β * r) - (β : ℂ) * Pr μ u (dt v) (t + 1 * r) (s + β * r) =
      Pr μ (dt u) v t s - (β : ℂ) * Pr μ u (dt v) t s := by
  have hd : ∀ r, HasDerivAt (fun r => Pr μ (dt u) v (t + 1 * r) (s + β * r) - (β : ℂ) * Pr μ u (dt v) (t + 1 * r) (s + β * r)) 0 r := by
    intro r
    have d1 := Pr_hasDeriv μ hL (sm_dt (a := u) hu.1) hv.1 (sp_dt su) sv t s 1 β r
    have d2 := Pr_hasDeriv μ hL hu.1 (sm_dt (a := v) hv.1) su (sp_dt sv) t s 1 β r
    have d3 := d1.sub (d2.const_mul (β : ℂ))
    have hβ' : (β : ℂ) * β = 1 := by exact_mod_cast hβ
    have e := wave_pairing_second_time_derivative μ hL hR hu hv su sv (t + 1 * r) (s + β * r)
    have z : ((1 : ℝ) : ℂ) * Pr μ (dt (dt u)) v (t + 1 * r) (s + β * r) + (β : ℂ) * Pr μ (dt u) (dt v) (t + 1 * r) (s + β * r) -
        (β : ℂ) * (((1 : ℝ) : ℂ) * Pr μ (dt u) (dt v) (t + 1 * r) (s + β * r) + (β : ℂ) * Pr μ u (dt (dt v)) (t + 1 * r) (s + β * r)) = 0 := by
      rw [e]
      push_cast
      linear_combination (-Pr μ u (dt (dt v)) (t + 1 * r) (s + β * r)) * hβ'
    rw [z] at d3
    exact d3
  have hc := is_const_of_deriv_eq_zero
    (f := fun r => Pr μ (dt u) v (t + 1 * r) (s + β * r) - (β : ℂ) * Pr μ u (dt v) (t + 1 * r) (s + β * r))
    (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) r 0
  simpa using hc

end Wave

theorem _root_.GlobalTheory.CompanionTheory.WaveMult.wave_symm : LgFacts → RCalc → WaveSpeed → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) → ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ := by
  intro hL hR hS n _ _ μ _ E u v hu hv cu cv t
  have su : Sp u := wave_cpt_bounded_time hL hS n E u hu cu
  have sv : Sp v := wave_cpt_bounded_time hL hS n E v hv cv
  refine one_dim (Pr μ u v) (Pr μ (dt u) v) (Pr μ u (dt v)) ?_ ?_ ?_ ?_ ?_ t
  · intro T r
    have h := Pr_hasDeriv μ hL hu.1 hv.1 su sv 0 T 1 (-1) r
    have e1 : ∀ r : ℝ, (0 : ℝ) + 1 * r = r := fun r => by ring
    have e2 : ∀ r : ℝ, T + -1 * r = T - r := fun r => by ring
    simp only [e1, e2] at h
    refine h.congr_deriv ?_
    push_cast
    ring
  · intro t s r
    have h := line_const μ hL hR hu hv su sv 1 (by norm_num) t s r
    simpa using h
  · intro t s r
    have h := line_const μ hL hR hu hv su sv (-1) (by norm_num) t s r
    simpa [sub_eq_add_neg] using h
  · intro s
    unfold Pr
    have : ∀ y : G n, ⟪dt u 0 y.val, v s y.val⟫_ℂ = 0 := fun y => by
      rw [dt_zero hu (val_mem_GLs y), inner_zero_left]
    simp [this]
  · intro t
    unfold Pr
    have : ∀ y : G n, ⟪u t y.val, dt v 0 y.val⟫_ℂ = 0 := fun y => by
      rw [dt_zero hv (val_mem_GLs y), inner_zero_right]
    simp [this]

end GlobalTheory.CompanionTheory.WaveMult.WaveSymm
end
end

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_pairing_time_symmetry : LgFacts → RCalc → WaveSpeed → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) → ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WaveMult.wave_symm
end

section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_operator_preserves_wave : RCalc → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w : List (Bool × ℕ)), IsWave E u → IsWave E (fun t => zOp w (u t)) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp | exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp <;> assumption)
end

section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_operator_commutes_integral : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T → ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | exact GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg <;> assumption)
end

section
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem continuousOn_inv_GLs {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have h : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuous_id.matrix_det).continuousOn.inv₀ (fun y hy => hy)).smul
    (continuous_id.matrix_adjugate).continuousOn

theorem unitary_matrix_inv {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (k.1 : Mat n)⁻¹ = (k⁻¹).1 := by
  apply Matrix.inv_eq_left_inv
  have := congrArg Subtype.val (inv_mul_cancel k)
  simpa using this

theorem adjoint_rho_inv {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let f : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →L[ℂ] E.V).toLinearMap, E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ y) = y := by
    have : E.ρ k * E.ρ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun T : E.V →L[ℂ] E.V => T y) this
  have h2 := f.inner_map_map x (E.ρ k⁻¹ y)
  have h3 : f (E.ρ k⁻¹ y) = y := h1
  rw [h3] at h2
  exact h2

theorem adjoint_kernel_reg : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  intro hL n E k hk heq
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨hc, R, hR⟩ := hk
  refine ⟨⟨?_, R, ?_⟩, ?_⟩
  · have hinv : ContinuousOn (fun y : Mat n => k y⁻¹) (GLs n) :=
      hc.comp continuousOn_inv_GLs (fun y hy => inv_mem_GLs hy)
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E.V) (F := E.V)).continuous.comp_continuousOn hinv
  · intro y hy hlt
    have h1 : lg y⁻¹ = lg y := (hL n).2.1 y hy
    have h2 : k y⁻¹ = 0 := hR _ (inv_mem_GLs hy) (by rw [h1]; exact hlt)
    simp [h2]
  · intro y hy k₁ k₂
    have h1 : ((k₁.1 : Mat n) * y * k₂.1)⁻¹ = (k₂⁻¹).1 * y⁻¹ * (k₁⁻¹).1 := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, unitary_matrix_inv, unitary_matrix_inv, mul_assoc]
    rw [h1, heq _ (inv_mem_GLs hy)]
    have h2 : ContinuousLinearMap.adjoint (E.ρ k₂⁻¹ * k y⁻¹ * E.ρ k₁⁻¹)
        = ContinuousLinearMap.adjoint (E.ρ k₁⁻¹) * ContinuousLinearMap.adjoint (k y⁻¹)
          * ContinuousLinearMap.adjoint (E.ρ k₂⁻¹) := by
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      rfl
    rw [h2, adjoint_rho_inv, adjoint_rho_inv]

end GlobalTheory.CompanionTheory.WaveMult
end
end

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_adjoint_regular : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg
end

section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_time_average_is_wave : WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ), IsWave E u → IsBump g T → IsWave E (fun t x => ∫ s, (g s : ℂ) • u (t + s) x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | exact GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg <;> assumption)
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.KerAdj

variable {n : ℕ}

theorem cpt_zOp (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × ℕ)) {f : Mat n → V} (hf : Cpt f) : Cpt (zOp w f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun y hy hlt => ?_⟩
  have hO : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) :=
    (hL n).2.2.2.1.continuousOn.isOpen_inter_preimage (GlobalTheory.CompanionTheory.WaveKer.isOpen_GLs n) isOpen_Ioi
  have h0 : f =ᶠ[𝓝 y] 0 := by
    filter_upwards [hO.mem_nhds ⟨hy, hlt⟩] with x hx
    exact hR x hx.1 hx.2
  exact (GlobalTheory.CompanionTheory.WaveKer.zOp_germ w h0).self_of_nhds

theorem cont_val {W : Type} [TopologicalSpace W] {φ : Mat n → W} (hφ : ContinuousOn φ (GLs n)) :
    Continuous fun y : G n => φ y.val :=
  hφ.comp_continuous Units.continuous_val PairAdj.val_mem_GLs

section Pair

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem pair_integrable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (hL : LgFacts) {a b : Mat n → V} (ha : ContinuousOn a (GLs n))
    (hb : ContinuousOn b (GLs n)) (cb : Cpt b) :
    Integrable (fun y : G n => ⟪a y.val, b y.val⟫_ℂ) μ := by
  obtain ⟨R, hR⟩ := cb
  refine Continuous.integrable_of_hasCompactSupport ((cont_val ha).inner (cont_val hb)) ?_
  refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => ?_
  simp [hR _ (PairAdj.val_mem_GLs y) (not_le.1 hy)]

theorem pair_avg {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hL : LgFacts) {a : Mat n → V} {W : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ}
    (ha : ContinuousOn a (GLs n)) (ca : Cpt a)
    (hW : ContinuousOn (Function.uncurry W) (Set.univ ×ˢ GLs n)) (hg : IsBump g T) :
    ∫ y : G n, ⟪a y.val, ∫ t, (g t : ℂ) • W t y.val⟫_ℂ ∂μ
      = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪a y.val, W t y.val⟫_ℂ ∂μ := by
  have hc : ∀ R, IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1
  haveI : SigmaFinite μ := ⟨⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun _ => trivial,
    fun m => (hc m).measure_lt_top,
    Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (exists_nat_ge (lg y.val))⟩⟩⟩
  obtain ⟨R, hR⟩ := ca
  have hgc : Continuous fun t : ℝ => (g t : ℂ) := Complex.continuous_ofReal.comp hg.1.continuous
  have hWc : Continuous fun p : G n × ℝ => W p.2 p.1.val := by
    have h1 : Continuous fun p : G n × ℝ => ((p.2, p.1.val) : ℝ × Mat n) :=
      continuous_snd.prodMk (Units.continuous_val.comp continuous_fst)
    exact hW.comp_continuous h1 (fun p => ⟨Set.mem_univ _, PairAdj.val_mem_GLs _⟩)
  have hgz : ∀ t, t ∉ Set.Icc (-T) T → (g t : ℂ) = 0 := by
    intro t ht
    have h1 : T < |t| := by
      by_contra h
      exact ht (abs_le.1 (not_lt.1 h))
    simp [hg.2.2 t h1]
  have i1 : ∀ y : G n, Integrable (fun t => (g t : ℂ) • W t y.val) volume := by
    intro y
    refine Continuous.integrable_of_hasCompactSupport
      (hgc.smul (hWc.comp (Continuous.prodMk_right y))) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_
    simp [hgz t ht]
  have j : Integrable (Function.uncurry fun (y : G n) (t : ℝ) =>
      ⟪a y.val, (g t : ℂ) • W t y.val⟫_ℂ) (μ.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((cont_val ha).comp continuous_fst).inner ((hgc.comp continuous_snd).smul hWc)
    · refine HasCompactSupport.intro ((hc R).prod (isCompact_Icc (a := -T) (b := T))) fun p hp => ?_
      by_cases h1 : lg p.1.val ≤ R
      · have h2 : p.2 ∉ Set.Icc (-T) T := fun h2 => hp ⟨h1, h2⟩
        simp [Function.uncurry, hgz _ h2]
      · simp [Function.uncurry, hR _ (PairAdj.val_mem_GLs p.1) (not_le.1 h1)]
  calc _ = ∫ y : G n, ∫ t, ⟪a y.val, (g t : ℂ) • W t y.val⟫_ℂ ∂volume ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact (integral_inner (i1 y) (a y.val)).symm
    _ = ∫ t, ∫ y : G n, ⟪a y.val, (g t : ℂ) • W t y.val⟫_ℂ ∂μ ∂volume :=
        integral_integral_swap j
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [inner_smul_right]
        exact integral_const_mul _ _

end Pair

section Chain

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem term_eq (hL : LgFacts) (hR : RCalc) (hS : WaveSpeed) {E : KMod n}
    {w' : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {K' : Mat n → (E.V →L[ℂ] E.V)}
    (hb : IsBump g T) (hK : IsKer μ E w' g K') {f h : Mat n → E.V} {u v : ℝ → Mat n → E.V}
    (hu : IsWave E u) (hv : IsWave E v) (hu0 : ∀ y ∈ GLs n, u 0 y = f y)
    (hv0 : ∀ y ∈ GLs n, v 0 y = h y) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪zOp w' f y.val, ∫ t, (g t : ℂ) • v t y.val⟫_ℂ ∂μ
      = ∫ y : G n, ⟪act μ E K' f y.val, h y.val⟫_ℂ ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hui : IsWave E (fun t => zOp w' (u t)) := GlobalTheory.T.center_operator_preserves_wave hR n E u w' hu
  have cu0 : Cpt (u 0) := by
    obtain ⟨R, hR'⟩ := cf
    exact ⟨R, fun y hy hl => by rw [hu0 y hy]; exact hR' y hy hl⟩
  have cv0 : Cpt (v 0) := by
    obtain ⟨R, hR'⟩ := ch
    exact ⟨R, fun y hy hl => by rw [hv0 y hy]; exact hR' y hy hl⟩
  have cui0 : Cpt ((fun t => zOp w' (u t)) 0) := cpt_zOp hL w' cu0
  have c1 : ContinuousOn ((fun t => zOp w' (u t)) 0) (GLs n) := (hui.2.1 0).1.continuousOn
  have c2 : ContinuousOn (v 0) (GLs n) := (hv.2.1 0).1.continuousOn
  have L : ∫ y : G n, ⟪zOp w' f y.val, ∫ t, (g t : ℂ) • v t y.val⟫_ℂ ∂μ
      = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪zOp w' (u t) y.val, v 0 y.val⟫_ℂ ∂μ := by
    calc _ = ∫ y : G n, ⟪zOp w' (u 0) y.val, ∫ t, (g t : ℂ) • v t y.val⟫_ℂ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          rw [zOp_agree_GLs n w' (u 0) f hu0 _ (PairAdj.val_mem_GLs y)]
      _ = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪zOp w' (u 0) y.val, v t y.val⟫_ℂ ∂μ :=
          pair_avg μ hL c1 cui0 hv.1.continuousOn hb
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only
          rw [GlobalTheory.T.wave_pairing_time_symmetry hL hR hS n μ E _ v hui hv cui0 cv0 t]
  have Rr : ∫ y : G n, ⟪act μ E K' f y.val, h y.val⟫_ℂ ∂μ
      = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪zOp w' (u t) y.val, v 0 y.val⟫_ℂ ∂μ := by
    have hF := pair_avg μ hL c2 cv0 hui.1.continuousOn hb
    calc _ = ∫ y : G n, ⟪∫ t, (g t : ℂ) • zOp w' (u t) y.val, v 0 y.val⟫_ℂ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          have hy := PairAdj.val_mem_GLs y
          have e1 : act μ E K' f y.val = act μ E K' (u 0) y.val := by
            simp only [act]
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only
            rw [hu0 _ (GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (PairAdj.val_mem_GLs z))]
          simp only
          rw [e1, hK.2.2.2 u hu _ hy, GlobalTheory.T.center_operator_commutes_integral n u g T w' hu.1 hb _ hy, hv0 _ hy]
      _ = conj (∫ y : G n, ⟪v 0 y.val, ∫ t, (g t : ℂ) • zOp w' (u t) y.val⟫_ℂ ∂μ) := by
          rw [← integral_conj]
          simp only [inner_conj_symm]
      _ = conj (∫ t, (g t : ℂ) * ∫ y : G n, ⟪v 0 y.val, zOp w' (u t) y.val⟫_ℂ ∂μ) := by
          rw [hF]
      _ = _ := by
          rw [← integral_conj]
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only
          rw [map_mul, Complex.conj_ofReal, ← integral_conj]
          simp only [inner_conj_symm]
  rw [L, Rr]

theorem chain (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hS : WaveSpeed) (hE : WaveEx) {E : KMod n}
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (E.V →L[ℂ] E.V)}
    (hb : IsBump g T) (hk : IsKer μ E w g k) {N : ℕ} {c : Fin N → ℂ}
    {w₁ : Fin N → List (Bool × ℕ)} {K : Fin N → Mat n → (E.V →L[ℂ] E.V)}
    (hw : ∀ a b : Mat n → E.V, ContDiffOn ℝ ∞ a (GLs n) → ContDiffOn ℝ ∞ b (GLs n) → Cpt a → Cpt b →
      ∫ y : G n, ⟪zOp w a y.val, b y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪a y.val, zOp (w₁ i) b y.val⟫_ℂ ∂μ)
    (hK : ∀ i, IsKer μ E (w₁ i) g (K i)) {f h : Mat n → E.V} (hf : f ∈ CE E) (cf : Cpt f)
    (hh : h ∈ CE E) (ch : Cpt h) :
    (haveI := FiniteDimensional.complete ℂ E.V
     ∫ y : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val, h y.val⟫_ℂ ∂μ
      = ∑ i, conj (c i) * ∫ y : G n, ⟪act μ E (K i) f y.val, h y.val⟫_ℂ ∂μ) := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨u, hu, hu0⟩ := hE n E f hf
  obtain ⟨v, hv, hv0⟩ := hE n E h hh
  have hHs : ContDiffOn ℝ ∞ (fun x => ∫ t, (g t : ℂ) • v t x) (GLs n) := by
    have h1 := ((GlobalTheory.T.wave_time_average_is_wave hS n E v g T hv hb).2.1 0).1
    simpa only [zero_add] using h1
  have cv0 : Cpt (v 0) := by
    obtain ⟨R, hR'⟩ := ch
    exact ⟨R, fun y hy hl => by rw [hv0 y hy]; exact hR' y hy hl⟩
  have cH : Cpt (fun x => ∫ t, (g t : ℂ) • v t x) := by
    obtain ⟨R, hRv⟩ := wave_cpt_bounded_time hL hS n E v hv cv0 T
    refine ⟨R, fun y hy hl => ?_⟩
    have h0 : ∀ t, (g t : ℂ) • v t y = 0 := by
      intro t
      by_cases ht : |t| ≤ T
      · rw [hRv t ht y hy hl, smul_zero]
      · rw [hb.2.2 t (not_le.1 ht)]
        simp
    simp [h0]
  have e1 := PairAdj.pairAdj hL hU n μ E k f h ⟨hk.1.continuousOn, hk.2.1⟩ hf.1.continuousOn
    hh.1.continuousOn cf ch
  have e2 : ∫ y : G n, ⟪f y.val, act μ E k h y.val⟫_ℂ ∂μ
      = ∫ y : G n, ⟪f y.val, zOp w (fun x => ∫ t, (g t : ℂ) • v t x) y.val⟫_ℂ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hy := PairAdj.val_mem_GLs y
    have e : act μ E k h y.val = act μ E k (v 0) y.val := by
      simp only [act]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      rw [hv0 _ (GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (PairAdj.val_mem_GLs z))]
    simp only
    rw [e, hk.2.2.2 v hv _ hy]
  have e3 : ∫ y : G n, ⟪f y.val, zOp w (fun x => ∫ t, (g t : ℂ) • v t x) y.val⟫_ℂ ∂μ
      = conj (∫ y : G n, ⟪zOp w (fun x => ∫ t, (g t : ℂ) • v t x) y.val, f y.val⟫_ℂ ∂μ) := by
    rw [← integral_conj]
    simp only [inner_conj_symm]
  rw [e1, e2, e3, hw _ f hHs hf.1 cH cf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← term_eq μ hL hR hS hb (hK i) hu hv hu0 hv0 cf ch, ← integral_conj]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_conj_symm]

end Chain

theorem kernel_adjoint : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E w g k → ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)) (K : Fin N → Mat n → (E.V →L[ℂ] E.V)), (∀ i, IsKer μ E (w₁ i) g (K i)) ∧ (haveI := FiniteDimensional.complete ℂ E.V; ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = ∑ i, c i • K i y) ∧ ∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ := by
  intro hL hU hR hS hE hQ hO n _ _ μ _ E w g T k hb hk
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨N, c, w₁, hval, hop⟩ := GlobalTheory.T.gelfand_operator_pairing_adjoint n w
  choose K hK using fun i => hO n μ E (w₁ i) g T hb
  refine ⟨N, c, w₁, K, hK, ?_, hval⟩
  have hw := hop hL hR μ E.V
  obtain ⟨regp, eqvp⟩ := GlobalTheory.T.kernel_adjoint_regular hL n E k ⟨hk.1.continuousOn, hk.2.1⟩ hk.2.2.1
  have regK : ∀ i, KReg (K i) := fun i => ⟨(hK i).1.continuousOn, (hK i).2.1⟩
  have rp : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (y * k₂.1)⁻¹) = ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂ := by
    intro y hy k₂
    simpa using eqvp y hy 1 k₂
  have lp : ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (k₁.1 * y)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) := by
    intro y hy k₁
    simpa using eqvp y hy k₁ 1
  have rK : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K i (y * k₂.1) = K i y * E.ρ k₂ := by
    intro i y hy k₂
    simpa using (hK i).2.2.1 y hy 1 k₂
  have lK : ∀ i, ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, K i (k₁.1 * y) = E.ρ k₁ * K i y := by
    intro i y hy k₁
    simpa using (hK i).2.2.1 y hy k₁ 1
  have hD : ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y = 0 := by
    refine hQ n μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) (GLs n)
      (GlobalTheory.CompanionTheory.WaveKer.isOpen_GLs n) subset_rfl
      (fun y hy k₂ => GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₂)) ?_ ?_ ?_
    · exact regp.1.sub (continuousOn_finset_sum _ fun i _ => (regK i).1.const_smul (c i))
    · intro y hy k₂
      simp only [rp y hy k₂, rK _ y hy k₂, sub_mul, Finset.sum_mul, smul_mul_assoc]
    · intro f hf cf _
      have hfc := hf.1.continuousOn
      have ap := GlobalTheory.T.kernel_action_equivariant hL n μ E _ f regp hfc lp
      have aK := fun i => GlobalTheory.T.kernel_action_equivariant hL n μ E (K i) f (regK i) hfc (lK i)
      have hA0 := section_orth_cpt_zero hQ n μ E
        (fun x => act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x - ∑ i, c i • act μ E (K i) f x)
        (ap.1.sub (continuousOn_finset_sum _ fun i _ => (aK i).1.const_smul (c i)))
        (by
          intro y hy k₂
          simp only [ap.2 y hy k₂, (aK _).2 y hy k₂, map_sub, map_sum, map_smul])
        (by
          intro h hh ch
          have int1 := pair_integrable μ hL ap.1 hh.1.continuousOn ch
          have int2 := fun i => (pair_integrable μ hL (aK i).1 hh.1.continuousOn ch).const_mul (conj (c i))
          have hpt : ∀ y : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val - ∑ i, c i • act μ E (K i) f y.val, h y.val⟫_ℂ
              = ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val, h y.val⟫_ℂ
                - ∑ i, conj (c i) * ⟪act μ E (K i) f y.val, h y.val⟫_ℂ := by
            intro y
            simp only [inner_sub_left, sum_inner, inner_smul_left]
          simp only [hpt]
          rw [integral_sub int1 (integrable_finset_sum _ fun i _ => int2 i),
            integral_finset_sum _ fun i _ => int2 i]
          simp only [integral_const_mul]
          rw [chain μ hL hU hR hS hE hb hk hw hK hf cf hh ch, sub_self])
      have h1 := hA0 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      have h2 := act_eq_sum_of_kernel hL n μ E (ι := Option (Fin N))
        (fun o => o.elim 1 fun i => -c i)
        (fun o => o.elim (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) K)
        (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) f
        (by rintro (_ | i); exacts [regp, regK i])
        (by intro y _; simp [Fintype.sum_option, sub_eq_add_neg])
        hfc 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      rw [h2]
      simpa [Fintype.sum_option, sub_eq_add_neg] using h1
  intro y hy
  exact sub_eq_zero.1 (hD y hy)

end GlobalTheory.CompanionTheory.WaveMult.KerAdj
end
end
