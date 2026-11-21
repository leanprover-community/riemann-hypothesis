import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdOfFnEqSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqMatrixCoeffOfLocallyUniformLimitKFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoeffSeriesOfKTypeProjections

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.SecondKindChart

section Norm
open scoped Matrix.Norms.Operator ContDiff

variable {n : ℕ}

theorem ofFn_prod_single {M : Type*} [Monoid M] : ∀ {d : ℕ} (g : Fin d → M) (j : Fin d),
    (∀ i, i ≠ j → g i = 1) → (List.ofFn g).prod = g j := by
  first
  | exact @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | (apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single ..)

def lc {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (b i)

theorem lc_apply {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (v : Fin d → ℝ) : lc b v = ∑ i, v i • b i := by
  simp [lc, ContinuousLinearMap.sum_apply]

theorem expProd_line {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin d) (r : ℝ) :
    (List.ofFn fun i => NormedSpace.exp ((r • Pi.single j (1 : ℝ) : Fin d → ℝ) i • b i)).prod =
      NormedSpace.exp (r • b j) := by
  rw [ofFn_prod_single _ j]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

theorem hasStrictFDerivAt_expProd {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (fun s : Fin d → ℝ => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod) (lc b) 0 := by
  set f := fun s : Fin d → ℝ => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod with hfdef
  have hcd : ContDiff ℝ ∞ f := GlobalTheory.GardingVec.contDiff_expProd b
  have hs : HasStrictFDerivAt f (fderiv ℝ f 0) 0 := hcd.contDiffAt.hasStrictFDerivAt (by simp)
  suffices e : fderiv ℝ f 0 = lc b by rwa [e] at hs
  have hD : HasFDerivAt f (fderiv ℝ f 0) 0 := hs.hasFDerivAt
  have hj : ∀ j : Fin d, fderiv ℝ f 0 (Pi.single j 1) = b j := by
    intro j
    have h1 : HasDerivAt (fun r : ℝ => f (r • Pi.single j (1 : ℝ))) (fderiv ℝ f 0 (Pi.single j 1)) 0 := by
      have hl : HasDerivAt (fun r : ℝ => r • (Pi.single j (1 : ℝ) : Fin d → ℝ)) ((1 : ℝ) • Pi.single j 1) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const _
      rw [one_smul] at hl
      exact hD.comp_hasDerivAt_of_eq 0 hl (by simp)
    have h2 : HasDerivAt (fun r : ℝ => f (r • Pi.single j (1 : ℝ))) (b j) 0 := by
      have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (b j) (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
      exact expProd_line b j r
    exact h1.unique h2
  ext1 v
  rw [pi_eq_sum_univ v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun k => if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext k; simp [Pi.single_apply, eq_comm]
  rw [e1, map_smul, map_smul, hj, lc_apply]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_apply, hi]
  · simp

end Norm

section Chart
open scoped Matrix.Norms.Operator ContDiff

theorem exp_product_chart_local (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ lieSet ε)
    (hli : LinearIndependent ℝ b) (hsp : ∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) (c : Fin d → ℝ) :
    ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  classical
  set A : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ := lc b with hA
  have hAinj : LinearMap.ker (A : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : ∑ i, x i • b i = 0 := by rw [← lc_apply]; exact hx
    funext i
    exact Fintype.linearIndependent_iff.1 hli x hx' i
  obtain ⟨C, hC⟩ := LinearMap.exists_leftInverse_of_injective _ hAinj
  let Cc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap C
  have hCA : ∀ v, Cc (A v) = v := fun v => LinearMap.congr_fun hC v
  set f : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun s => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod with hfdef
  have hf : HasStrictFDerivAt f A 0 := hasStrictFDerivAt_expProd b
  have hf0 : f 0 = 1 := by simp [hfdef]
  have hlog : HasStrictFDerivAt (Formalism.MainNotions.S.Gauge.logM n) (ContinuousLinearMap.id ℝ _) (f 0) := by
    have h := (Formalism.MainNotions.S.Gauge.hasStrict_expM (n := n)).to_localInverse
    rw [NormedSpace.exp_zero] at h
    rw [hf0]
    exact h
  set ψ : (Fin d → ℝ) → (Fin d → ℝ) := fun s => Cc (Formalism.MainNotions.S.Gauge.logM n (f s)) with hψdef
  have hψ : HasStrictFDerivAt ψ ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
    have h := Cc.hasStrictFDerivAt.comp (0 : Fin d → ℝ) (hlog.comp (0 : Fin d → ℝ) hf)
    have e : (Cc.comp ((ContinuousLinearMap.id ℝ (Formalism.MainNotions.S.Gauge.MxC n)).comp A)) =
        ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) := by
      ext1 v
      simp [hCA]
    exact h.congr_fderiv e
  have hψ0 : ψ 0 = 0 := by simp [hψdef, hf0, Formalism.MainNotions.S.Gauge.logM_one]
  set g := hψ.localInverse ψ _ 0 with hgdef
  have hg : HasFDerivAt g (((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)).symm : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (ψ 0) := hψ.to_localInverse.hasFDerivAt
  have hg0 : g (ψ 0) = 0 := hψ.localInverse_apply_image
  refine ⟨fun t => g (t • c), ?_, ?_, ?_⟩
  · simp only [zero_smul]; simpa [hψ0] using hg0
  · have hl : HasDerivAt (fun t : ℝ => t • c) ((1 : ℝ) • c) 0 := (hasDerivAt_id (0 : ℝ)).smul_const _
    rw [one_smul] at hl
    have := hg.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp [hψ0])
    exact this
  ·
    have hlin : Filter.Tendsto (fun t : ℝ => t • c) (nhds 0) (nhds (ψ 0)) := by
      exact (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto' 0 (ψ 0) (by simp [hψ0])
    have E1 : ∀ᶠ t in nhds (0 : ℝ), ψ (g (t • c)) = t • c := hlin.eventually hψ.eventually_right_inverse
    have hτc : ContinuousAt (fun t : ℝ => g (t • c)) 0 := by
      exact hg.continuousAt.comp_of_eq
        (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).continuousAt (by simp [hψ0])
    have hfc : ContinuousAt (fun t : ℝ => f (g (t • c))) 0 :=
      (GlobalTheory.GardingVec.contDiff_expProd b).continuous.continuousAt.comp hτc
    have E2 : ∀ᶠ t in nhds (0 : ℝ), f (g (t • c)) ∈ Formalism.MainNotions.S.Gauge.tOne ε := by
      apply hfc.preimage_mem_nhds
      have h0 : f (g ((0 : ℝ) • c)) = 1 := by simp only [zero_smul]; rw [← hψ0, hg0, hf0]
      rw [h0]
      exact (Formalism.MainNotions.S.Gauge.isOpen_tOne ε).mem_nhds (Formalism.MainNotions.S.Gauge.one_mem_tOne ε)
    filter_upwards [E1, E2] with t h1 h2
    set y := f (g (t • c)) with hy
    have hU : Formalism.REAL.inUJ ε y := by
      have := GlobalTheory.LowTypeDetermined.expProd_mem (GlobalTheory.TypeSum.isUnit_Jm ε) (Xs := b) (fun i => hb i) (g (t • c))
      exact this
    obtain ⟨hG, hE⟩ := Formalism.MainNotions.S.Gauge.logM_inG h2 hU
    obtain ⟨c', hc'⟩ := hsp _ hG
    have hc'A : Formalism.MainNotions.S.Gauge.logM n y = A c' := by rw [hc', hA, lc_apply]
    have hψy : ψ (g (t • c)) = c' := by
      show Cc (Formalism.MainNotions.S.Gauge.logM n y) = c'
      rw [hc'A, hCA]
    have hcc : c' = t • c := by rw [← hψy, h1]
    have hL : Formalism.MainNotions.S.Gauge.logM n y = t • ∑ i, c i • b i := by
      rw [hc'A, hcc, map_smul, hA, lc_apply]
    rw [← hL, hE]

end Chart

theorem exp_eq_expProd_near_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod :=
  fun n ε d b hb hli hsp c => exp_product_chart_local n ε d b hb hli hsp c

end GlobalTheory.SecondKindChart
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_second_kind_coordinates : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  atlas_forward_decl GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem FamGrowth.bdd_of_isCompact {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hG : FamGrowth ε N F)
    {w : List (Mx n)} (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {K : Set (Mx n)} (hK : IsCompact K) (hKU : K ⊆ UJset ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ‖F w y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hG w hw
  obtain ⟨M, hM⟩ := hK.bddAbove_image continuous_hs.continuousOn
  refine ⟨|C| * (1 + max M 0) ^ N, by positivity, fun y hy => ?_⟩
  have h1 : hs y ≤ max M 0 := (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  have h0 : 0 ≤ hs y := hs_nonneg y
  calc ‖F w y‖ ≤ C * (1 + hs y) ^ N := hC y (hKU hy)
    _ ≤ |C| * (1 + hs y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (1 + max M 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (abs_nonneg C)

def expSweep (K : Set (Mx n)) (X : Mx n) : Set (Mx n) :=
  (fun p : Mx n × ℝ => p.1 * NormedSpace.exp (p.2 • X)) '' (K ×ˢ Set.Icc (-1 : ℝ) 1)

theorem isCompact_expSweep {K : Set (Mx n)} (hK : IsCompact K) (X : Mx n) : IsCompact (expSweep K X) :=
  (hK.prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image
    (continuous_fst.matrix_mul ((continuous_exp_smul X).comp continuous_snd))
theorem expSweep_sub {K : Set (Mx n)} (hKU : K ⊆ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    expSweep K X ⊆ UJset ε := by
  rintro _ ⟨⟨z, s⟩, ⟨hz, -⟩, rfl⟩
  exact mul_mem_UJ (hKU hz) (exp_mem_UJ hX s)

theorem mem_expSweep {K : Set (Mx n)} {z : Mx n} (hz : z ∈ K) (X : Mx n) {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    z * NormedSpace.exp (s • X) ∈ expSweep K X := ⟨(z, s), ⟨hz, hs⟩, rfl⟩

theorem exp_zero_smul_mx (X : Mx n) : NormedSpace.exp ((0 : ℝ) • X) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

theorem IsDerFam.norm_sub_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z‖ ≤ B * |t| := by
  have h := norm_sub_le_of_deriv_Icc (f := fun s => F w (z * NormedSpace.exp (s • X)))
    (fun s => hF.hasDerivAt_exp hw hX hz s) zero_le_one hB (t := t) (abs_le.1 ht)
  simpa only [exp_zero_smul_mx, Matrix.mul_one] using h

theorem IsDerFam.norm_taylor_exp_le {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {w : List (Mx n)}
    (hw : ∀ Y ∈ w, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F (X :: X :: w) (z * NormedSpace.exp (s • X))‖ ≤ B) {t : ℝ} (ht : |t| ≤ 1) :
    ‖F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z‖ ≤ B * t ^ 2 := by
  have hXw : ∀ Y ∈ X :: w, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hw Y hY]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|,
      ‖F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z‖ ≤ B * |t| := by
    intro s hs
    have hs1 : |s| ≤ |t| := abs_le.2 hs
    exact (hF.norm_sub_exp_le hXw hX hz hB (hs1.trans ht)).trans (mul_le_mul_of_nonneg_left hs1 hB0)
  have hd : ∀ s, HasDerivAt (fun s : ℝ => F w (z * NormedSpace.exp (s • X)) - s • F (X :: w) z)
      (F (X :: w) (z * NormedSpace.exp (s • X)) - F (X :: w) z) s := by
    intro s
    have := (hF.hasDerivAt_exp hw hX hz s).fun_sub ((hasDerivAt_id s).smul_const (F (X :: w) z))
    simpa only [id, one_smul] using this
  have h := norm_sub_le_of_deriv_Icc hd (abs_nonneg t) h1 (t := t) ⟨neg_abs_le t, le_abs_self t⟩
  simp only [exp_zero_smul_mx, Matrix.mul_one, zero_smul, sub_zero, NormedSpace.exp_zero] at h
  have e : F w (z * NormedSpace.exp (t • X)) - F w z - t • F (X :: w) z =
      F w (z * NormedSpace.exp (t • X)) - t • F (X :: w) z - F w z := by abel
  rw [e]
  calc _ ≤ B * |t| * |t| := h
    _ = B * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem lie_cons {Y : Mx n} {w : List (Mx n)} (hY : Y ∈ lieSet ε) (hw : ∀ Z ∈ w, Z ∈ lieSet ε) :
    ∀ Z ∈ Y :: w, Z ∈ lieSet ε := by
  intro Z hZ
  rcases List.mem_cons.1 hZ with rfl | hZ
  exacts [hY, hw Z hZ]

theorem IsDerFam.taylor_prod {N : ℕ} {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) (hG : FamGrowth ε N F)
    {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) : ∀ (d : ℕ) (b : Fin d → Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ K : Set (Mx n), IsCompact K → K ⊆ UJset ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ t : Fin d → ℝ, ‖t‖ ≤ 1 →
      ‖F l (z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod) - F l z - ∑ i, t i • F (b i :: l) z‖ ≤
        C * ‖t‖ ^ 2 := by
  intro d
  induction d with
  | zero =>
    intro b hb K hK hKU
    refine ⟨0, le_rfl, fun z _ t _ => ?_⟩
    simp
  | succ d ih =>
    intro b hb K hK hKU
    have hX := hb 0
    have hK' := isCompact_expSweep hK (b 0)
    have hK'U := expSweep_sub hKU hX
    obtain ⟨C', hC'0, hC'⟩ := ih (fun i => b i.succ) (fun i => hb _) _ hK' hK'U
    obtain ⟨B0, hB00, hB0⟩ := hG.bdd_of_isCompact (lie_cons hX (lie_cons hX hl)) hK' hK'U
    have hBi : ∀ i : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ expSweep K (b 0), ‖F (b 0 :: b i.succ :: l) y‖ ≤ B :=
      fun i => hG.bdd_of_isCompact (lie_cons hX (lie_cons (hb _) hl)) hK' hK'U
    choose B hBnn hB using hBi
    have hBs : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hBnn i
    refine ⟨C' + ∑ i, B i + B0, by positivity, fun z hz t ht => ?_⟩
    have hzU := hKU hz
    have hti : ∀ i, |t i| ≤ ‖t‖ := fun i => by simpa using norm_le_pi_norm t i
    have ht0 : t 0 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 ((hti 0).trans ht)
    have ht' : ‖(fun i : Fin d => t i.succ)‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun i => norm_le_pi_norm t i.succ
    have hz1 := mem_expSweep hz (b 0) ht0
    have hprod : z * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod =
        z * NormedSpace.exp (t 0 • b 0) * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod := by
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_assoc]
    rw [hprod, Fin.sum_univ_succ]
    set z1 := z * NormedSpace.exp (t 0 • b 0) with hz1def
    have h1 := hC' z1 hz1 (fun i => t i.succ) (ht'.trans ht)
    have h2 : ‖∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z)‖ ≤ (∑ i, B i) * ‖t‖ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      have hd := hF.norm_sub_exp_le (lie_cons (hb i.succ) hl) hX hzU
        (fun s hs => hB i _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
      calc |t i.succ| * ‖F (b i.succ :: l) z1 - F (b i.succ :: l) z‖ ≤ ‖t‖ * (B i * ‖t‖) :=
            mul_le_mul (hti _) (hd.trans (mul_le_mul_of_nonneg_left (hti 0) (hBnn i))) (norm_nonneg _)
              (norm_nonneg _)
        _ = B i * ‖t‖ ^ 2 := by ring
    have h3 := hF.norm_taylor_exp_le hl hX hzU (fun s hs => hB0 _ (mem_expSweep hz (b 0) hs)) (abs_le.2 ht0)
    have h3' : B0 * t 0 ^ 2 ≤ B0 * ‖t‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hB00
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hti 0) 2
    have h1' : C' * ‖(fun i : Fin d => t i.succ)‖ ^ 2 ≤ C' * ‖t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) hC'0
    have e : F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z -
        (t 0 • F (b 0 :: l) z + ∑ i : Fin d, t i.succ • F (b i.succ :: l) z) =
        (F l (z1 * (List.ofFn fun i : Fin d => NormedSpace.exp (t i.succ • b i.succ)).prod) - F l z1 -
          ∑ i : Fin d, t i.succ • F (b i.succ :: l) z1) +
        ∑ i : Fin d, t i.succ • (F (b i.succ :: l) z1 - F (b i.succ :: l) z) +
        (F l z1 - F l z - t 0 • F (b 0 :: l) z) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine (norm_add₃_le).trans ?_
    have : (C' + ∑ i, B i + B0) * ‖t‖ ^ 2 = C' * ‖t‖ ^ 2 + (∑ i, B i) * ‖t‖ ^ 2 + B0 * ‖t‖ ^ 2 := by ring
    rw [this]
    exact add_le_add_three (h1.trans h1') h2 (h3.trans h3')

theorem hasFDerivAt_derFam_prodExp : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  intro n ε N F hF hG l hl d b hb g hg
  obtain ⟨C, -, hC⟩ := hF.taylor_prod hG hl d b hb {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have e0 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • b i)).prod = 1 := by
    simp [List.prod_ofFn]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℝ) one_pos] with h hh
  rw [mem_closedBall_zero_iff] at hh
  simp only [zero_add, e0, Matrix.mul_one, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_pow, norm_norm]
  exact hC g rfl h hh

end GlobalTheory.TypeSum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  atlas_forward_decl GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem derFam_expand_words : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n) (c : Fin d → GlobalTheory.TypeSum.Mx n → ℝ), (∀ i, b i ∈ lieSet ε) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g) →
    ∀ (m : ℕ) (Y : Fin m → GlobalTheory.TypeSum.Mx n), (∀ j, Y j ∈ lieSet ε) → ∀ g ∈ UJset ε,
      F (List.ofFn Y) g = ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j) : ℂ)) * F (List.ofFn fun j => b (J j)) g := by
  intro n ε F hF d b c hb hlin m
  induction m with
  | zero =>
    intro Y _ g _
    simp
  | succ m ih =>
    intro Y hY g hg
    have hwb : ∀ J : Fin m → Fin d, ∀ Z ∈ List.ofFn (fun j => b (J j)), Z ∈ lieSet ε := by
      intro J Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hb _
    have hwY : ∀ Z ∈ List.ofFn (fun j : Fin m => Y j.succ), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hY _
    have key : ∀ i, F (b i :: List.ofFn (fun j : Fin m => Y j.succ)) g =
        ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g := by
      intro i
      have h1 := hF (List.ofFn fun j : Fin m => Y j.succ) hwY (b i) (hb i) g hg
      have h2 : HasDerivAt (fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
          F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)))
          (∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g) 0 := by
        apply HasDerivAt.fun_sum
        intro J _
        exact (hF _ (hwb J) (b i) (hb i) g hg).const_mul _
      have heq : (fun t : ℝ => F (List.ofFn fun j : Fin m => Y j.succ) (g * NormedSpace.exp (t • b i))) =
          fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
            F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)) := by
        funext t
        exact ih (fun j => Y j.succ) (fun j => hY _) _ (mul_mem_UJ hg (exp_mem_UJ (hb i) t))
      rw [heq] at h1
      exact h1.unique h2
    rw [List.ofFn_succ, hlin _ hwY (Y 0) (hY 0) g hg]
    simp_rw [key, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

end GlobalTheory.TypeSum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n) (c : Fin d → GlobalTheory.TypeSum.Mx n → ℝ), (∀ i, b i ∈ lieSet ε) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g) →
    ∀ (m : ℕ) (Y : Fin m → GlobalTheory.TypeSum.Mx n), (∀ j, Y j ∈ lieSet ε) → ∀ g ∈ UJset ε,
      F (List.ofFn Y) g = ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j) : ℂ)) * F (List.ofFn fun j => b (J j)) g := by
  atlas_forward_decl GlobalTheory.TypeSum.derFam_expand_words
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem measurable_derFam_comp (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ)
    (hF : GlobalTheory.TypeSum.IsDerFam ε F) (h0 : ContinuousOn (F []) (UJset ε)) :
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  intro l
  induction l with
  | nil =>
    intro _ T _ _ _ φ hφ hφU
    exact (h0.comp_continuous hφ hφU).measurable
  | cons X l ih =>
    intro hl T _ _ _ φ hφ hφU
    have hX : X ∈ lieSet ε := hl X (List.mem_cons_self ..)
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)

    let q : ℕ → T → ℂ := fun m t =>
      (((m : ℝ) + 1)⁻¹)⁻¹ • (F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X)) - F l (φ t))
    have hq : ∀ m, Measurable (q m) := by
      intro m
      have h1 : Measurable (fun t => F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))) :=
        ih hl' T (fun t => φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))
          (hφ.mul continuous_const) (fun t => mul_mem_UJ (hφU t) (exp_mem_UJ hX _))
      have h2 : Measurable (fun t => F l (φ t)) := ih hl' T φ hφ hφU
      exact (h1.sub h2).const_smul ((((m : ℝ) + 1)⁻¹)⁻¹ : ℝ)
    have hlim : ∀ t, Tendsto (fun m => q m t) atTop (𝓝 (F (X :: l) (φ t))) := by
      intro t
      have hd := hF l hl' X hX (φ t) (hφU t)
      have hs := hd.tendsto_slope_zero
      have hseq : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
        · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
      have := hs.comp hseq
      refine this.congr fun m => ?_
      simp [q, Function.comp, zero_add]
    exact measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 hlim)

end GlobalTheory.TypeSum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ContinuousOn (F []) (UJset ε) → ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  atlas_forward_decl GlobalTheory.TypeSum.measurable_derFam_comp
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.KAvgDeriv

variable {n : ℕ} {ε : Fin n → Bool}

theorem hs_nonneg' (g : GlobalTheory.TypeSum.Mx n) : 0 ≤ hs g := by
  show 0 ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2
  positivity

theorem continuous_hs' : Continuous (fun g : GlobalTheory.TypeSum.Mx n => hs g) := by
  show Continuous (fun g : GlobalTheory.TypeSum.Mx n => ∑ i, ∑ j, ‖g i j‖ ^ 2)
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (((continuous_apply j).comp (continuous_apply i)).norm).pow 2

theorem mul_exp_conj {P : GlobalTheory.TypeSum.Mx n} (hP : IsUnit P) (X : GlobalTheory.TypeSum.Mx n) (t : ℝ) :
    P * NormedSpace.exp (t • (P⁻¹ * X * P)) = NormedSpace.exp (t • X) * P := by
  rw [← GlobalTheory.TypeSum.GrowthAtPlace.conj_exp hP X t, ← mul_assoc, ← mul_assoc,
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP), one_mul]

theorem bound_K (ε : Fin n → Bool) : ∃ M : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), 1 + hs (Formalism.REAL.toMK k) ≤ M := by
  have hc : Continuous fun k : ↥(Formalism.REAL.KG ε) => 1 + hs (Formalism.REAL.toMK k) :=
    continuous_const.add (continuous_hs'.comp
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun k => ?_⟩
  have h := hC k (Set.mem_univ _)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem bound_e (e : ↥(Formalism.REAL.KG ε) → ℂ) (he : Continuous e) : ∃ E : ℝ, 0 ≤ E ∧ ∀ k, ‖e k‖ ≤ E := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k => (hC k (Set.mem_univ _)).trans (le_max_left _ _)⟩

theorem bound_line (y X : GlobalTheory.TypeSum.Mx n) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 + hs (y * NormedSpace.exp (t • X)) ≤ M := by
  have hs1 : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
    have h : Continuous (NormedSpace.exp : GlobalTheory.TypeSum.Mx n → GlobalTheory.TypeSum.Mx n) := by
      open Matrix.Norms.Operator in exact NormedSpace.exp_continuous
    exact h.comp hs1
  have hc : Continuous fun t : ℝ => 1 + hs (y * NormedSpace.exp (t • X)) :=
    continuous_const.add (continuous_hs'.comp (continuous_const.mul hexp))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

private theorem isUnit_toMK (k : ↥(Formalism.REAL.KG ε)) : IsUnit (Formalism.REAL.toMK k) :=
  Units.isUnit _

private theorem toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm (k : ↥(Formalism.REAL.KG ε)) :
    (Formalism.REAL.toMK k)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK k = Formalism.REAL.Jm ε :=
  (k : Formalism.REAL.UJ ε).2

private theorem toMK_mem_UJset (k : ↥(Formalism.REAL.KG ε)) : Formalism.REAL.toMK k ∈ UJset ε :=
  toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm k

private theorem mul_mem_UJset_height {g h : GlobalTheory.TypeSum.Mx n} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hh' : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := hh
  show (g * h)ᴴ * Formalism.REAL.Jm ε * (g * h) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h by
      simp only [mul_assoc], hg', hh']

private theorem exp_smul_mem_UJset_of_mem_lieSet' {X : GlobalTheory.TypeSum.Mx n} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hG : Formalism.REAL.inG ε (t • X) := by
    show (t • X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (t • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX',
      smul_zero]
  exact Formalism.REAL.f1alg_exp_inUJ ε (t • X) hG

private theorem toMK_inv_mul_mul_toMK_mem_lieSet (k : ↥(Formalism.REAL.KG ε)) {X : GlobalTheory.TypeSum.Mx n} (hX : X ∈ lieSet ε) :
    (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k ∈ lieSet ε :=
  GlobalTheory.TypeSum.GrowthAtPlace.conj_lie (isUnit_toMK k) (toMK_conjTranspose_mul_Jm_mul_toMK_eq_Jm k) hX

private theorem mem_lieSet_of_mem_map_toMK_conj (k : ↥(Formalism.REAL.KG ε)) {l : List (GlobalTheory.TypeSum.Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) :
    ∀ Y ∈ l.map (fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k), Y ∈ lieSet ε := by
  intro Y hY
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
  exact toMK_inv_mul_mul_toMK_mem_lieSet k (hl Z hZ)

private theorem one_add_hs_nonneg (g : GlobalTheory.TypeSum.Mx n) : 0 ≤ 1 + hs g := by
  have := hs_nonneg' g
  linarith

private theorem mul_one_add_hs_mul_pow_le_abs_mul_pow {N : ℕ} {C MK ML : ℝ} {z k : GlobalTheory.TypeSum.Mx n}
    (hMK : 1 + hs k ≤ MK) (hML : 1 + hs z ≤ ML) :
    C * (1 + hs (z * k)) ^ N ≤ |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N := by
  have a0 := one_add_hs_nonneg (1 : GlobalTheory.TypeSum.Mx n)
  have k0 := one_add_hs_nonneg k
  have z0 := one_add_hs_nonneg z
  have h1 : 1 + hs (z * k) ≤ (1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML := by
    have h := GlobalTheory.TypeSum.GrowthAtPlace.one_add_hs_conj_le (1 : GlobalTheory.TypeSum.Mx n) z k
    rw [one_mul] at h
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hMK a0) hML z0 (mul_nonneg a0 (k0.trans hMK)))
  calc C * (1 + hs (z * k)) ^ N ≤ |C| * (1 + hs (z * k)) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (one_add_hs_nonneg _) N)
    _ ≤ |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (one_add_hs_nonneg _) h1 N) (abs_nonneg C)

theorem avg_derFam_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  intro n ε N F hF hG hM e he
  obtain ⟨E, hE0, hE⟩ := bound_e e he
  obtain ⟨MK, hMK⟩ := bound_K (n := n) ε
  refine ⟨?_, ?_⟩
  · intro l hl X hX g hg
    have hXl : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      · exact hX
      · exact hl Y hY
    obtain ⟨C, hC⟩ := hG (X :: l) hXl
    obtain ⟨C0, hC0⟩ := hG l hl
    obtain ⟨ML, hML⟩ := bound_line g X
    have hgt : ∀ t : ℝ, g * NormedSpace.exp (t • X) ∈ UJset ε := fun t => mul_mem_UJset_height hg (exp_smul_mem_UJset_of_mem_lieSet' hX t)
    have hb : ∀ (L : List (GlobalTheory.TypeSum.Mx n)) (C : ℝ),
        (∀ k : ↥(Formalism.REAL.KG ε), ∀ z ∈ UJset ε,
          ‖F (L.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k) z‖ ≤ C * (1 + hs z) ^ N) →
        ∀ k : ↥(Formalism.REAL.KG ε), ∀ t ∈ Set.Icc (-1 : ℝ) 1,
          ‖e k * F (L.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
            (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k)‖
            ≤ E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N) := by
      intro L C hC k t ht
      rw [norm_mul]
      exact mul_le_mul (hE k)
        ((hC k _ (mul_mem_UJset_height (hgt t) (toMK_mem_UJset k))).trans (mul_one_add_hs_mul_pow_le_abs_mul_pow (hMK k) (hML t ht)))
        (norm_nonneg _) hE0
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Formalism.REAL.muK ε) (x₀ := (0 : ℝ))
      (F := fun (t : ℝ) (k : ↥(Formalism.REAL.KG ε)) =>
        e k * F (l.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
          (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k))
      (F' := fun (t : ℝ) (k : ↥(Formalism.REAL.KG ε)) =>
        e k * F ((X :: l).map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k)
          (g * NormedSpace.exp (t • X) * Formalism.REAL.toMK k))
      (bound := fun _ => E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N))
      (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
      (Filter.Eventually.of_forall fun t => he.aestronglyMeasurable.mul (hM l hl _ (hgt t)))
      (Integrable.mono' (integrable_const (E * (|C0| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * ML) ^ N)))
        (he.aestronglyMeasurable.mul (hM l hl _ (hgt 0)))
        (Filter.Eventually.of_forall fun k => hb l C0 hC0 k 0 h0))
      (he.aestronglyMeasurable.mul (hM (X :: l) hXl _ (hgt 0)))
      (Filter.Eventually.of_forall fun k t ht => hb (X :: l) C hC k t ht)
      (integrable_const _)
      (Filter.Eventually.of_forall fun k t _ => by
        have hk := isUnit_toMK k
        have hm : ∀ s : ℝ, g * NormedSpace.exp (s • X) * Formalism.REAL.toMK k =
            g * Formalism.REAL.toMK k * NormedSpace.exp (s • ((Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)) := by
          intro s
          rw [mul_assoc g (Formalism.REAL.toMK k), mul_exp_conj hk X s, mul_assoc]
        have hd := GlobalTheory.TypeSum.IsDerFam.hasDerivAt_exp hF (mem_lieSet_of_mem_map_toMK_conj k hl) (toMK_inv_mul_mul_toMK_mem_lieSet k hX)
          (mul_mem_UJset_height hg (toMK_mem_UJset k)) t
        simp only [hm]
        exact hd.const_mul (e k))
    refine key.2.congr_deriv ?_
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  · intro l hl
    obtain ⟨C, hC⟩ := hG l hl
    refine ⟨(Formalism.REAL.muK ε).real Set.univ * E * |C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK) ^ N,
      fun g hg => ?_⟩
    have hk : ∀ k : ↥(Formalism.REAL.KG ε),
        ‖e k * F (l.map fun Y => (Formalism.REAL.toMK k)⁻¹ * Y * Formalism.REAL.toMK k) (g * Formalism.REAL.toMK k)‖
          ≤ E * (|C| * ((1 + hs (1 : GlobalTheory.TypeSum.Mx n)) * MK * (1 + hs g)) ^ N) := by
      intro k
      rw [norm_mul]
      exact mul_le_mul (hE k)
        ((hC k _ (mul_mem_UJset_height hg (toMK_mem_UJset k))).trans (mul_one_add_hs_mul_pow_le_abs_mul_pow (hMK k) le_rfl))
        (norm_nonneg _) hE0
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hk)).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow]
    ring

end GlobalTheory.KAvgDeriv
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.avg_derFam_growth_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  atlas_forward_decl GlobalTheory.KAvgDeriv.avg_derFam_growth
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.AvgCont

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  refine isClosed_eq ?_ continuous_const
  exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id

theorem mul_mem_UJset_of_inUJ {n : ℕ} {ε : Fin n → Bool} {y m : Matrix (Fin n) (Fin n) ℂ}
    (hy : y ∈ UJset ε) (hm : Formalism.REAL.inUJ ε m) : y * m ∈ UJset ε := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
  show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * yᴴ * Formalism.REAL.Jm ε * (y * m) = mᴴ * (yᴴ * Formalism.REAL.Jm ε * y) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hy', hm']

theorem continuous_maximalCompactSubgroup_toMatrix {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuousOn_avg_right_translates : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ),
    ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  intro n ε f hf e he
  rw [continuousOn_iff_continuous_restrict]
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (UJset ε) :=
    (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let F : UJset ε → Formalism.REAL.KG ε → ℂ := fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)
  have hF : Continuous (Function.uncurry F) := by
    refine (he.comp continuous_snd).mul ?_
    have hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε,
        (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε :=
      fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)
    exact hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps
  have h := continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

end GlobalTheory.AvgCont
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  atlas_forward_decl GlobalTheory.AvgCont.continuousOn_avg_right_translates
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.KAvgGrowth

theorem continuousOn_and_umg_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  classical
  intro n ε f hf hU e he
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  refine ⟨GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK n ε f hf e he, ?_⟩
  let B := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  let b : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n := fun i => (B i : Mx n)
  have hb : ∀ i, b i ∈ lieSet ε := fun i => by rw [lieSet_eq_lie]; exact (B i).2
  let c : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n → ℝ := fun i Z =>
    if h : Z ∈ lieSet ε then B.repr ⟨Z, by rwa [lieSet_eq_lie] at h⟩ i else 0
  have hsum : ∀ Z ∈ lieSet ε, Z = ∑ i, c i Z • b i := by
    intro Z hZ
    have hZ' : Z ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := by rwa [lieSet_eq_lie] at hZ
    have := congrArg Subtype.val (B.sum_repr ⟨Z, hZ'⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    simp only [c, dif_pos hZ]
    exact this.symm
  have hli : LinearIndependent ℝ b :=
    B.linearIndependent.map' (GlobalTheory.LowTypeDetermined.lie (Jm ε)).subtype (Submodule.ker_subtype _)
  have hC : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g := by
    intro l hl Z hZ g hg
    obtain ⟨τ, hτ0, hτ, hev⟩ := GlobalTheory.T.exp_second_kind_coordinates n ε _ b hb hli (fun Z hZ => ⟨fun i => c i Z, hsum Z hZ⟩) (fun i => c i Z)
    have h2 := GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero n ε N F hFd hFg l hl _ b hb g hg
    rw [← hτ0] at h2
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hτ
    have h4 : HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) (F (Z :: l) g) 0 := hFd l hl Z hZ g hg
    have h5 : (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) =ᶠ[nhds 0]
        ((fun t : Fin _ → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod)) ∘ τ) := by
      filter_upwards [hev] with t ht
      rw [← hsum Z hZ] at ht
      simp only [Function.comp_apply, ht]
    have h6 := h4.unique (h3.congr_of_eventuallyEq h5)
    rw [h6]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Complex.real_smul]
  have hD := GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand n ε F hFd _ b c hb hC
  have hK : ∀ k : ↥(KG ε), toMK k ∈ UJset ε := fun k => K_le_UJ (toMK_mem_K k)
  have had : ∀ (k : ↥(KG ε)) (X : Mx n), X ∈ lieSet ε → (toMK k)⁻¹ * X * toMK k ∈ lieSet ε := by
    intro k X hX
    rw [lieSet_eq_lie] at hX ⊢
    exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (hK k) hX
  have hinvc : Continuous fun k : ↥(KG ε) => (toMK k)⁻¹ := by
    have e1 : (fun k : ↥(KG ε) => (toMK k)⁻¹) = fun k => toMK k⁻¹ := by
      funext k
      exact (Matrix.coe_units_inv _).symm
    rw [e1]
    exact (continuous_toMK ε).comp continuous_inv
  have hcc : ∀ i (X : Mx n), X ∈ lieSet ε → Continuous fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k) := by
    intro i X hX
    have hX' : ∀ k : ↥(KG ε), (toMK k)⁻¹ * X * toMK k ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := fun k => by
      have := had k X hX; rwa [lieSet_eq_lie] at this
    have e1 : (fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)) =
        fun k => B.repr ⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ i := by
      funext k
      simp only [c, dif_pos (had k X hX)]
    rw [e1]
    have hm : Continuous fun k : ↥(KG ε) => (⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ : GlobalTheory.LowTypeDetermined.lie (Jm ε)) :=
      ((hinvc.matrix_mul continuous_const).matrix_mul (continuous_toMK ε)).subtype_mk _
    exact ((B.coord i).continuous_of_finiteDimensional).comp hm
  have e1 : ∀ (l : List (Mx n)) (k : ↥(KG ε)), (l.map fun X => (toMK k)⁻¹ * X * toMK k) =
      List.ofFn fun j => (toMK k)⁻¹ * l.get j * toMK k := by
    intro l k
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]; rfl
  have hbw : ∀ {m : ℕ} (J : Fin m → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε)))),
      ∀ Y ∈ List.ofFn (fun j => b (J j)), Y ∈ lieSet ε := by
    intro m J Y hY
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hY
    exact hb _
  have hUb : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (toMK k)⁻¹ * X * toMK k) g‖ ≤ C * (1 + hs g) ^ N := by
    intro l hl
    have hcb : ∀ i (j : Fin l.length), ∃ M : ℝ, ∀ k : ↥(KG ε), |c i ((toMK k)⁻¹ * l.get j * toMK k)| ≤ M := by
      intro i j
      obtain ⟨M, hM⟩ := (isCompact_univ.image (hcc i _ (hl _ (List.get_mem l j)))).isBounded.exists_norm_le
      exact ⟨M, fun k => by simpa [Real.norm_eq_abs] using hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    choose M hM using hcb
    have hCJ : ∀ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), ∃ C : ℝ,
        ∀ g ∈ UJset ε, ‖F (List.ofFn fun j => b (J j)) g‖ ≤ C * (1 + hs g) ^ N := fun J => hFg _ (hbw J)
    choose CJ hCJ using hCJ
    refine ⟨∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
      (∏ j, |M (J j) j|) * |CJ J|, fun k g hg => ?_⟩
    rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) g hg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc]
    have hw : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
    refine mul_le_mul (Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_) ?_ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => abs_nonneg _)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hM _ _ k).trans (le_abs_self _)
    · exact (hCJ J g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)
  have hF0c : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hMs : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      AEStronglyMeasurable (fun k : ↥(KG ε) =>
        F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) (muK ε) := by
    intro l hl z hz
    refine Measurable.aestronglyMeasurable ?_
    have e2 : (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) =
        fun k => ∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
          (∏ j, (c (J j) ((toMK k)⁻¹ * l.get j * toMK k) : ℂ)) * F (List.ofFn fun j => b (J j)) (z * toMK k) := by
      funext k
      rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) _ (mul_mem_UJ hz (hK k))]
    rw [e2]
    refine Finset.measurable_sum _ fun J _ => Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun j _ =>
        Complex.measurable_ofReal.comp (hcc _ _ (hl _ (List.get_mem l j))).measurable
    · exact GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset n ε F hFd hF0c _ (hbw J) (↥(KG ε)) (fun k => z * toMK k)
        (continuous_const.matrix_mul (continuous_toMK ε)) fun k => mul_mem_UJ hz (hK k)
  obtain ⟨hA, hB⟩ := GlobalTheory.T.avg_derFam_growth_alt n ε N F hFd hUb hMs e he
  refine ⟨N, _, fun y hy => ?_, hA, hB⟩
  simp only [List.map_nil]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [hF0 _ (mul_mem_UJ hy (hK k))]

end GlobalTheory.KAvgGrowth
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_continuousOn_uniformModerateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  atlas_forward_decl GlobalTheory.KAvgGrowth.continuousOn_and_umg_kAvg
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.KProjApprox

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sobCont_zero' : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) := ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add' {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', max (max C C') 0, words_append hS hS', fun w hw => ?_⟩
  have e1 := hC w hw
  have e2 := hC' w hw
  have s1 : 0 ≤ sobNorm σ S w := sobNorm_nonneg σ S w
  have s2 : 0 ≤ sobNorm σ S' w := sobNorm_nonneg σ S' w
  have h3 : sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := sobNorm_append σ S S' w
  change ‖ℓ w + ℓ' w‖ ≤ max (max C C') 0 * sobNorm σ (S ++ S') w
  change ‖ℓ w‖ ≤ C * sobNorm σ S w at e1
  change ‖ℓ' w‖ ≤ C' * sobNorm σ S' w at e2
  rw [h3]
  have a1 : C * sobNorm σ S w ≤ max (max C C') 0 * sobNorm σ S w :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) s1
  have a2 : C' * sobNorm σ S' w ≤ max (max C C') 0 * sobNorm σ S' w :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) s2
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem sobCont_smul' (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) : Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have e1 := hC w hw
  change ‖c * ℓ w‖ ≤ ‖c‖ * C * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left e1 (norm_nonneg c)

theorem sobCont_sum {ι : Type} (s : Finset ι) (ℓ : ι → (H →ₗ[ℂ] ℂ)) (h : ∀ i, Sobolev₂ (lieSet ε) σ (ℓ i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, ℓ i) :=
  Finset.sum_induction _ _ (fun _ _ => sobCont_add') sobCont_zero' fun i _ => h i

end GlobalTheory.TypeSum.KProjApprox

namespace GlobalTheory.TypeSum

open GlobalTheory.TypeSum.KProjApprox

theorem kAvg_approx_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
    ∃ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) ∧
      ∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε →
            ‖(∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) - ∑ a, L a (σ y (w a))‖ < δ := by
  intro n ε H _ _ _ σ h f hf happ e he hK
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h e hK
  refine ⟨m, a, haK, fun C hC δ hδ => ?_⟩
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  set I := ∫ k, ‖e k‖ ∂(muK ε) with hIdef
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hC' : IsCompact ((fun p : Mx n × KG ε => p.1 * toMK p.2) '' (C ×ˢ Set.univ)) :=
    (hC.prod isCompact_univ).image (continuous_fst.mul ((continuous_toMK ε).comp continuous_snd))
  obtain ⟨m', ℓ, v, hℓ, hv, happ'⟩ := happ _ hC' (δ / (1 + I)) (by positivity)
  refine ⟨fun j => ∑ i, ⟪c j, v i⟫_ℂ • ℓ i, fun j => sobCont_sum _ _ fun i => sobCont_smul' _ (hℓ i),
    fun y hy hyU => ?_⟩
  have hsm : ∀ w, Sm ε σ (kAvg ε σ e w) := fun w => h.2.2.1 _ (by
    rw [hsum]
    exact (kfin ε σ).sum_mem fun j _ => (kfin ε σ).smul_mem _ (haK j))
  have hmem : ∀ k : KG ε, y * toMK k ∈ UJset ε := fun k => mul_mem_UJ hyU (GlobalTheory.ExpansionAverage.toMK_mem k)
  have hcm : Continuous fun k : KG ε => y * toMK k := continuous_const.mul (continuous_toMK ε)
  have hci : ∀ i, Continuous fun k : KG ε => ℓ i (σ (y * toMK k) (v i)) := fun i =>
    (h.continuousOn_coef (hℓ i) (hv i)).comp_continuous hcm hmem
  have hcf : Continuous fun k : KG ε => f (y * toMK k) := hf.comp_continuous hcm hmem
  have h1 : ∀ i, ℓ i (σ y (kAvg ε σ e (v i))) = ∫ k, e k * ℓ i (σ (y * toMK k) (v i)) ∂(muK ε) := by
    intro i
    have := GlobalTheory.ExpansionAverage.form_kAvg h he (sobCont_translate h.1 (hℓ i) hyU) (hv i) (hsm _)
    simpa [sigma_mul h.1 hyU (GlobalTheory.ExpansionAverage.toMK_mem _)] using this
  have hid : ∑ j, (∑ i, ⟪c j, v i⟫_ℂ • ℓ i) (σ y (a j)) =
      ∫ k, e k * ∑ i, ℓ i (σ (y * toMK k) (v i)) ∂(muK ε) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum (f := fun i k => e k * ℓ i (σ (y * toMK k) (v i))) Finset.univ
      fun i _ => GlobalTheory.ExpansionAverage.integrable_K (he.mul (hci i))]
    simp_rw [← h1, hsum, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
  have hint : ∀ k : KG ε, ‖e k * f (y * toMK k) - e k * ∑ i, ℓ i (σ (y * toMK k) (v i))‖ ≤ ‖e k‖ * (δ / (1 + I)) := by
    intro k
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (happ' _ ⟨(y, k), ⟨hy, Set.mem_univ _⟩, rfl⟩ (hmem k)).le (norm_nonneg _)
  have i1 : Integrable (fun k : KG ε => e k * f (y * toMK k)) (muK ε) :=
    GlobalTheory.ExpansionAverage.integrable_K (he.mul hcf)
  have i2 : Integrable (fun k : KG ε => e k * ∑ i, ℓ i (σ (y * toMK k) (v i))) (muK ε) :=
    GlobalTheory.ExpansionAverage.integrable_K (he.mul (continuous_finsetSum _ fun i _ => hci i))
  rw [hid, ← integral_sub i1 i2]
  calc ‖∫ k, (e k * f (y * toMK k) - e k * ∑ i, ℓ i (σ (y * toMK k) (v i))) ∂(muK ε)‖
      ≤ ∫ k, ‖e k‖ * (δ / (1 + I)) ∂(muK ε) :=
        norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (he.norm.mul continuous_const))
          (Filter.Eventually.of_forall hint)
    _ = I * (δ / (1 + I)) := integral_mul_const _ _
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
end GlobalTheory.TypeSum
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kProjection_limit_discreteSeriesCoeffs : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
    ∃ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) ∧
      ∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε →
            ‖(∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) - ∑ a, L a (σ y (w a))‖ < δ := by
  atlas_forward_decl GlobalTheory.TypeSum.kAvg_approx_coef
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClosureSeries

open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum

theorem hasTypeAll_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := by
  intro hHC hCW n ε lam _ H _ _ σ hDS f hf hU happ
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  refine GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections hHC hCW n ε H σ hstd f hf hU ?_
  intro e he hK
  obtain ⟨hc, hu⟩ := GlobalTheory.T.compactAverage_continuousOn_uniformModerateGrowth n ε f hf hU e he
  obtain ⟨d, w, hw, hap⟩ := GlobalTheory.T.kProjection_limit_discreteSeriesCoeffs n ε H σ hstd f hf happ e he hK
  obtain ⟨L, hL, heq⟩ := GlobalTheory.T.eq_matrixCoeff_of_locallyUniform_limit_kFinite hHC hCW n ε H σ hstd d w hw _ hc hu hap
  exact ⟨d, L, w, hL, hw, heq⟩

end GlobalTheory.ClosureSeries
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasAllKTypes_of_closure_discreteSeriesCoefficients : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := by
  atlas_forward_decl GlobalTheory.ClosureSeries.hasTypeAll_of_closure
end
