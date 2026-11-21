import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolicStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwoSmooth

open Topology Filter
open scoped ContDiff

section General

variable {X P : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in

theorem iteratedFDeriv_fderiv_eq' {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : P → F) (m : ℕ) (x : P) :
    iteratedFDeriv ℝ m (fderiv ℝ f) x =
      (continuousMultilinearCurryRightEquiv' ℝ m P F) (iteratedFDeriv ℝ (m + 1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

omit [MeasurableSpace X] [OpensMeasurableSpace X] [FiniteDimensional ℝ P] in

theorem continuousOn_of_iteratedFDeriv_zero {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : X → P → F}
    {s : Set (X × P)} (h : ContinuousOn (fun p : X × P => iteratedFDeriv ℝ 0 (H p.1) p.2) s) :
    ContinuousOn (fun p : X × P => H p.1 p.2) s := by
  have e : (fun p : X × P => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ P F (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]
  exact (continuousMultilinearCurryFin0 ℝ P F).continuous.comp_continuousOn h

theorem hasFDerivAt_integral_param (ν : Measure X) [IsFiniteMeasure ν] {U : Set P} (hU : IsOpen U) {S : Set X}
    (hS : IsCompact S) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (H : X → P → F)
    (hrep : ∀ u, ∃ v ∈ S, H u = H v) (hd : ∀ u, DifferentiableOn ℝ (H u) U)
    (h0 : ContinuousOn (fun p : X × P => H p.1 p.2) (Set.univ ×ˢ U))
    (h1 : ContinuousOn (fun p : X × P => fderiv ℝ (H p.1) p.2) (Set.univ ×ˢ U)) {x₀ : P} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ u, H u x ∂ν) (∫ u, fderiv ℝ (H u) x₀ ∂ν) x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hcb : Metric.closedBall x₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (S ×ˢ Metric.closedBall x₀ (ε / 2)) := hS.prod (isCompact_closedBall _ _)
  have hsub : S ×ˢ Metric.closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ U := Set.prod_mono (Set.subset_univ _) hcb
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn (h0.mono hsub)
  have bd : ∀ u, ∀ x ∈ Metric.closedBall x₀ (ε / 2), ‖fderiv ℝ (H u) x‖ ≤ C := fun u x hx => by
    obtain ⟨v, hv, e⟩ := hrep u
    rw [e]; exact hC (v, x) ⟨hv, hx⟩
  have bd0 : ∀ u, ‖H u x₀‖ ≤ C0 := fun u => by
    obtain ⟨v, hv, e⟩ := hrep u
    rw [e]; exact hC0 (v, x₀) ⟨hv, Metric.mem_closedBall_self (by linarith)⟩
  have hcx : ∀ x ∈ U, Continuous fun u => H u x := fun x hx =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun u => ⟨trivial, hx⟩
  have hcx' : Continuous fun u => fderiv ℝ (H u) x₀ :=
    h1.comp_continuous (continuous_id.prodMk continuous_const) fun u => ⟨trivial, hx₀⟩
  have hball2 : Metric.ball x₀ (ε / 2) ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ (by linarith)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hball2
    (Filter.eventually_of_mem (hU.mem_nhds hx₀) fun x hx => (hcx x hx).aestronglyMeasurable)
    (Integrable.of_bound (hcx x₀ hx₀).aestronglyMeasurable C0 (.of_forall bd0)) hcx'.aestronglyMeasurable
    (.of_forall fun u x hx => bd u x (Metric.ball_subset_closedBall hx)) (integrable_const C)
    (.of_forall fun u x hx =>
      ((hd u).differentiableAt (hU.mem_nhds (hcb (Metric.ball_subset_closedBall hx)))).hasFDerivAt)

theorem contDiffOn_integral_param (ν : Measure X) [IsFiniteMeasure ν] {U : Set P} (hU : IsOpen U) {S : Set X}
    (hS : IsCompact S) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (H : X → P → F),
      (∀ u, ∃ v ∈ S, H u = H v) → (∀ u, ContDiffOn ℝ ∞ (H u) U) →
      (∀ m : ℕ, ContinuousOn (fun p : X × P => iteratedFDeriv ℝ m (H p.1) p.2) (Set.univ ×ˢ U)) →
      ContDiffOn ℝ n (fun x => ∫ u, H u x ∂ν) U := by
  induction n with
  | zero =>
    intro F _ _ _ H hrep hs hm
    have h1 : ContinuousOn (fun p : X × P => fderiv ℝ (H p.1) p.2) (Set.univ ×ˢ U) := by
      refine continuousOn_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq']
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 P F).continuous.comp_continuousOn (hm 1)
    refine contDiffOn_zero.2 fun x hx => ?_
    exact (hasFDerivAt_integral_param ν hU hS H hrep (fun u => (hs u).differentiableOn (by simp))
      (continuousOn_of_iteratedFDeriv_zero (hm 0)) h1 hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ H hrep hs hm
    have hm' : ∀ m : ℕ, ContinuousOn (fun p : X × P => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2)
        (Set.univ ×ˢ U) := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq']
      exact (continuousMultilinearCurryRightEquiv' ℝ m P F).continuous.comp_continuousOn (hm (m + 1))
    have hrep' : ∀ u, ∃ v ∈ S, fderiv ℝ (H u) = fderiv ℝ (H v) := fun u => by
      obtain ⟨v, hv, e⟩ := hrep u
      exact ⟨v, hv, by rw [e]⟩
    have hD := ih (fun u => fderiv ℝ (H u)) hrep' (fun u => (hs u).fderiv_of_isOpen hU (by simp)) hm'
    have hder : ∀ x ∈ U, HasFDerivAt (fun x => ∫ u, H u x ∂ν) (∫ u, fderiv ℝ (H u) x ∂ν) x := fun x hx =>
      hasFDerivAt_integral_param ν hU hS H hrep (fun u => (hs u).differentiableOn (by simp))
        (continuousOn_of_iteratedFDeriv_zero (hm 0))
        (continuousOn_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) hx
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
      ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, by simp,
        hD.congr fun x hx => (hder x hx).fderiv⟩

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [FiniteDimensional ℝ P] in

theorem contDiffAt_iteratedFDeriv_param {M F : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : M → P → F) {O : Set (M × P)}
    (hΦ : ∀ q ∈ O, ContDiffAt ℝ ∞ (Function.uncurry Φ) q) (m : ℕ) :
    ∀ q ∈ O, ContDiffAt ℝ ∞ (fun q : M × P => iteratedFDeriv ℝ m (Φ q.1) q.2) q := by
  induction m with
  | zero =>
    intro q hq
    have e : (fun q : M × P => iteratedFDeriv ℝ 0 (Φ q.1) q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ P F).symm (Function.uncurry Φ q) := by
      funext q; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [e]
    exact (continuousMultilinearCurryFin0 ℝ P F).symm.contDiff.contDiffAt.comp q (hΦ q hq)
  | succ m ih =>
    intro q hq
    have e : (fun q : M × P => iteratedFDeriv ℝ (m + 1) (Φ q.1) q.2) =
        fun q => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => P) F).symm
          (fderiv ℝ (fun z => iteratedFDeriv ℝ m (Φ q.1) z) q.2) := by
      funext q; rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [e]
    refine (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => P) F).symm.contDiff.contDiffAt.comp q ?_
    refine ContDiffAt.fderiv (f := fun (q : M × P) (z : P) => iteratedFDeriv ℝ m (Φ q.1) z) (g := Prod.snd)
      ?_ contDiffAt_snd le_rfl
    have hg : ContDiffAt ℝ ∞ (fun p : (M × P) × P => (p.1.1, p.2)) (q, q.2) :=
      (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
    exact (ih (q.1, q.2) hq).comp (q, q.2) hg

end General

section Specific

open GlobalTheory.LeviGA GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

omit [IsTotallyComplex E] in

theorem contDiff_mulL {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Lie E n × Lie E n => toL (Matrix.of p.1 * Matrix.of p.2)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun p : Lie E n × Lie E n => ∑ k, p.1 i k * p.2 k j
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply_apply ℝ (Cinf E) i k).comp contDiff_fst).mul
      ((contDiff_apply_apply ℝ (Cinf E) k j).comp contDiff_snd)

omit [IsTotallyComplex E] in

theorem contDiff_blkMat_entry (hr : r ≤ a) (i k : Fin a) :
    ContDiff ℝ ∞ (fun x : Lie E (a - r) => blkMat (Cinf E) hr (1, Matrix.of x) i k) := by
  change ContDiff ℝ ∞ (fun x : Lie E (a - r) => Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (Cinf E)) 0 0
    (Matrix.of x) ((blkEquiv hr).symm i) ((blkEquiv hr).symm k))
  rcases (blkEquiv hr).symm i with i | i <;> rcases (blkEquiv hr).symm k with k | k
  · simp only [Matrix.fromBlocks_apply₁₁]; exact contDiff_const
  · simp only [Matrix.fromBlocks_apply₁₂]; exact contDiff_const
  · simp only [Matrix.fromBlocks_apply₂₁]; exact contDiff_const
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact contDiff_apply_apply ℝ (Cinf E) i k

omit [IsTotallyComplex E] in

def blkA (hr : r ≤ a) (κ : Kinf E a) (x : Lie E (a - r)) : Lie E a :=
  toL (blkMat (Cinf E) hr (1, Matrix.of x) * κ.1)

omit [IsTotallyComplex E] in

theorem contDiff_blkA (hr : r ≤ a) (κ : Kinf E a) : ContDiff ℝ ∞ (blkA hr κ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun x : Lie E (a - r) => ∑ k, blkMat (Cinf E) hr (1, Matrix.of x) i k * κ.1 k j
  exact ContDiff.sum fun k _ => (contDiff_blkMat_entry hr i k).mul contDiff_const

omit [IsTotallyComplex E] in

theorem blkA_mem (hr : r ≤ a) (κ : Kinf E a) {x : Lie E (a - r)} (hx : x ∈ invSet E (a - r)) :
    blkA hr κ x ∈ invSet E a := by
  have h1 : IsUnit ((1 : Matrix (Fin r) (Fin r) (Cinf E)), Matrix.of x) := Prod.isUnit_iff.2 ⟨isUnit_one, hx⟩
  exact (h1.map (blkMat (Cinf E) hr)).mul (Unitary.toUnits κ).isUnit

theorem chart_slice [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) (g : GA E (a - r)) {x : Lie E (a - r)} (hx : x ∈ invSet E (a - r)) :
    chart (slice E μ 𝓕 hr φ m₁ t κ) g x =
      ∫ u in 𝓕, chart φ (unip u * (blkGL hr (m₁, g) * finGL E a t)) (blkA hr κ x) ∂μ := by
  obtain ⟨y, hy⟩ := hx
  have ex : x = toL y.val := by rw [hy]; rfl
  subst ex
  rw [chart_val]
  unfold slice
  congr 1
  funext u
  have e : blkA hr κ (toL y.val) = toL (blkGL hr (1, y) * Unitary.toUnits κ).val := rfl
  rw [e, chart_val, blkGL_mul_infGL]
  congr 1
  rw [map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
  simp only [mul_assoc]

theorem chart_unip_add {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (G : GA E a)
    {γ : BlockIx a r → Ad E} (hγ : γ ∈ ratN E a r) (u : BlockIx a r → Ad E) :
    chart φ (unip (γ + u) * G) = chart φ (unip u * G) := by
  obtain ⟨y, rfl⟩ := hγ
  have e : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y) =
      ratGL E a (unip y) := unip_algebraMap y
  funext x
  unfold chart
  split_ifs
  · rw [unip_add, e, mul_assoc, mul_assoc, hl]; simp only [mul_assoc]
  · rfl

end Specific

section Local

open GlobalTheory.LeviGA GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem eventually_chart_eq (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (G : GA E a)
    (u₀ : BlockIx a r → Ad E) :
    ∀ᶠ u in 𝓝 u₀, ∀ y, chart φ.1 (unip u * G) y = chart φ.1 (unip u₀ * G)
      (toL (Matrix.of (toL (Matrix.GeneralLinearGroup.map (pInf E) ((unip u₀ * G)⁻¹ * (unip u * G))).val) *
        Matrix.of y)) := by
  have hc : Continuous fun u : BlockIx a r → Ad E =>
      Matrix.GeneralLinearGroup.map (pFin E) ((unip u₀ * G)⁻¹ * (unip u * G)) :=
    (ContAut.continuous_map_pFin E a).comp (continuous_const.mul (CuspidalL2GL.continuous_unip.mul continuous_const))
  have hmem : {u : BlockIx a r → Ad E | finRep E a (Matrix.GeneralLinearGroup.map (pFin E)
      ((unip u₀ * G)⁻¹ * (unip u * G))) φ = φ} ∈ 𝓝 u₀ := by
    refine (hlev.preimage hc).mem_nhds ?_
    change finRep E a _ φ = φ
    simp
  filter_upwards [hmem] with u hu y
  set h₀ := unip u₀ * G
  set h := unip u * G
  set c := Matrix.GeneralLinearGroup.map (pInf E) (h₀⁻¹ * h)
  set k := Matrix.GeneralLinearGroup.map (pFin E) (h₀⁻¹ * h)
  have key : h = h₀ * finGL E a k * infGL E a c := by
    rw [mul_assoc, ← infGL_comm, infGL_mul_finGL, mul_inv_cancel_left]
  have hk : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hu
  rw [key, chart_mul, ← chart_rt_fin, hk]
  rfl

theorem continuousAt_iteratedFDeriv (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (hr : r ≤ a)
    (κ : Kinf E a) (G : GA E a) (m : ℕ) (u₀ : BlockIx a r → Ad E) {x₀ : Lie E (a - r)}
    (hx₀ : x₀ ∈ invSet E (a - r)) :
    ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E (a - r) =>
      iteratedFDeriv ℝ m (fun x => chart φ.1 (unip p.1 * G) (blkA hr κ x)) p.2) (u₀, x₀) := by
  set h₀ := unip u₀ * G
  let Cm : (BlockIx a r → Ad E) → Lie E a := fun u =>
    toL (Matrix.GeneralLinearGroup.map (pInf E) (h₀⁻¹ * (unip u * G))).val
  have hCm : Continuous Cm :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp
      (continuous_const.mul (CuspidalL2GL.continuous_unip.mul continuous_const)))
  have hC0 : Cm u₀ = oneL E a := by
    simp only [Cm, h₀, inv_mul_cancel, map_one]
    rfl
  let Φ₂ : Lie E a → Lie E (a - r) → ℂ := fun c x =>
    chart φ.1 h₀ (toL (Matrix.of c * Matrix.of (blkA hr κ x)))
  have hq : ContDiff ℝ ∞ (fun q : Lie E a × Lie E (a - r) => toL (Matrix.of q.1 * Matrix.of (blkA hr κ q.2))) :=
    contDiff_mulL.comp (contDiff_fst.prodMk ((contDiff_blkA hr κ).comp contDiff_snd))
  let O : Set (Lie E a × Lie E (a - r)) :=
    {q | toL (Matrix.of q.1 * Matrix.of (blkA hr κ q.2)) ∈ invSet E a}
  have hΦ : ∀ q ∈ O, ContDiffAt ℝ ∞ (Function.uncurry Φ₂) q := fun q hq' => by
    have e : Function.uncurry Φ₂ =
        chart φ.1 h₀ ∘ fun q : Lie E a × Lie E (a - r) => toL (Matrix.of q.1 * Matrix.of (blkA hr κ q.2)) := rfl
    rw [e]
    exact (contDiffAt_chart φ.2 h₀ hq').comp q hq.contDiffAt
  have hO : (oneL E a, x₀) ∈ O := by
    change toL (Matrix.of (toL 1) * Matrix.of (blkA hr κ x₀)) ∈ invSet E a
    simpa using blkA_mem hr κ hx₀
  have hΨ := (contDiffAt_iteratedFDeriv_param Φ₂ hΦ m (oneL E a, x₀) hO).continuousAt
  have hcomp : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E (a - r) =>
      iteratedFDeriv ℝ m (Φ₂ (Cm p.1)) p.2) (u₀, x₀) :=
    ContinuousAt.comp_of_eq (g := fun q : Lie E a × Lie E (a - r) => iteratedFDeriv ℝ m (Φ₂ q.1) q.2)
      (f := fun p : (BlockIx a r → Ad E) × Lie E (a - r) => (Cm p.1, p.2)) hΨ
      ((hCm.comp continuous_fst).prodMk continuous_snd).continuousAt (Prod.ext hC0 rfl)
  refine hcomp.congr ?_
  have hev := (continuous_fst.tendsto (u₀, x₀)).eventually (eventually_chart_eq φ hlev G u₀)
  filter_upwards [hev] with p hp
  have e : (fun x => chart φ.1 (unip p.1 * G) (blkA hr κ x)) = Φ₂ (Cm p.1) := funext fun x => hp _
  rw [e]

end Local

theorem slice_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a),
      GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ ∈ Sm E (a - r) := by
  intro E _ _ _ a r hr _ _ μ 𝓕 _ _ h1 φ hφ m₁ t κ g
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  set G := GlobalTheory.LeviGA.blkGL hr (m₁, g) * finGL E a t
  let H : (BlockIx a r → Ad E) → Lie E (a - r) → ℂ := fun u x => chart φ.1 (unip u * G) (blkA hr κ x)
  have hrep : ∀ u, ∃ v ∈ K, H u = H v := fun u => by
    obtain ⟨γ, hγ, hk⟩ := hcov u
    refine ⟨γ + u, hk, funext fun x => ?_⟩
    change chart φ.1 (unip u * G) _ = chart φ.1 (unip (γ + u) * G) _
    rw [chart_unip_add hφ.left G hγ u]
  have hs : ∀ u, ContDiffOn ℝ ∞ (H u) (invSet E (a - r)) := fun u =>
    (φ.2 (unip u * G)).comp (contDiff_blkA hr κ).contDiffOn fun x hx => blkA_mem hr κ hx
  have hm : ∀ m : ℕ, ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E (a - r) =>
      iteratedFDeriv ℝ m (H p.1) p.2) (Set.univ ×ˢ invSet E (a - r)) := fun m p hp =>
    (continuousAt_iteratedFDeriv φ hφ.level hr κ G m p.1 hp.2).continuousWithinAt
  exact (contDiffOn_infty.2 fun n => contDiffOn_integral_param (μ.restrict 𝓕) isOpen_invSet hK n H hrep hs hm).congr
    fun x hx => chart_slice μ 𝓕 hr φ.1 m₁ t κ g hx

end GlobalTheory.SliceTwoSmooth
end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_cusp_form : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a), GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ ∈ Sm E (a - r) := by
  atlas_forward_decl GlobalTheory.SliceTwoSmooth.slice_mem_Sm
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem setIntegral_comp_contAddEquiv {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    (N : AddSubgroup X) [Countable N] {𝓕 : Set X} (h𝓕 : IsAddFundamentalDomain N 𝓕 μ) (h1 : μ 𝓕 = 1)
    (T : X ≃ₜ+ X) (hT : ∀ n ∈ N, T n ∈ N) (hT' : ∀ n ∈ N, T.symm n ∈ N)
    (f : X → ℂ) (hf : ∀ n ∈ N, ∀ x, f (n + x) = f x) :
    ∫ x in 𝓕, f (T x) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  let m := T.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  let e : N ≃ N :=
    { toFun := fun n => ⟨T.symm n, hT' _ n.2⟩
      invFun := fun n => ⟨T n, hT _ n.2⟩
      left_inv := fun n => Subtype.ext (T.apply_symm_apply _)
      right_inv := fun n => Subtype.ext (T.symm_apply_apply _) }
  have hD : IsAddFundamentalDomain N (m '' 𝓕) (μ.map m) :=
    h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e
      fun n x => by
        change T (T.symm n + x) = n + T x
        rw [map_add, T.apply_symm_apply]
  have hD2 : IsAddFundamentalDomain N 𝓕 (μ.map m) :=
    h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hinv : ∀ (n : N) (x : X), f (n +ᵥ x) = f x := fun n x => hf n n.2 x
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map m = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map m) μ⟩
  have hm : (μ.map m) (m '' 𝓕) = 1 := by
    rw [m.map_apply, m.preimage_image, h1]
  have hc1 : c = 1 := by
    have h3 := hD.measure_eq hD2
    rw [hm, hc, Measure.smul_apply, h1] at h3
    have h4 : (c : ENNReal) = 1 := by simpa [ENNReal.smul_def] using h3.symm
    exact_mod_cast h4
  have step := m.measurableEmbedding.setIntegral_map (μ := μ) f (m '' 𝓕)
  rw [m.preimage_image] at step
  change ∫ x in 𝓕, f (m x) ∂μ = _
  rw [← step, hD.setIntegral_eq hD2 hinv, hc, hc1, one_smul]

section Shear

variable {R : Type} [CommRing R] {a r : ℕ}

def shear (D : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (nilM x * D) p.1.1 p.1.2

theorem nilM_apply_ix (x : BlockIx a r → R) (p : BlockIx a r) : nilM x p.1.1 p.1.2 = x p := by
  unfold nilM
  rw [Matrix.of_apply, dif_pos p.2]

theorem nilM_injective : Function.Injective (fun x : BlockIx a r → R => nilM x) := by
  intro x y h
  funext p
  have h' := congrFun (congrFun h p.1.1) p.1.2
  simp only at h'
  rwa [nilM_apply_ix, nilM_apply_ix] at h'

theorem nilM_add (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem shear_add (D : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    shear D (x + y) = shear D x + shear D y := by
  funext p
  simp only [shear, nilM_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]

theorem nilM_shear (D : Matrix (Fin a) (Fin a) R) (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0)
    (x : BlockIx a r → R) : nilM (shear D x) = nilM x * D := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · conv_lhs => rw [nilM, Matrix.of_apply, dif_pos h]
    rfl
  · have h0 : nilM (shear D x) i j = 0 := by
      unfold nilM
      rw [Matrix.of_apply, dif_neg h]
    rw [h0, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : (i : ℕ) < r ∧ r ≤ (k : ℕ)
    · rw [hD k j hk.2 (by omega), mul_zero]
    · have h1 : nilM x i k = 0 := by
        unfold nilM
        rw [Matrix.of_apply, dif_neg hk]
      rw [h1, zero_mul]

theorem mul_nilM (D : Matrix (Fin a) (Fin a) R)
    (hD1 : ∀ i j : Fin a, (i : ℕ) < r → D i j = (1 : Matrix (Fin a) (Fin a) R) i j)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0) (x : BlockIx a r → R) : D * nilM x = nilM x := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < r
  · rw [show (∑ k, D i k * nilM x k j) = ∑ k, (1 : Matrix (Fin a) (Fin a) R) i k * nilM x k j from
      Finset.sum_congr rfl fun k _ => by rw [hD1 i k hi]]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  · have h0 : nilM x i j = 0 := by
      unfold nilM
      rw [Matrix.of_apply, dif_neg (fun h => hi h.1)]
    rw [h0]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [hD i k (by omega) hk.1, zero_mul]
    · have h1 : nilM x k j = 0 := by
        unfold nilM
        rw [Matrix.of_apply, dif_neg hk]
      rw [h1, mul_zero]

theorem unip_mul_eq (D : GL (Fin a) R)
    (hD1 : ∀ i j : Fin a, (i : ℕ) < r → (D : Matrix (Fin a) (Fin a) R) i j = (1 : Matrix (Fin a) (Fin a) R) i j)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → (D : Matrix (Fin a) (Fin a) R) i j = 0)
    (x : BlockIx a r → R) : unip x * D = D * unip (shear (D : Matrix (Fin a) (Fin a) R) x) := by
  apply Units.ext
  change (1 + nilM x) * (D : Matrix (Fin a) (Fin a) R) =
    (D : Matrix (Fin a) (Fin a) R) * (1 + nilM (shear (D : Matrix (Fin a) (Fin a) R) x))
  rw [nilM_shear _ hD, add_mul, mul_add, one_mul, mul_one, ← mul_assoc, mul_nilM _ hD1 hD]

theorem shear_shear (D D' : Matrix (Fin a) (Fin a) R)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0)
    (hD' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D' i j = 0) (h : D * D' = 1) (x : BlockIx a r → R) :
    shear D' (shear D x) = x := by
  apply nilM_injective
  simp only
  rw [nilM_shear _ hD', nilM_shear _ hD, Matrix.mul_assoc, h, Matrix.mul_one]

theorem continuous_shear [TopologicalSpace R] [IsTopologicalRing R] (D : Matrix (Fin a) (Fin a) R) :
    Continuous (shear (r := r) D) := by
  have hN : Continuous fun x : BlockIx a r → R => nilM x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold nilM
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hM : Continuous fun x : BlockIx a r → R => nilM x * D := hN.matrix_mul continuous_const
  exact continuous_pi fun p => (hM.matrix_elem p.1.1 p.1.2)

theorem nilM_map {S : Type} [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    nilM (fun p => f (x p)) = (nilM x).map f := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp

theorem shear_map {S : Type} [CommRing S] (f : R →+* S) (D : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) :
    shear (D.map f) (fun p => f (x p)) = fun p => f (shear D x p) := by
  funext p
  simp only [shear]
  rw [nilM_map, ← Matrix.map_mul]
  rfl

theorem blkGL_one_top (hr : r ≤ a) (l : GL (Fin (a - r)) R) (i j : Fin a) (hi : (i : ℕ) < r) :
    (blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) i j = (1 : Matrix (Fin a) (Fin a) R) i j := by
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  rw [blkGL_apply]
  have e1 : (1 : Matrix (Fin a) (Fin a) R) (blkEquiv hr i) (blkEquiv hr j) =
      (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) R) i j := by
    simp [Matrix.one_apply, (blkEquiv hr).injective.eq_iff]
  rw [e1]
  rcases i with i | i
  · rcases j with j | j <;> simp [Matrix.one_apply]
  · exfalso
    rw [blkEquiv_inr] at hi
    omega

theorem blkGL_one_low (hr : r ≤ a) (l : GL (Fin (a - r)) R) (i j : Fin a) (hi : r ≤ (i : ℕ)) (hj : (j : ℕ) < r) :
    (blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) i j = 0 := by
  rcases blkGL_block hr (1, l) i j with h | h
  · exact absurd (h.2 hj) (by omega)
  · exact h

end Shear

theorem slice_ratGL_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : GA E a → ℂ, Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (γ : GL (Fin (a - r)) E) (g : GA E (a - r)),
    GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ (ratGL E (a - r) γ * g) = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ g := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 φ _ hφ m₁ t κ γ g
  haveI := hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype

  let G : GL (Fin a) E := blkGL hr (1, γ)
  have hDG : ratGL E a G = blkGL hr (1, ratGL E (a - r) γ) :=
    (map_blkGL hr (algebraMap E (Ad E)) (1, γ)).trans (by rw [map_one]; rfl)
  have hDG' : (ratGL E a G)⁻¹ = blkGL hr (1, (ratGL E (a - r) γ)⁻¹) := by
    rw [hDG, ← map_inv, Prod.inv_mk, inv_one]
  let M : Matrix (Fin a) (Fin a) (Ad E) := (ratGL E a G : Matrix (Fin a) (Fin a) (Ad E))
  let M' : Matrix (Fin a) (Fin a) (Ad E) := ((ratGL E a G)⁻¹ : GA E a)
  have hM1 : ∀ i j : Fin a, (i : ℕ) < r → M i j = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j := fun i j hi => by
    change ((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG]; exact blkGL_one_top hr _ i j hi
  have hM2 : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0 := fun i j hi hj => by
    change ((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG]; exact blkGL_one_low hr _ i j hi hj
  have hM2' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M' i j = 0 := fun i j hi hj => by
    change (((ratGL E a G)⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG']; exact blkGL_one_low hr _ i j hi hj
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := shear M
      invFun := shear M'
      left_inv := fun x => shear_shear M M' hM2 hM2' hMM' x
      right_inv := fun x => shear_shear M' M hM2' hM2 hM'M x
      map_add' := shear_add M
      continuous_toFun := continuous_shear M
      continuous_invFun := continuous_shear M' }
  have hT : ∀ n ∈ ratN E a r, T n ∈ ratN E a r := by
    rintro _ ⟨e, rfl⟩
    exact ⟨shear (G : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩
  have hT' : ∀ n ∈ ratN E a r, T.symm n ∈ ratN E a r := by
    rintro _ ⟨e, rfl⟩
    exact ⟨shear ((G⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩

  let B : GA E a := blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)
  let f : (BlockIx a r → Ad E) → ℂ := fun y => φ (unip y * B)
  have hf : ∀ n ∈ ratN E a r, ∀ x, f (n + x) = f x := by
    rintro _ ⟨e, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * B) = φ (unip x * B)
    rw [unip_add, unip_algebraMap, mul_assoc, hφ]
  have key : ∀ x, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) =
      f (T x) := fun x => by
    rw [show (m₁, ratGL E (a - r) γ * g) = ((1 : GA E r), ratGL E (a - r) γ) * (m₁, g) by simp, map_mul, ← hDG]
    change _ = φ (unip (shear M x) * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))
    simp only [mul_assoc]
    rw [← mul_assoc (unip x) (ratGL E a G), unip_mul_eq (ratGL E a G) hM1 hM2, mul_assoc, hφ]
  unfold slice
  calc ∫ x in 𝓕, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ
      = ∫ x in 𝓕, f (T x) ∂μ := by congr 1; funext x; exact key x
    _ = ∫ x in 𝓕, f x ∂μ := setIntegral_comp_contAddEquiv μ (ratN E a r) h𝓕 h1 T hT hT' f hf

end GlobalTheory.SliceTwo

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : GA E a → ℂ, Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (γ : GL (Fin (a - r)) E) (g : GA E (a - r)), GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ (ratGL E (a - r) γ * g) = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ g := by
  atlas_forward_decl GlobalTheory.SliceTwo.slice_ratGL_mul
end

section
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem isOpen_levelSub : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E))
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
      IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  intro E _ _ a r hr t L hL
  have hblk : Continuous fun l : GL (Fin (a - r)) (Af E) => blkGL hr (1, l) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 (l : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_val).matrix_reindex _ _
    · have e : ∀ l : GL (Fin (a - r)) (Af E), ((blkGL hr (1, l))⁻¹ : GL (Fin a) (Af E)) = blkGL hr (1, l⁻¹) := by
        intro l; rw [← map_inv]; rfl
      simp_rw [e]
      show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 ((l⁻¹ : GL _ _) : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_coe_inv).matrix_reindex _ _
  have hc : Continuous fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t :=
    (continuous_const.mul hblk).mul continuous_const
  have hs : (levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) =
      (fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t) ⁻¹' (L : Set (GL (Fin a) (Af E))) := by
    ext l
    simp only [levelSub, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, e⟩
      rw [← e]; simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  rw [hs]
  exact hL.preimage hc

end GlobalTheory.SliceTwo
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  atlas_forward_decl GlobalTheory.SliceTwo.isOpen_levelSub
end

section
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def contLeft : Submodule ℂ (Sm E a) where
  carrier := {f | Continuous f.1 ∧ ∀ γ g, f.1 (ratGL E a γ * g) = f.1 g}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl⟩
  add_mem' := fun {f h} hf hh => ⟨hf.1.add hh.1, fun γ g => by
    change f.1 _ + h.1 _ = f.1 _ + h.1 _
    rw [hf.2, hh.2]⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun γ g => by
    change c • f.1 _ = c • f.1 _
    rw [hf.2]⟩

theorem span_cpt_le_contLeft {φ : Sm E a} (hA : IsAutForm φ) :
    Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ≤ contLeft E a := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  have hc := ContAut.continuous_of_isOpen_stab E a φ hA.level
  refine ⟨hc.comp (continuous_mul_const _), fun γ g => ?_⟩
  change φ.1 (ratGL E a γ * g * _) = φ.1 (g * _)
  rw [mul_assoc, hA.left]

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

def sliceLin (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] {𝓕 : Set (BlockIx a r → Ad E)}
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (hr : r ≤ a) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) : contLeft E a →ₗ[ℂ] (GA E (a - r) → ℂ) where
  toFun f := slice E μ 𝓕 hr f.1.1 m₁ t κ
  map_add' f h := by
    funext m₂
    exact integral_add (CuspidalL2GL.integrableOn_unip f.2.1 f.2.2 μ h𝓕 _) (CuspidalL2GL.integrableOn_unip h.2.1 h.2.2 μ h𝓕 _)
  map_smul' c f := by
    funext m₂
    exact integral_const_mul c _

theorem slice_kfin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (ψ : Sm E (a - r)),
      ψ.1 = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 _ φ hA m₁ t κ ψ hψ
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hV
  have hfin : FiniteDimensional ℂ V := hA.kfin
  have hle := span_cpt_le_contLeft hA
  let L : V →ₗ[ℂ] (GA E (a - r) → ℂ) := sliceLin μ h𝓕 hr m₁ t κ ∘ₗ Submodule.inclusion hle
  have hR : FiniteDimensional ℂ (LinearMap.range L) := inferInstance
  set S := Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)
  have hS : S.map (Sm E (a - r)).subtype ≤ LinearMap.range L := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨cptRep E a (κ⁻¹ * blkK hr k * κ) φ, Submodule.subset_span ⟨_, rfl⟩⟩, ?_⟩
    funext g
    change slice E μ 𝓕 hr (cptRep E a (κ⁻¹ * blkK hr k * κ) φ).1 m₁ t κ g =
      ψ.1 (g * infGL E (a - r) (Unitary.toUnits k))
    rw [hψ, slice_mul_cpt]
    unfold slice
    congr 1
    funext x
    change φ.1 (_ * _ * _) = _
    simp only [mul_assoc]
    rfl
  have h1 : FiniteDimensional ℂ (S.map (Sm E (a - r)).subtype) := Submodule.finiteDimensional_of_le hS
  exact Module.Finite.equiv (Submodule.equivMapOfInjective (Sm E (a - r)).subtype Subtype.val_injective S).symm

end GlobalTheory.SliceTwo

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_levi_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (ψ : Sm E (a - r)), ψ.1 = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) := by
  atlas_forward_decl GlobalTheory.SliceTwo.slice_kfin
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_levi_moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y, ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  first | exact @GlobalTheory.SliceTwo.Growth.norm_slice_le | exact GlobalTheory.SliceTwo.Growth.norm_slice_le | (intros; apply GlobalTheory.SliceTwo.Growth.norm_slice_le <;> assumption)
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem slice_cpt_mem {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ} (hr : r ≤ a)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) [MeasurableSpace (BlockIx a r → Ad E)]
    [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (φ : Sm E a) (hφ : φ ∈ GlobalTheory.HCF.formsGL E a L W X N) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a)
    (g : GA E (a - r)) :
    (fun k : Kinf E (a - r) => slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) (Unitary.toUnits k))) ∈
      ktypeSub hr κ W := by
  have hm := GlobalTheory.HCFct.constTerm_cptTranslate_mem E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ (Submodule.subset_span hφ)
    (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ))
  refine ⟨_, hm, ?_⟩
  funext k
  exact (slice_mul_cpt μ 𝓕 hr φ.1 m₁ t κ g k).symm

end GlobalTheory.SliceTwo

namespace GlobalTheory.HCFct

open GlobalTheory.SliceTwo

theorem slice2_autForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (L' : Subgroup (GL (Fin (a - r)) (Af E))) (W' : Submodule ℂ (Kinf E (a - r) → ℂ)), IsOpen (L' : Set (GL (Fin (a - r)) (Af E))) ∧ FiniteDimensional ℂ W' ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∃ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∧ (∀ γ g, ψ.1 (ratGL E (a - r) γ * g) = ψ.1 g) ∧ IsOpen {k | finRep E (a - r) k ψ = ψ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) ∧ (∀ g, ∃ (C : ℝ) (M : ℕ), ∀ y, ‖ψ.1 (g * infGL E (a - r) y)‖ ≤ C * height y ^ M) ∧ (∀ k ∈ L', finRep E (a - r) k ψ = ψ) ∧ ∀ g : GA E (a - r), (fun k : Kinf E (a - r) => (cptRep E (a - r) k ψ).1 g) ∈ W' := by
  intro E _ _ _ a L hL W hW X _ N r _ hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  refine ⟨levelSub hr.le t L, ktypeSub hr.le κ W, GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup E a r hr.le t L hL, inferInstance, fun φ hφ m₁ => ?_⟩
  have hA : IsAutForm φ := hφ.1
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hA.level
  have hfix : ∀ k ∈ L, ∀ g, φ.1 (g * finGL E a k) = φ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (hφ.2.1 k hk)) g
  let ψ : Sm E (a - r) := ⟨slice E μ 𝓕 hr.le φ.1 m₁ t κ, GlobalTheory.T.constant_term_slice_cusp_form E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ⟩
  have hlev : ∀ k ∈ levelSub hr.le t L, finRep E (a - r) k ψ = ψ := fun k hk =>
    Subtype.ext (funext fun g => slice_mul_finGL μ 𝓕 hr.le φ.1 L hfix m₁ t κ k hk g)
  refine ⟨ψ, rfl, GlobalTheory.T.constant_term_slice_continuous_invariant E a r hr.le μ 𝓕 hμ h𝓕 h1 φ.1 hc hA.left m₁ t κ, ?_,
    GlobalTheory.T.constant_term_slice_levi_restriction E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ ψ rfl, GlobalTheory.T.constant_term_slice_levi_moderate_growth E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ, hlev,
    fun g => slice_cpt_mem hr.le L W hW X N μ 𝓕 hμ h𝓕 h1 φ hφ m₁ t κ g⟩
  refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup E a r hr.le t L hL).mem_nhds (Subgroup.one_mem _)) fun k hk => hlev k hk)

end GlobalTheory.HCFct

end
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_finite_dimensional_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (L' : Subgroup (GL (Fin (a - r)) (Af E))) (W' : Submodule ℂ (Kinf E (a - r) → ℂ)), IsOpen (L' : Set (GL (Fin (a - r)) (Af E))) ∧ FiniteDimensional ℂ W' ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∃ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∧ (∀ γ g, ψ.1 (ratGL E (a - r) γ * g) = ψ.1 g) ∧ IsOpen {k | finRep E (a - r) k ψ = ψ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) ∧ (∀ g, ∃ (C : ℝ) (M : ℕ), ∀ y, ‖ψ.1 (g * infGL E (a - r) y)‖ ≤ C * height y ^ M) ∧ (∀ k ∈ L', finRep E (a - r) k ψ = ψ) ∧ ∀ g : GA E (a - r), (fun k : Kinf E (a - r) => (cptRep E (a - r) k ψ).1 g) ∈ W' := by
  first | exact @GlobalTheory.HCFct.slice2_autForm | exact GlobalTheory.HCFct.slice2_autForm | (intros; apply GlobalTheory.HCFct.slice2_autForm <;> assumption)
end

section
open Module

namespace GlobalTheory.GenEigenFinOrbit

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem foldr_eq_prod (χ : End ℂ V → ℂ) (zs : List (End ℂ V)) (v : V) :
    zs.foldr (fun z f => z f - χ z • f) v =
      (zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ z))).prod v := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih, Module.End.mul_apply]

theorem map_lt_of_pow_eq_zero {N : Submodule ℂ V} (g : End ℂ V) (K : ℕ)
    (hg : N.map g ≤ N) (hK : ∀ n ∈ N, (g ^ K) n = 0) (hN : N ≠ ⊥) : N.map g < N := by
  refine lt_of_le_of_ne hg fun h => hN ?_
  have hk : ∀ k : ℕ, N.map (g ^ k) = N := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih => rw [pow_succ, Module.End.mul_eq_comp, Submodule.map_comp, h, ih]
  rw [← hk K, eq_bot_iff]
  rintro _ ⟨n, hn, rfl⟩
  simp [hK n hn]

section Family
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)

include hst in
theorem map_prod_le (gs : List (End ℂ V)) (hgs : ∀ g ∈ gs, g ∈ G) : N.map gs.prod ≤ N := by
  induction gs with
  | nil => simp [Module.End.one_eq_id]
  | cons g gs ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp]
    exact (Submodule.map_mono (ih fun x hx => hgs x (by simp [hx]))).trans
      (hst g (hgs g (by simp)))

include hcomm hst hnil in
theorem finrank_map_prod_le [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) :
    finrank ℂ (N.map gs.prod) ≤ finrank ℂ N - gs.length := by
  induction gs with
  | nil => rw [List.prod_nil, Module.End.one_eq_id, Submodule.map_id]; simp
  | cons g gs ih =>
    have hgs' : ∀ x ∈ gs, x ∈ G := fun x hx => hgs x (by simp [hx])
    have hg : g ∈ G := hgs g (by simp)
    specialize ih hgs'
    set M := N.map gs.prod with hM
    have hMN : M ≤ N := map_prod_le G N hst gs hgs'
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMN
    have hc : Commute g gs.prod :=
      Commute.list_prod_right _ _ fun x hx => hcomm g hg x (hgs' x hx)
    have hMst : M.map g ≤ M := by
      rw [hM, ← Submodule.map_comp, ← Module.End.mul_eq_comp, hc.eq, Module.End.mul_eq_comp,
        Submodule.map_comp]
      exact Submodule.map_mono (hst g hg)
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp, ← hM, List.length_cons]
    by_cases h0 : M = ⊥
    · rw [h0, Submodule.map_bot]; simp
    · have hlt := Submodule.finrank_lt_finrank_of_lt
        (map_lt_of_pow_eq_zero g K hMst (fun n hn => hnil g hg n (hMN hn)) h0)
      omega

include hcomm hst hnil in
theorem map_prod_eq_bot [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) (hlen : finrank ℂ N ≤ gs.length) : N.map gs.prod = ⊥ := by
  haveI : FiniteDimensional ℂ (N.map gs.prod) :=
    Submodule.finiteDimensional_of_le (map_prod_le G N hst gs hgs)
  rw [← Submodule.finrank_eq_zero]
  have := finrank_map_prod_le G N K hcomm hst hnil gs hgs
  omega

include hcomm hst hnil in
theorem exists_common_kernel [FiniteDimensional ℂ N] (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ g ∈ G, g n = 0 := by
  classical
  let Pr : ℕ → Prop := fun l => ∃ gs : List (End ℂ V), (∀ g ∈ gs, g ∈ G) ∧ gs.length = l ∧
    N.map gs.prod ≠ ⊥
  have hex : ∃ l, ¬ Pr l := ⟨finrank ℂ N, fun ⟨gs, hgs, hl, hne⟩ =>
    hne (map_prod_eq_bot G N K hcomm hst hnil gs hgs hl.ge)⟩
  have h0 : Pr 0 := ⟨[], by simp, rfl, by simpa [Module.End.one_eq_id] using hN⟩
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact absurd (h ▸ Nat.find_spec hex) (not_not.2 h0)
    · exact h
  obtain ⟨gs, hgs, hl, hne⟩ : Pr (Nat.find hex - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨gs.prod n, map_prod_le G N hst gs hgs ⟨n, hn, rfl⟩, hx0, fun g hg => ?_⟩
  by_contra hne'
  apply Nat.find_spec hex
  refine ⟨g :: gs, ?_, by simp [hl]; omega, ?_⟩
  · intro x hx; simp at hx; rcases hx with rfl | hx; exacts [hg, hgs x hx]
  · intro hbot
    apply hne'
    have : (g :: gs).prod n ∈ N.map (g :: gs).prod := ⟨n, hn, rfl⟩
    rw [hbot] at this
    simpa [Module.End.mul_apply] using this

end Family

theorem sub_pow_coe {U : Submodule ℂ V} (z : End ℂ V) (F : End ℂ U)
    (hF : ∀ u : U, (F u : V) = z u) (c : ℂ) (k : ℕ) (u : U) :
    (((F - c • 1) ^ k) u : V) = ((z - algebraMap ℂ (End ℂ V) c) ^ k) (u : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    simp [hF]

end GlobalTheory.GenEigenFinOrbit

namespace GlobalTheory

open GenEigenFinOrbit in

theorem mem_span_genEigen_of_finiteDimensional_orbit :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V),
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) →
    Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D →
    (∀ (χ' : Module.End ℂ V → ℂ) (u : V),
      u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 →
      (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) →
    ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧
      ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) →
        zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  intro V _ _ A hA X' D ψ hfin hD hX
  set U := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) with hU
  have hUst : ∀ z ∈ A, Set.MapsTo z U U := by
    intro z hz
    have : U.map z ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨z * w, A.mul_mem hz hw, rfl⟩
    exact fun u hu => this ⟨u, hu, rfl⟩
  have hψU : ψ ∈ U := Submodule.subset_span ⟨1, A.one_mem, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : A → End ℂ U, ∀ (i : A) (u : U), (f i u : V) = (i : End ℂ V) u :=
    ⟨fun i => (i : End ℂ V).restrict (hUst i i.2), fun _ _ => rfl⟩
  have hcommAll : ∀ i j, Commute (f i) (f j) := by
    intro i j
    show f i * f j = f j * f i
    ext u
    have := congrArg (fun T : End ℂ V => T (u : V)) (hA i i.2 j j.2)
    simpa [Module.End.mul_apply, hf] using this
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcommAll i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  set T := {ψ' | ψ' ∈ U ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D →
        (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} with hT
  have key : ∀ χ : A → ℂ, ∀ x ∈ ⨅ i, (f i).maxGenEigenspace (χ i),
      (x : V) ∈ Submodule.span ℂ T := by
    classical
    intro χ x hx
    set N := (⨅ i, (f i).maxGenEigenspace (χ i)).map U.subtype with hNdef
    have hxN : (x : V) ∈ N := ⟨x, hx, rfl⟩
    have hNU : N ≤ U := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNU
    obtain ⟨χ', hχ'⟩ : ∃ χ' : End ℂ V → ℂ, ∀ z (hz : z ∈ A), χ' z = χ ⟨z, hz⟩ :=
      ⟨fun y => if h : y ∈ A then χ ⟨y, h⟩ else 0, fun z hz => dif_pos hz⟩
    set G : Set (End ℂ V) := {g | ∃ z ∈ A, g = z - algebraMap ℂ _ (χ' z)} with hG
    have hGA : ∀ g ∈ G, g ∈ A := by
      rintro _ ⟨z, hz, rfl⟩
      exact A.sub_mem hz (A.algebraMap_mem _)
    have hcommG : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a :=
      fun a ha b hb => hA a (hGA a ha) b (hGA b hb)
    have hNst : ∀ z ∈ A, N.map z ≤ N := by
      rintro z hz _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨f ⟨z, hz⟩ y, ?_, hf ⟨z, hz⟩ y⟩
      simp only [SetLike.mem_coe, Submodule.mem_iInf] at hy ⊢
      intro i
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommAll i ⟨z, hz⟩) (χ i) (hy i)
    have hstG : ∀ g ∈ G, N.map g ≤ N := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
      exact N.sub_mem (hNst z hz ⟨v, hv, rfl⟩) (N.smul_mem _ hv)
    have hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ finrank ℂ U) n = 0 := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
      have hy' := (Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hy) ⟨z, hz⟩
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
        LinearMap.mem_ker] at hy'
      rw [hχ' z hz, Submodule.subtype_apply, ← sub_pow_coe z (f ⟨z, hz⟩) (hf ⟨z, hz⟩), hy']
      rfl
    by_cases hN : N = ⊥
    · rw [hN, Submodule.mem_bot] at hxN
      rw [hxN]
      exact zero_mem _
    obtain ⟨n, hnN, hn0, hnker⟩ := exists_common_kernel G N (finrank ℂ U) hcommG hstG hnil hN
    have heig : ∀ z ∈ A, z n = χ' z • n := by
      intro z hz
      have := hnker _ ⟨z, hz, rfl⟩
      simpa [sub_eq_zero] using this
    obtain ⟨χ0, hχ0X, hχ0⟩ := hX χ' n (hNU hnN) hn0 heig
    apply Submodule.subset_span
    refine ⟨hNU hxN, χ0, hχ0X, fun zs hlen hzs => ?_⟩
    rw [foldr_eq_prod]
    have hmap : zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ0 z)) =
        zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ' z)) :=
      List.map_congr_left fun z hz => by rw [hχ0 z (hzs z hz)]
    rw [hmap]
    have hbot := map_prod_eq_bot G N (finrank ℂ U) hcommG hstG hnil
      (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z))
      (by
        intro g hg
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
        exact ⟨z, hzs z hz, rfl⟩)
      (by rw [List.length_map, hlen]; exact (Submodule.finrank_mono hNU).trans hD)
    have hmem : (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod (x : V) ∈
        N.map (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod := ⟨_, hxN, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hmem : (⟨ψ, hψU⟩ : U) ∈ ⨆ χ : A → ℂ, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun x : U => (x : V) ∈ Submodule.span ℂ T) hmem key
    (by simp) (fun x y hx hy => by simpa using add_mem hx hy)

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_genEigen_of_finiteDimensional_orbit_alt : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V), FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) → Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D → (∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 → (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) → ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  first | exact @GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit | exact GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit | (intros; apply GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit <;> assumption)
end

section
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology GlobalTheory.HCF

namespace GlobalTheory.AutGrowth.RankLocal

open GlobalTheory.AutGrowth.KilledFin GlobalTheory.AutGrowth.SmoothFinite

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem finite_forms (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (c : (E →+* ℂ) → ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L ρ c)) := by
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

theorem finiteDimensional_capEigen_maps_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (hWf : FiniteDimensional ℂ W)
    (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)) (hN : N ≤ maps L W hW)
    (hcap : ∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) : FiniteDimensional ℂ N := by
  haveI := hWf
  have hF := finite_forms h L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

theorem finiteDimensional_mapsJ_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (φ : Sm E a) (hφ : IsAutForm φ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) : FiniteDimensional ℂ (mapsJ φ L) := by
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h₀ := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h₀
      exact congrArg Subtype.val h₀
    have hN : FiniteDimensional ℂ N :=
      finiteDimensional_capEigen_maps_rank h L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

theorem exists_finite_space_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := finiteDimensional_mapsJ_rank h φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

theorem tame_of_autForm_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
    (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) →
    ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  intro E _ _ _ a hfin φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := exists_finite_space_rank hfin ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

end GlobalTheory.AutGrowth.RankLocal

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  atlas_forward_decl GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CentreInherit

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

def stab (φ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | finRep E n k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem ktype_of_central {ψ : Sm E n} (hk : FiniteDimensional ℂ (spanK E n ψ)) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') (g : GA E n) :
    (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  let S := spanK E n ψ
  let ev : GA E n → Module.Dual ℂ S := fun h => (LinearMap.proj h).comp ((Sm E n).subtype.comp S.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ h, v.1.1 h = 0 := fun h => hv _ (Submodule.subset_span ⟨h, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have hmem : ∀ k, cptRep E n k ψ ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ m ∈ Submodule.span ℂ (Set.range ev), (fun k => m ⟨cptRep E n k ψ, hmem k⟩) ∈ W' := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨h, rfl⟩ := hx; exact hW h
    | zero => exact W'.zero_mem
    | add x y _ _ hx hy => exact W'.add_mem hx hy
    | smul c x _ hx => exact W'.smul_mem c hx
  let ℓ : Module.Dual ℂ S := (LinearMap.proj g).comp ((Sm E n).subtype.comp (z.comp S.subtype))
  have e : (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) = fun k => ℓ ⟨cptRep E n k ψ, hmem k⟩ := by
    funext k
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simp only [Module.End.mul_apply] at h1
    show _ = (z (cptRep E n k ψ)).1 g
    rw [h1]
  rw [e]
  exact key ℓ (hspan ▸ Submodule.mem_top)

theorem central_of_tame {ψ : Sm E n} (hA : IsAutForm ψ) (htame : ψ ∈ tame E n) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hL : ∀ k ∈ L', finRep E n k ψ = ψ) (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') :
    IsAutForm (z ψ) ∧ (∀ k ∈ L', finRep E n k (z ψ) = z ψ) ∧
      ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  have hs : z ψ ∈ fixL E n (stab ψ) :=
    Zalg_stable (V := fixL E n (stab ψ)) (fun X _ h => lie_mem_fixL _ X h) hz ψ (fun k hk => hk)
  refine ⟨⟨Zalg_stable (V := leftInv E n) (fun X _ h => lie_mem_leftInv X h) hz ψ hA.left, ?_, ?_, ?_,
    growth_of_tame (Zalg_stable (V := tame E n) (fun X _ h => lie_mem_tame X h) hz ψ htame)⟩,
    Zalg_stable (V := fixL E n L') (fun X _ h => lie_mem_fixL L' X h) hz ψ hL,
    ktype_of_central hA.kfin hz W' hW⟩
  · exact isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hA.level.mem_nhds (by simp)) fun k hk => hs k hk)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k ψ)).map z)
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simpa only [Module.End.mul_apply] using h1
  · have := hA.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun y : Module.End ℂ (Sm E n) => y ψ) '' Zalg E n)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    exact Submodule.subset_span ⟨z' * z, mul_mem hz' hz, rfl⟩

end GlobalTheory.CentreInherit

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CentreInherit

theorem centre_preserves_forms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  intro E _ _ _ n hH L' W' ψ hA hL hW ψ' hψ'
  have htame : ψ ∈ tame E n := GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank E n hH ψ hA
  induction hψ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact central_of_tame hA htame hz L' W' hL hW
  | zero => exact ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun k _ => map_zero _, fun g => by
      convert W'.zero_mem using 1; funext k; simp⟩
  | add x y _ _ hx hy =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_add hx.1 hy.1, fun k hk => by rw [map_add, hx.2.1 k hk, hy.2.1 k hk],
      fun g => ?_⟩
    convert W'.add_mem (hx.2.2 g) (hy.2.2 g) using 1
    funext k; simp [map_add]
  | smul c x _ hx =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_smul c hx.1, fun k hk => by rw [map_smul, hx.2.1 k hk], fun g => ?_⟩
    convert W'.smul_mem c (hx.2.2 g) using 1
    funext k; simp [map_smul]

end GlobalTheory.CentreInherit
end
end

section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_gl_inductive_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  first | exact @GlobalTheory.CentreInherit.centre_preserves_forms | exact GlobalTheory.CentreInherit.centre_preserves_forms | (intros; apply GlobalTheory.CentreInherit.centre_preserves_forms <;> assumption)
end

section
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviSliceTwo

set_option maxHeartbeats 1000000 in

theorem secondSlice_mem_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₂ : Submodule ℂ (GA E (a - r) → ℂ), FiniteDimensional ℂ V₂ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₁ : GA E r, (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₂ := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨L', W', hL', hW', hA⟩ := GlobalTheory.T.constant_term_finite_dimensional_span E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨X', D, hX', hB⟩ := GlobalTheory.T.constant_term_finite_dimensional_span_parabolic E a L hL W hW X hX N r hr0 hr μ 𝓕 hμ h𝓕 h1 t κ
  have hfin := hind (a - r) (by omega)
  haveI := hfin L' hL' W' hW' X' hX' D
  refine ⟨(Submodule.span ℂ (GlobalTheory.HCF.formsGL E (a - r) L' W' X' D)).map (Sm E (a - r)).subtype, inferInstance, ?_⟩
  intro φ hφ m₁
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨ψ, hψ, hleft, hlev, hkfin, hgr, hL'ψ, hW'ψ⟩ := hA φ hφ m₁
    obtain ⟨hU, hUD, hchar⟩ := hB φ hφ m₁ ψ hψ
    have hAψ : IsAutForm ψ := ⟨hleft, hlev, hkfin, hU, hgr⟩
    have hdec := GlobalTheory.T.mem_span_genEigen_of_finiteDimensional_orbit_alt (Sm E (a - r)) (Zalg E (a - r))
      (fun x hx y hy => (GlobalTheory.AutGrowth.KilledFin.Zalg_commute hx hy).eq) X' D ψ hU hUD hchar
    refine ⟨ψ, Submodule.span_mono ?_ hdec, hψ⟩
    rintro ψ' ⟨hψ'U, χ, hχ, hnil⟩
    obtain ⟨e1, e2, e3⟩ := GlobalTheory.T.finiteDimensional_forms_gl_inductive_rank E (a - r) hfin L' W' ψ hAψ hL'ψ hW'ψ ψ' hψ'U
    exact ⟨e1, e2, e3, χ, hχ, hnil⟩
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    funext m₂
    simp only [Submodule.coe_subtype, ZeroMemClass.coe_zero, Pi.zero_apply, integral_zero]
  | add x y hx hy ihx ihy =>
    have hint : ∀ z ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ h,
        IntegrableOn (fun x => z.1 (unip x * h)) 𝓕 μ := by
      intro z hz h
      have hP : Continuous z.1 ∧ (∀ γ h, z.1 (ratGL E a γ * h) = z.1 h) := by
        induction hz using Submodule.span_induction with
        | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left⟩
        | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
        | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2 γ h) (hy.2 γ h)⟩
        | smul c x _ hx => exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2 γ h)⟩
      haveI := hμ
      exact CuspidalL2GL.integrableOn_unip hP.1 hP.2 μ h𝓕 h
    obtain ⟨u, hu, eu⟩ := ihx
    obtain ⟨v, hv, ev⟩ := ihy
    refine ⟨u + v, add_mem hu hv, ?_⟩
    funext m₂
    have := congrFun eu m₂
    have := congrFun ev m₂
    simp only [Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply] at *
    rw [integral_add (hint x hx _) (hint y hy _)]
    simp_all
  | smul c x hx ihx =>
    obtain ⟨u, hu, eu⟩ := ihx
    refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
    funext m₂
    have := congrFun eu m₂
    simp only [Submodule.coe_subtype, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at *
    rw [integral_const_mul, this]

end GlobalTheory.LeviSliceTwo

end
end

open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_gl_of_open_level_induction : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₂ : Submodule ℂ (GA E (a - r) → ℂ), FiniteDimensional ℂ V₂ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₁ : GA E r, (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₂ := by
  atlas_forward_decl GlobalTheory.LeviSliceTwo.secondSlice_mem_finiteDimensional
end
