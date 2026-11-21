import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

theorem smoothOnG_exists_contDiff_compactSupport_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (β : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε β →
      HasCompactSupport (fun g : UJ ε => β (umat g)) →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        ∀ g : UJ ε, β (umat g) = F (fun i j => umat g i j) := by
  intro n ε β hβ hc
  obtain ⟨F₀, hF₀, hF₀eq⟩ := smoothOnG_exists_contDiff_extension n ε β hβ

  have hp : Continuous (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
    have hu : Continuous (fun g : UJ ε => umat g) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_pi fun i => continuous_pi fun j => hu.matrix_elem i j

  have hK : IsCompact ((fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) ''
      tsupport (fun g : UJ ε => β (umat g))) := hc.isCompact.image hp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0

  let χ : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x => (χ x : ℂ) * F₀ x, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hF₀
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro g
    have h₀ : F₀ (fun i j => umat g i j) = β (umat g) := hF₀eq (umat g) g.2
    by_cases hz : β (umat g) = 0
    · show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [h₀, hz, mul_zero]
    · have hmem : (fun i j => umat g i j : Fin n → Fin n → ℂ) ∈ Metric.closedBall 0 χ.rIn := by
        refine Metric.closedBall_subset_closedBall ?_ (hR ⟨g, subset_tsupport _ hz, rfl⟩)
        show R ≤ max R 0 + 1
        linarith [le_max_left R 0]
      show β (umat g) = (χ (fun i j => umat g i j) : ℂ) * F₀ (fun i j => umat g i j)
      rw [χ.one_of_mem_closedBall hmem, h₀, Complex.ofReal_one, one_mul]

end GlobalTheory
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

noncomputable def leftMulEntries {n : ℕ} (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Fin n → Fin n → ℂ) ≃L[ℂ] (Fin n → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x i j => ((a : Matrix (Fin n) (Fin n) ℂ) * Matrix.of x) i j
      invFun := fun x i j => (((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.of x) i j
      map_add' := fun x y => by
        have h := Matrix.mul_add (a : Matrix (Fin n) (Fin n) ℂ) (Matrix.of x) (Matrix.of y)
        exact h
      map_smul' := fun c x => by
        have h := Matrix.mul_smul (a : Matrix (Fin n) (Fin n) ℂ) c (Matrix.of x)
        exact h
      left_inv := fun x => by
        have h := Units.inv_mul_cancel_left a (Matrix.of x)
        exact h
      right_inv := fun x => by
        have h := Units.mul_inv_cancel_left a (Matrix.of x)
        exact h }

private lemma inUJ_of_mem_Kset' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : Formalism.REAL.inUJ ε g := by
  have hu : star g * g = 1 := Unitary.star_mul_self_of_mem hg.1
  unfold Formalism.REAL.inUJ
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hu, Matrix.one_mul]

private lemma mul_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hg' : g' ∈ Formalism.REAL.Kset ε) : g * g' ∈ Formalism.REAL.Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hg'.1, ?_⟩
  rw [Matrix.mul_assoc, hg'.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

private lemma exists_UJ_umat_eq_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : ∃ k : Formalism.REAL.UJ ε, umat k = g :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_Kset' hg⟩, rfl⟩

theorem exists_smooth_average_eq_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → w ∈ lowKSub ε lam σ → w ≠ 0 → ∀ u ∈ lowKSub ε lam σ, ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g : UJ ε, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) := by
  intro n ε H _ _ _ σ lam w hrep hK hw hw0 u hu
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have humat : Continuous fun g : Formalism.REAL.UJ ε => umat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w :=
    (hrep.2.2 w).comp_continuous humat hmem
  have he : Continuous fun g : Formalism.REAL.UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ) := humat

  have hint : ∀ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) →
      Integrable (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
    intro F hFd _ hFg
    have hc : Continuous fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) := hFd.continuous.comp he
    exact (hc.smul hcont).integrable_of_hasCompactSupport
      (hFg.smul_right (f' := fun g : Formalism.REAL.UJ ε => σ (umat g) w))

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hrep hK
  obtain ⟨F0, hF0d, hF0c, hF0e⟩ :=
    smoothOnG_exists_contDiff_compactSupport_extension n ε α hαs hαc
  have hF0g : HasCompactSupport (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) := by
    have hfun : (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) = fun g => α (umat g) :=
      funext fun g => (hF0e g).symm
    rw [hfun]
    exact hαc
  have hbase : ∫ g, F0 (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun v => ?_
    rw [← integral_inner (hint F0 hF0d hF0c hF0g) v]
    simp_rw [inner_smul_right, ← hF0e]
    exact hαfix w hw v

  let T : Submodule ℂ H :=
    { carrier := {v | ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
          HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) ∧
          v = ∫ g, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε)}
      add_mem' := by
        rintro _ _ ⟨F1, h1d, h1c, h1g, rfl⟩ ⟨F2, h2d, h2c, h2g, rfl⟩
        refine ⟨fun y => F1 y + F2 y, h1d.add h2d, h1c.add h2c, h1g.add h2g, ?_⟩
        rw [← integral_add (hint F1 h1d h1c h1g) (hint F2 h2d h2c h2g)]
        simp only [add_smul]
      zero_mem' := by
        refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, HasCompactSupport.zero, ?_⟩
        simp
      smul_mem' := by
        rintro c _ ⟨F1, h1d, h1c, h1g, rfl⟩
        refine ⟨fun y => c * F1 y, contDiff_const.mul h1d, h1c.mul_left, h1g.mul_left, ?_⟩
        rw [← integral_smul]
        simp only [mul_smul] }

  have hgen : ∀ g ∈ Formalism.REAL.Kset ε, σ g w ∈ T := by
    intro g hg
    obtain ⟨k, rfl⟩ := exists_UJ_umat_eq_of_mem_Kset hg
    let a : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    have hshift : ∀ x : Formalism.REAL.UJ ε,
        leftMulEntries a (fun i j => umat x i j) = fun i j => umat (k⁻¹ * x) i j := fun x => rfl
    refine ⟨fun y => F0 (leftMulEntries a y), ?_, ?_, ?_, ?_⟩
    · exact hF0d.comp ((leftMulEntries a).contDiff.restrict_scalars ℝ)
    · exact hF0c.comp_homeomorph (leftMulEntries a).toHomeomorph
    · simp only [hshift]
      exact hF0g.comp_homeomorph (Homeomorph.mulLeft k⁻¹)
    · simp only [hshift]
      have hinv := integral_mul_left_eq_self (μ := muG ε)
        (fun x : Formalism.REAL.UJ ε => F0 (fun i j => umat (k⁻¹ * x) i j) • σ (umat x) w) k
      simp only [inv_mul_cancel_left] at hinv
      rw [← hinv]
      have hmul : ∀ x : Formalism.REAL.UJ ε, F0 (fun i j => umat x i j) • σ (umat (k * x)) w
          = σ (umat k) (F0 (fun i j => umat x i j) • σ (umat x) w) := by
        intro x
        rw [map_smul]
        congr 1
        show σ (umat k * umat x) w = σ (umat k) (σ (umat x) w)
        rw [hrep.1.2 _ (hmem k) _ (hmem x)]
        rfl
      simp_rw [hmul]
      rw [ContinuousLinearMap.integral_comp_comm _ (hint F0 hF0d hF0c hF0g), hbase]

  let S' : Submodule ℂ H := Submodule.span ℂ {v | ∃ g ∈ Formalism.REAL.Kset ε, v = σ g w}
  have hS'le : S' ≤ lowKSub ε lam σ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hK.2.1 g hg w hw
  have hS'st : IsKStableOn ε σ S' := by
    intro g hg v hv
    have hle : S' ≤ S'.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', hg', rfl⟩
      show σ g (σ g' w) ∈ S'
      refine Submodule.subset_span ⟨g * g', mul_mem_Kset hg hg', ?_⟩
      rw [hrep.1.2 g (inUJ_of_mem_Kset' hg) g' (inUJ_of_mem_Kset' hg')]
      rfl
    exact hle hv
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
    ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  have hwS' : w ∈ S' := Submodule.subset_span ⟨1, h1K, by rw [hrep.1.1]; rfl⟩
  have hS'eq : S' = lowKSub ε lam σ := by
    rcases hK.2.2.1 S' hS'le hS'st with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hwS')) hw0
    · exact h
  have huS' : u ∈ S' := by rw [hS'eq]; exact hu
  have huT : u ∈ T := Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hgen g hg) huS'
  obtain ⟨F, hFd, hFc, _, hFu⟩ := huT
  exact ⟨F, hFd, hFc, hFu⟩

end GlobalTheory
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → w ∈ lowKSub ε lam σ → w ≠ 0 → ∀ u ∈ lowKSub ε lam σ, ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g : UJ ε, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) := by
  first | exact @GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub | exact GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub | (intros; apply GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.AverageDeriv

theorem hasDerivAt_average {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G → (H →L[ℂ] H)} (hσ : IsURep σ) (w : H) {a : ℝ → G} (ha : Continuous a) (ha0 : a 0 = 1)
    {f f' : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f')
    (hfc' : HasCompactSupport f')
    (hd : ∀ g t, HasDerivAt (fun s => f ((a s)⁻¹ * g)) (f' ((a t)⁻¹ * g)) t) :
    HasDerivAt (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) (∫ g, f' g • σ g w ∂μ) 0 := by
  obtain ⟨-, hmul, hnorm, hcont⟩ := hσ
  have hcw : Continuous fun g => σ g w := hcont w

  have key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ := by
    intro t
    have hint : Integrable (fun g => f g • σ g w) μ :=
      (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)
    rw [← (σ (a t)).integral_comp_comm hint]
    rw [← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]
    congr 1
    funext g
    rw [map_smul, inv_mul_cancel_left, hmul]
    rfl

  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support hfc'
  set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)
  have hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0 := by
    intro s hs g hg
    by_contra h
    apply hg
    refine ⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hs
    exact Set.Ioo_subset_Icc_self hs
  have hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet
  have hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w :=
    fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w)
    (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun s => (hcont_tr f hf s).aestronglyMeasurable)
    (by
      simp only [ha0, inv_one, one_mul]
      exact (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))
    (hcont_tr f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g s hs => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])
    hbound_int
    (Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))
  have hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ :=
    funext key
  rw [hfun]
  simpa only [ha0, inv_one, one_mul] using hder.2

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  simp

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)
  rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU ((-t) • X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← expU_add, add_neg_cancel, zero_smul, expU_zero]

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hcexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • A) := by
    intro A
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    exact (differentiable_exp_smul_const ℝ A).continuous
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · have e : (fun t : ℝ => (((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun t : ℝ => NormedSpace.exp (t • X.1) := by
      funext t
      rw [← Submodule.coe_smul]
      exact uMat_expU (t • X)
    have h := hcexp X.1
    rw [← e] at h
    exact h
  · have e : (fun t : ℝ => ((((expU (t • X) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
        (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun t : ℝ => NormedSpace.exp (t • (-X.1)) := by
      funext t
      have h1 := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) (expU_inv X t)
      refine h1.trans ((uMat_expU _).trans ?_)
      rw [Submodule.coe_smul, neg_smul, smul_neg]
    have h := hcexp (-X.1)
    rw [← e] at h
    exact h

theorem hasDerivAt_exp_mul_entry {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * (NormedSpace.exp (t • X) * Y)) i j) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y
  let l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j)
      ((X * NormedSpace.exp (t • X) * Y) i j) t := h2
  rw [← mul_assoc]
  exact h3

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) = NormedSpace.exp (t • (-X.1)) * uMat g := by
  rw [expU_inv]
  show uMat (expU ((-t) • X)) * uMat g = _
  rw [uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]

theorem hasDerivAt_orbit_average : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  intro B F E w hσ hF hFc

  have hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v)) := rfl
  haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance
  let c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    fun g v i j => uMat (g v) i j
  have hc : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1

  let Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ]
      (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    { toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j
      map_add' := by
        intro M N
        funext v i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r M
        funext v i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }
  let L := LinearMap.toContinuousLinearMap Lm
  let F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun M => fderiv ℝ F M (L M)
  have hF's : ContDiff ℝ ∞ F' := (contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff
  have hF'c : HasCompactSupport F' := by
    refine (hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_
    intro h0
    apply hM
    show fderiv ℝ F M (L M) = 0
    rw [h0]
    rfl
  refine ⟨F', hF's, hF'c, ?_⟩
  let a : ℝ → B.I.Ginf := fun t v => expU (t • E v)
  have ha : Continuous a := continuous_pi fun v => continuous_expU (E v)
  have ha0 : a 0 = 1 := by
    funext v
    show expU ((0 : ℝ) • E v) = 1
    rw [zero_smul, expU_zero]
  have hcc : Continuous c := hc.continuous
  have hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t := by
    intro g t
    let p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
      fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j
    have hp : ∀ s, c ((a s)⁻¹ * g) = p s := by
      intro s
      funext v i j
      show uMat ((expU (s • E v))⁻¹ * g v) i j = _
      rw [uMat_inv_mul]
    have hp' : HasDerivAt p (L (p t)) t := by
      refine hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
      exact hasDerivAt_exp_mul_entry _ _ t i j
    have hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h := hFd.comp_hasDerivAt t hp'
    simp only [hp]
    exact h
  have main := hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g))
    (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc)
    (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd
  exact main

end GlobalTheory.AverageDeriv
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  first | exact @GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | exact GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | (intros; apply GlobalTheory.AverageDeriv.hasDerivAt_orbit_average <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem isClosedEmbedding_entries {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ)) := by
  have key := (uJEmb n ε).1
  exact key

theorem isClosedEmbedding_entries_inf (I : AutInst) :
    Topology.IsClosedEmbedding (fun g : I.Ginf =>
      (fun v i j => uMat (g v) i j : InfinitePlace I.F → Fin I.n → Fin I.n → ℂ)) := by
  have h : ∀ v : InfinitePlace I.F, Topology.IsClosedEmbedding
      (fun g : Formalism.REAL.UJ (I.ε v) => (fun i j => uMat g i j : Fin I.n → Fin I.n → ℂ)) :=
    fun v => isClosedEmbedding_entries (I.ε v)
  exact Topology.IsClosedEmbedding.piMap h

theorem integrable_loc {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {F : (Fin n → Fin n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
  have hemb := isClosedEmbedding_entries ε
  have hrep : Continuous (fun g : UJ ε => σ (umat g) w) :=
    (hσ.2.2 w).comp_continuous hemb.continuous (fun g => g.2)
  have hcs : HasCompactSupport (fun g : UJ ε => F (fun i j => umat g i j) • σ (umat g) w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem integrable_inf (B : RowsAut) (hσ : IsURep B.σs) (w : B.Hs)
    {F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) (muInf B.I) := by
  have hemb := isClosedEmbedding_entries_inf B.I
  have hrep : Continuous (fun g : B.I.Ginf => B.σs g w) := hσ.2.2.2 w
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by
    rw [hμ]
    infer_instance
  have hcs : HasCompactSupport (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g w) :=
    (hc.comp_isClosedEmbedding hemb).smul_right
  exact ((hF.comp hemb.continuous).smul hrep).integrable_of_hasCompactSupport hcs

theorem tens_average (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hσ : IsURep B.σs)
    (w : ∀ v, B.H v) (F : InfinitePlace B.I.F → (Fin B.I.n → Fin B.I.n → ℂ) → ℂ)
    (hF : ∀ v, ContDiff ℝ ∞ (F v)) (hc : ∀ v, HasCompactSupport (F v)) :
    ∃ G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      B.tens (fun v => ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v) ∂(muG (B.I.ε v))) =
        ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I) := by
  classical
  obtain ⟨hin, hact, hden⟩ := B.tens_spec
  set G : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun x => ∏ v, F v (x v) with hGdef
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_prod (fun v _ => (hF v).comp (contDiff_apply ℝ (Fin B.I.n → Fin B.I.n → ℂ) v))
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro' (isCompact_univ_pi fun v => hc v)
      (isClosed_set_pi fun v _ => isClosed_tsupport (F v)) ?_
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨v, hv⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)
  refine ⟨G, hGs, hGc, ?_⟩
  refine eq_of_inner_eq_on_dense_span hden ?_
  rintro y ⟨x, rfl⟩
  have hloc : ∀ v, ⟪x v, ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) • B.σ v (umat g) (w v)
        ∂(muG (B.I.ε v))⟫_ℂ =
      ∫ g : UJ (B.I.ε v), F v (fun i j => umat g i j) * ⟪x v, B.σ v (umat g) (w v)⟫_ℂ ∂(muG (B.I.ε v)) := by
    intro v
    rw [← integral_inner (integrable_loc (hU v) (w v) (hF v).continuous (hc v))]
    simp only [inner_smul_right]
  have hglob : ⟪B.tens x, ∫ g, G (fun v i j => uMat (g v) i j) • B.σs g (B.tens w) ∂(muInf B.I)⟫_ℂ =
      ∫ g : B.I.Ginf, ∏ v, (F v (fun i j => uMat (g v) i j) * ⟪x v, B.σ v (uMat (g v)) (w v)⟫_ℂ)
        ∂(muInf B.I) := by
    rw [← integral_inner (integrable_inf B hσ (B.tens w) hGs.continuous hGc)]
    congr 1
    funext g
    rw [inner_smul_right, hact, hin, Finset.prod_mul_distrib]
  have hμ : muInf B.I = Measure.pi fun v => muG (B.I.ε v) := rfl
  have hprod := integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v (h : UJ (B.I.ε v)) => F v (fun i j => uMat h i j) * ⟪x v, B.σ v (uMat h) (w v)⟫_ℂ)
  rw [hglob, hin, hμ]
  refine Eq.trans ?_ hprod.symm
  exact Finset.prod_congr rfl (fun v _ => hloc v)

theorem exists_smooth_average : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro hSL B d hd P u hu
  have hσ : IsURep B.σs := (tensorRep B d hd).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hd v).2.1.2.2.1

  let Av : B.Hs → Prop := fun y => ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ,
    ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)
  have hzero : Av 0 := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_⟩
    simp only [zero_smul, integral_zero]
  have hadd : ∀ a b, Av a → Av b → Av (a + b) := by
    rintro a b ⟨F₁, hF₁, hc₁, rfl⟩ ⟨F₂, hF₂, hc₂, rfl⟩
    refine ⟨F₁ + F₂, hF₁.add hF₂, hc₁.add hc₂, ?_⟩
    rw [← integral_add (integrable_inf B hσ _ hF₁.continuous hc₁)
      (integrable_inf B hσ _ hF₂.continuous hc₂)]
    congr 1
    funext g
    rw [Pi.add_apply, add_smul]
  have hsmul : ∀ (c : ℂ) a, Av a → Av (c • a) := by
    rintro c a ⟨F₁, hF₁, hc₁, rfl⟩
    refine ⟨fun x => c * F₁ x, contDiff_const.mul hF₁, hc₁.mul_left, ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have hbase : ∀ x : ∀ v, B.H v, (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (B.tens x) := by
    intro x hx
    have hloc : ∀ v, ∃ F : (Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        x v = ∫ g : UJ (B.I.ε v), F (fun i j => umat g i j) • B.σ v (umat g) (B.w v) ∂(muG (B.I.ε v)) := by
      intro v
      have hlow := (hd v).2.2.1
      have hw0 : B.w v ≠ 0 := by
        intro h0
        have h1 := hlow.1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have hK := (hSL B.I.n (B.I.ε v) (B.lam v) (hd v).1 (B.H v) (B.σ v) (hd v).2.1).1
      exact GlobalTheory.T.exists_smooth_average_eq_of_mem_lowKSub' B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (B.w v) (hU v) hK hlow.2 hw0 (x v) (hx v)
    choose Fl hFl hcl hxl using hloc
    obtain ⟨G, hG, hcG, hEq⟩ := tens_average B hU hσ B.w Fl hFl hcl
    refine ⟨G, hG, hcG, ?_⟩
    rw [← hEq]
    congr 1
    funext v
    exact hxl v

  have hstep : ∀ (E : gInf B) y, Av y → Av (dAct B E y) := by
    rintro E y ⟨F₁, hF₁, hc₁, rfl⟩
    obtain ⟨F', hF', hc', hder⟩ := GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage B F₁ E (B.tens B.w) hσ hF₁ hc₁
    exact ⟨F', hF', hc', hder.deriv⟩
  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (x : ∀ v, B.H v),
      (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → Av (wordAct B l (B.tens x)) := by
    intro l x hx
    induction l with
    | nil => exact hbase x hx
    | cons X l ih => exact hstep (atPlace B X.1 X.2) _ ih
  have hu' : u ∈ Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v)))
      (x : ∀ v, B.H v), l.length ≤ P ∧ (∀ v, x v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧
        y = wordAct B l (B.tens x)} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, x, -, hx, rfl⟩ := hy
    exact hword l x hx
  | zero => exact hzero
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

end GlobalTheory.StepAverage
end
