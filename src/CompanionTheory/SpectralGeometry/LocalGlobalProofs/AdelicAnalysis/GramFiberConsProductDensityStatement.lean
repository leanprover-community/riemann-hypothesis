import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtension
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductMeasurable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame | exact GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame | (intros; apply GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem measurable_fin_cons {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    {f : Ω → A} {g : Ω → Fin n → A} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => (Fin.cons (f p) (g p) : Fin (n + 1) → A) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa using measurable_pi_iff.1 hg j

theorem measurable_scl {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {N m : ℕ} :
    Measurable fun p : K × (Fin m → Fin N → K) => scl p.1 p.2 := by
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (measurable_pi_iff.1 (measurable_pi_iff.1 (measurable_snd (α := K) (β := Fin m → Fin N → K)) a) i).mul measurable_fst

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem corner_half_trace_gram_cons (σ : E →ₐ[F] E) {N n : ℕ} (J₂ : Matrix (Fin N) (Fin N) E)
    (y : Fin 1 → Fin N → R ⊗[F] E) (Z : Fin n → Fin N → R ⊗[F] E) :
    s0 R (gramR R σ J₂ (Fin.cons (y 0) Z : Fin (n + 1) → Fin N → R ⊗[F] E)) =
      s0 R (gramR R σ J₂ y) := by
  simp [s0, gramR]

theorem isUnit_tmul_one {x : R} (hx : IsUnit x) : IsUnit (x ⊗ₜ[F] (1 : E)) := by
  simpa using hx.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)

theorem tmul_one_eq_smul (x : R) : x ⊗ₜ[F] (1 : E) = x • (1 : R ⊗[F] E) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem continuous_tmul_one [TopologicalSpace R] :
    Continuous fun x : R => x ⊗ₜ[F] (1 : E) := by
  haveI : ContinuousSMul R (R ⊗[F] E) := ModuleTopology.continuousSMul R (R ⊗[F] E)
  have h : Continuous fun x : R => x • (1 : R ⊗[F] E) := by fun_prop
  simpa only [tmul_one_eq_smul] using h

end

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}

include R in
theorem measurable_inv_a (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    Measurable fun x : R => ((((a x)⁻¹ : Rˣ) : R)) := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := D.hR
  classical
  have h1 : ContinuousOn (fun x : R => ((((a x)⁻¹ : Rˣ) : R))) B₀ :=
    Units.continuous_val.comp_continuousOn (continuous_inv.comp_continuousOn D.hac)
  have h2 : ContinuousOn (fun _ : R => (1 : R)) B₀ᶜ := continuousOn_const
  have h3 := h1.measurable_piecewise h2 D.hB₀.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ B₀
  · simp [hx]
  · simp [hx, D.hoff x hx]

theorem measurable_sTil (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    Measurable (sTil σ J t s a) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, hsigc, htrc, -, hbw, -, hgramc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hq : Continuous fun y : Fin 1 → Fin (M + 1) → R ⊗[F] E =>
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) := by
    unfold s0
    exact continuous_const.mul (htrc.comp ((hgramc 1 (M + 1) _).matrix_elem 0 0))
  have hw : Measurable fun y : Fin 1 → Fin (M + 1) → R ⊗[F] E =>
      (((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) :=
    (continuous_tmul_one R (F := F) (E := E)).measurable.comp ((measurable_inv_a D).comp hq.measurable)
  exact D.hs.comp (measurable_scl.comp (hw.prodMk measurable_id))

theorem measurable_chi (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (chi σ J t s a b lam φ) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨h1, h2, h3, h4, h5, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  have hact' := (hact n).1.measurable
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := by unfold coordW; infer_instance
  have hG : Measurable fun q : ((Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E)) ×
      (Fin n → Fin M → R ⊗[F] E) =>
      φ (Fin.cons (q.1.1 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a q.1.1)
        (fun j => Fin.cons (q.1.2 j) (q.2 j)))) := by
    refine hφ.comp (measurable_fin_cons ?_ ?_)
    · exact measurable_pi_iff.1 (measurable_fst.comp measurable_fst) 0
    · refine hact'.comp (((measurable_sTil D).comp (measurable_fst.comp measurable_fst)).prodMk ?_)
      refine measurable_pi_iff.2 fun j => measurable_fin_cons ?_ ?_
      · exact measurable_pi_iff.1 (measurable_snd.comp measurable_fst) j
      · exact measurable_pi_iff.1 measurable_snd j
  exact (hG.lintegral_prod_right' (ν := coordW R b lam n M)).lintegral_prod_right'
    (ν := Measure.pi fun _ : Fin n => coordK R b lam)

theorem chi_eq_zero (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀) :
    chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) y = 0 := by
  unfold chi
  have hz : ∀ Z : Fin n → Fin (M + 1) → R ⊗[F] E,
      (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ (Fin.cons (y 0) Z) = 0 := by
    intro Z
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨S, hS, hSe⟩
    apply hy
    rw [← corner_half_trace_gram_cons R σ _ y Z, ← hSe]
    exact hS.1
  simp [hz]

theorem isUnit_gram (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∈ B₀) :
    IsUnit (gramR R σ (blockOne (algebraMap F E t) J) y).det := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g, -, hg⟩ := hg (M + 1) _ hJ'
  obtain ⟨-, hh, -⟩ := hermScal_main F E σ D.hCM R d b
  have hS := hh (g y)
  rw [← hg y] at hS
  have hx : IsUnit (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)) := by
    rw [D.hsq _ hy]
    exact ((Units.isUnit _).pow 2).mul ((IsUnit.mk0 t D.ht).map (algebraMap F R))
  have h00 : gramR R σ (blockOne (algebraMap F E t) J) y 0 0 =
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ⊗ₜ[F] (1 : E) := by
    have := congrArg (fun S : HermR R σ 1 => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) hS
    simp only [← hg y] at this
    simpa [hermScal, s0] using this.symm
  rw [Matrix.det_fin_one, h00]
  exact isUnit_tmul_one R hx

end Main

theorem first_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht

  have hUm : MeasurableSet (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) := by
    obtain ⟨-, -, -, hbor, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
    obtain ⟨g, hgc, hg⟩ := hg (M + 1) _ hJ'
    have hBo := (GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2.2.2.2
    have : (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) = g ⁻¹' Bset R σ t a B₀ := by
      ext v
      constructor
      · rintro ⟨S, hS, hSe⟩
        have : S = g v := Subtype.ext (hSe.trans (hg v))
        simpa [this] using hS
      · intro hv
        exact ⟨g v, hv, (hg v).symm⟩
    rw [this]
    exact (hBo.preimage hgc).measurableSet
  have hφ' := hφ.indicator hUm
  have hchi := measurable_chi D hφ'

  obtain ⟨-, -, -, hbor1, hg1⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R 1
  obtain ⟨g₁, hg₁c, hg₁⟩ := hg1 (M + 1) _ hJ'
  obtain ⟨hUo, -, -, -, -, hae⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  have hU₁ : MeasurableSet {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
      IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} := by
    have : {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} = g₁ ⁻¹' Unt σ R 1 := by
      ext X
      simp [Unt, hg₁ X]
    rw [this]
    exact (hUo.preimage hg₁c).measurableSet
  obtain ⟨hh, hh2, hh3⟩ := hermScal_main F E σ D.hCM R d b
  have hemb : MeasurableEmbedding (hermScal R σ) := (hh.homeomorph _).measurableEmbedding
  have hs0 : ∀ x : R, s0 R ((hermScal R σ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = x :=
    fun x => hh.injective (hh2 (hermScal R σ x))
  set χ := chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) with hχ
  have hzero : ∀ y, s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀ → χ y = 0 :=
    fun y hy => chi_eq_zero D φ hy

  have e1 : ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hUm]
    exact GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section F E σ D.hCM M _ hJ' R D.hR d b lam D.hlam n (sTil σ J t s a) (measurable_sTil D) _ hφ'
  have e2 : ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) =
      ∫⁻ y in {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hU₁]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}
    · exact (Set.indicator_of_mem hy χ).symm
    · rw [Set.indicator_of_notMem hy, hzero y fun h => hy (isUnit_gram D h)]
  have e3 := D.hm₁.2.1 χ hchi
  rw [← hh3 lam D.hlam, hemb.lintegral_map] at e3
  have e4 : ∫⁻ x, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam = ∫⁻ x in B₀, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam := by
    rw [← lintegral_indicator D.hB₀.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B₀
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hae (hermScal R σ x)] with y hy
      refine hzero y ?_
      rw [hy, hs0]
      exact hx
  rw [e1, e2, e3, e4]
  refine setLIntegral_congr_fun D.hB₀.measurableSet fun x hx => ?_
  have hm : m₁ (hermScal R σ x) =
      κ₁ (a x) • (m₁ (hermScal R σ (algebraMap F R t))).map (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) := by
    have := D.hscale (a x)
    rwa [← D.hsq x hx] at this
  have hsm : Measurable (scl (N := M + 1) (n := 1) (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) :=
    measurable_scl.comp (measurable_const.prodMk measurable_id)
  simp only [hm]
  rw [lintegral_smul_measure, lintegral_map hchi hsm]
  rfl

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_product_unfold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1.first_step <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_scalar_tmul (σ : E →ₐ[F] E) (α : R) :
    sigR R σ (α ⊗ₜ[F] (1 : E)) = α ⊗ₜ[F] (1 : E) := by
  simp [sigR]

theorem gramR_scl_tmul (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (α : R)
    (y : Fin 1 → Fin N → R ⊗[F] E) (i j : Fin 1) :
    gramR R σ J (scl (α ⊗ₜ[F] (1 : E)) y) i j =
      (α ⊗ₜ[F] (1 : E)) * (α ⊗ₜ[F] (1 : E)) * gramR R σ J y i j := by
  simp only [gramR, hR, hform, scl, map_mul, sigR_scalar_tmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem corner_half_trace_of_pure_tensor [CharZero F] {d : ℕ} (b : Module.Basis (Fin d) F E) (hd : Module.finrank F E = 2)
    (x : R) (S : Matrix (Fin (0 + 1)) (Fin (0 + 1)) (R ⊗[F] E)) (h : S 0 0 = x ⊗ₜ[F] (1 : E)) :
    s0 R S = x := by
  have hd2 : d = 2 := by
    rw [← hd, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd2
  have e : x ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) x := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [s0, h, e, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b), Fintype.card_fin,
    two_nsmul, ← two_mul, ← mul_assoc]
  have : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    simp
  rw [this, one_mul]

end Alg

theorem chi_at_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id D.hR
  have hJt := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJt R
  obtain ⟨-, -, -, hBH, hliftn⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  obtain ⟨-, -, -, -, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R (n + 1)
  obtain ⟨hUo, -, hoff, -⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨g, -, hg⟩ := hlift (M + 1) _ hJt
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).1 x hx
  have hd : Module.finrank F E = 2 := D.hCM.2.2.1
  set u : R := ((a x : Rˣ) : R) with hu

  have hy00 : gramR R σ (blockOne (algebraMap F E t) J) y₀ 0 0 = algebraMap F R t ⊗ₜ[F] (1 : E) := by
    rw [hy₀]; rfl
  have hG : gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀) 0 0 =
      x ⊗ₜ[F] (1 : E) := by
    rw [gramR_scl_tmul, hy00, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have hq : u ^ 2 * algebraMap F R t = x := (D.hsq x hx).symm
    rw [mul_one, mul_one, ← pow_two, hq]
  have hs0 : s0 R (gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀)) = x :=
    corner_half_trace_of_pure_tensor R b hd x _ hG
  have hsT : sTil σ J t s a (scl (u ⊗ₜ[F] (1 : E)) y₀) = s y₀ := by
    unfold sTil
    rw [hs0]
    congr 1
    funext i j
    simp only [scl, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hu, Units.mul_inv]
    exact mul_one _
  have hsec := congrFun (D.hsec y₀ hy₀) 0
  have hcons : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      (Fin.cons (scl (u ⊗ₜ[F] (1 : E)) y₀ 0)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (fun j => Fin.cons (c j) (X j))) :
          Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) := by
    intro c X
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have e : (Fin.cons (u ⊗ₜ[F] (1 : E)) (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) =
          (u ⊗ₜ[F] (1 : E)) • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
        funext k
        refine Fin.cases ?_ (fun l => ?_) k <;> simp
      simp only [Fin.cons_zero, vec, actW, actTup]
      rw [e, Matrix.mulVec_smul]
      simp only [actW, actTup] at hsec
      rw [hsec]
      funext k
      simp [scl, mul_comm]
    · simp [vec, actW, actTup]
  have hmem : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) ∈
        (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) ↔
      X ∈ {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    intro c X
    have hinv := (hact (n + 1)).2.2.2 (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)
    simp only [Uset, Set.mem_preimage, hinv, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, ⟨-, hSu⟩, hS⟩
      have := (hcoord c X S hS).2.2
      rwa [this] at hSu
    · intro hX
      have h3 := hcoord c X (g (vec (u ⊗ₜ[F] (1 : E)) c X)) (hg _).symm
      refine ⟨g (vec (u ⊗ₜ[F] (1 : E)) c X), ⟨?_, ?_⟩, (hg _).symm⟩
      · rw [h3.1]; exact hx
      · rw [h3.2.2]; exact hX
  haveI := hBor n M
  haveI := hBor (n + 1) (M + 1)
  have hUt : MeasurableSet (Unt σ R n) := hUo.measurableSet
  have hUd : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    obtain ⟨g', hg'c, hg'⟩ := hliftn M J D.hJ
    have e : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = g' ⁻¹' Unt σ R n := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hg' X]
    rw [e]
    exact (hUo.preimage hg'c).measurableSet
  have hψ : ∀ c : Fin n → R ⊗[F] E, Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
      φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) := by
    intro c
    have hv : Continuous fun X : Fin n → Fin M → R ⊗[F] E => vec (u ⊗ₜ[F] (1 : E)) c X := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · refine continuous_pi fun k => ?_
        refine Fin.cases ?_ (fun l => ?_) k
        · exact continuous_const
        · exact (continuous_apply l).comp (continuous_apply j)
    have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
        actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) :=
      (hact (n + 1)).1.comp (continuous_const.prodMk hv)
    exact hφ.comp hc.measurable
  unfold chi
  rw [hsT]
  refine lintegral_congr fun c => ?_
  calc _ = ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}.indicator (fun X =>
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))) X
        ∂(coordW R b lam n M) := by
        refine lintegral_congr fun X => ?_
        rw [hcons c X]
        by_cases h : X ∈ {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem c X).2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem c X).1 h'))]
    _ = ∫⁻ X in {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det},
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))
        ∂(coordW R b lam n M) := lintegral_indicator hUd _
    _ = ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀)
            (vec (u ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) :=
        D.hm'.2.1 _ (hψ c)
    _ = _ := by
        rw [← lintegral_indicator hUt]
        refine lintegral_congr fun S' => ?_
        by_cases h : S' ∈ Unt σ R n
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, hoff S' h, lintegral_zero_measure]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_product_fold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

theorem measurable_vec {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) :
    Measurable (fun p : (Fin n → K) × (Fin n → Fin M → K) => vec α p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [vec, Fin.cons_zero]
    exact measurable_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply i').comp measurable_fst
    · simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply j').comp ((measurable_pi_apply i').comp measurable_snd)

theorem swap_through_fibres {Y C X H : Type} [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace X]
    [MeasurableSpace H] (μ₁ : Measure Y) (μc : Measure C) (μ : Measure X) (ν : Measure H)
    [SFinite μ₁] [SFinite μc] [SFinite μ] (U : Set X) (W : Set H) (hW : MeasurableSet W)
    (m : H → Measure X) (hm : ∀ S, SFinite (m S)) (hoff : ∀ S, S ∉ W → m S = 0)
    (hfib : ∀ ψ : X → ℝ≥0∞, Measurable ψ → ∫⁻ v in U, ψ v ∂μ = ∫⁻ S, ∫⁻ v, ψ v ∂(m S) ∂ν)
    (f : Y → C → X → ℝ≥0∞) (hf : Measurable fun p : Y × C × X => f p.1 p.2.1 p.2.2) :
    ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁ =
      ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by
  have restr : ∀ G : H → ℝ≥0∞, (∀ S, S ∉ W → G S = 0) → ∫⁻ S in W, G S ∂ν = ∫⁻ S, G S ∂ν := by
    intro G hG
    rw [← lintegral_indicator hW]
    refine lintegral_congr fun S => ?_
    by_cases hS : S ∈ W
    · simp [hS]
    · simp [hS, hG S hS]
  have hfyc : ∀ y c, Measurable (f y c) := fun y c =>
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hfc : ∀ c, Measurable fun p : Y × X => f p.1 c p.2 := fun c =>
    hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have e1 : ∀ y c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν = ∫⁻ v in U, f y c v ∂μ := by
    intro y c
    rw [hfib _ (hfyc y c)]
    refine restr _ fun S hS => ?_
    simp [hoff S hS]
  have hyc : Measurable fun q : Y × C => ∫⁻ v in U, f q.1 q.2 v ∂μ := by
    have : Measurable fun r : (Y × C) × X => f r.1.1 r.1.2 r.2 :=
      hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact this.lintegral_prod_right'
  calc ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁
      = ∫⁻ y, ∫⁻ c, ∫⁻ v in U, f y c v ∂μ ∂μc ∂μ₁ := by simp only [e1]
    _ = ∫⁻ c, ∫⁻ y, ∫⁻ v in U, f y c v ∂μ ∂μ₁ ∂μc :=
        lintegral_lintegral_swap (f := fun y c => ∫⁻ v in U, f y c v ∂μ) hyc.aemeasurable
    _ = ∫⁻ c, ∫⁻ v in U, ∫⁻ y, f y c v ∂μ₁ ∂μ ∂μc := by
        refine lintegral_congr fun c => ?_
        exact lintegral_lintegral_swap (f := fun y v => f y c v) (hfc c).aemeasurable
    _ = ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by
        refine lintegral_congr fun c => ?_
        rw [hfib _ (hfc c).lintegral_prod_left']
        rw [restr]
        · refine lintegral_congr fun S => ?_
          haveI := hm S
          exact lintegral_lintegral_swap (f := fun v y => f y c v)
            ((hfc c).comp measurable_swap).aemeasurable
        · intro S hS
          simp [hoff S hS]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem lintegral_Uset_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hCM := D.hCM
  have hlam := D.hlam
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id D.hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hlf1, -, -, -, hae1⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hCM (M + 1) 1 _ hJ' R D.hR d b lam hlam m₁ D.hm₁
  obtain ⟨hUo, hlf, hoff, -, -, -⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hCM M n J D.hJ R D.hR d b lam hlam m' D.hm'
  obtain ⟨-, -, h₃, -, h₅, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  have hc := (hact (n + 1)).1
  haveI := hBorel n M
  haveI := hBorel (n + 1) (M + 1)
  haveI := hBorel 1 (M + 1)
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := inferInstance
  haveI : SigmaFinite (m₁ (hermScal R σ (algebraMap F R t))) := inferInstance
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : SFinite (Measure.pi fun _ : Fin n => coordK R b lam) := inferInstance
  have hm : ∀ S, SFinite (m' S) := fun S => inferInstance
  have hUm : MeasurableSet (Unt σ R n) := hUo.measurableSet
  have hB : MeasurableSet B₀ := D.hB₀.measurableSet
  rw [GlobalTheory.T.gram_fiber_cons_product_unfold F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ]
  unfold Mid
  refine setLIntegral_congr_fun hB fun x hx => ?_
  refine congrArg _ ?_
  set f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → (Fin n → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ :=
    fun y₀ c X => φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) with hfdef
  have hf : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      f p.1 p.2.1 p.2.2 := by
    have hcm : Measurable (fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) p.1 p.2) := by
      haveI : SecondCountableTopology (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J)) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
        Prod.opensMeasurableSpace
      exact hc.measurable
    have hg : Measurable (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        ((s p.1, vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) p.2.1 p.2.2) :
          HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))) :=
      (D.hs.comp measurable_fst).prodMk
        ((Unfold.measurable_vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))).comp measurable_snd)
    exact hφ.comp (hcm.comp hg)
  have hae : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ)
          (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) =
        ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, f y₀ c X ∂(m' S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
    filter_upwards [hae1 (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    exact GlobalTheory.T.gram_fiber_cons_product_fold F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  rw [lintegral_congr_ae hae]
  exact Unfold.swap_through_fibres (m₁ (hermScal R σ (algebraMap F R t)))
    (Measure.pi fun _ => coordK R b lam) (coordW R b lam n M) (coordHerm R σ b lam n)
    {X | IsUnit (gramR R σ J X).det} (Unt σ R n) hUm m' hm hoff D.hm'.2.1 f hf

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_Uset_coordW_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid <;> assumption)
end
