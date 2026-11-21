import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.InhHasFDerivAtNormSq
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.AnReadModel

open GlobalTheory.CxPts GlobalTheory.AnRead

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem volume_ball_one : volume (Metric.ball (0 : V 1) 1) = ENNReal.ofReal Real.pi := by
  have h : Module.finrank ℝ (V 1) = 2 * 1 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (V 1)]; simp
  rw [InnerProductSpace.volume_ball_of_dim_even h]
  simp

theorem topInt_pos [SmoothOfRelativeDimension D p] [SecondCountableTopology (CxPts p σ)] {B : LB Y}
    (K : CanonLB p D) {φ : Weight p σ B} {f : (tens K.bundle B).ι → CxPts p σ → ℂ}
    {R : AnRead p σ D} (hφ : φ.IsSmooth R) (hf : f ∈ R.holSec (tens K.bundle B))
    {j : (tens K.bundle B).ι} {y : CxPts p σ} (h0 : f j y ≠ 0) : 0 < R.topInt K φ f := by
  have hj : y ∈ ptsIn p σ ((tens K.bundle B).U j) := by
    by_contra h; exact h0 (hf.1.2 j y h)
  obtain ⟨a, b⟩ := j
  obtain ⟨ha, hb⟩ := mem_ptsIn_inf.1 hj
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let S := ptsIn p σ (c.U ⊓ K.bundle.U a) ∩ ptsIn p σ (B.U b)
  have hS : IsOpen S := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hc : ContinuousOn (fun v => c.topDens K φ f (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' S) := by
    have h₁ := (holoOn_ev_of_subset (R := R) (c.isFrame.ratio (K.isFrame a)).val
      (inter_subset_left (t := ptsIn p σ (B.U b)))).mul
      ((hf.2 (a, b)).mono
        fun _ hz => mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hz.1).2, hz.2⟩) i
    have h₂ := (hφ b).mono (inter_subset_right : S ⊆ _) i
    exact (continuousOn_const.mul ((h₁.continuousOn.norm.pow 2).mul h₂.continuousOn.neg.rexp)).congr
      fun v hv => c.topDens_eq K φ hf.1 (c.e.map_target hv.1) (mem_ptsIn_inf.1 hv.2.1).2 hv.2.2
  have hyS : y ∈ S := ⟨mem_ptsIn_inf.2 ⟨c.source_subset hi, ha⟩, hb⟩
  have hpos : 0 < c.topDens K φ f (c.e.symm (c.e y)) := by
    rw [c.e.left_inv hi, c.topDens_eq K φ hf.1 hi ha hb]
    have : c.topCoeff K f a b y ≠ 0 :=
      mul_ne_zero (rv_ne_zero _ _ (c.source_subset hi) ha) h0
    positivity
  have ho := isOpen_over c.e hS
  have hO := hc.isOpen_inter_preimage ho (isOpen_Ioi (a := c.topDens K φ f (c.e.symm (c.e y)) / 2))
  have hA : IsOpen (c.e.source ∩ S) := c.e.open_source.inter hS
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ (c.e.source ∩ S)))
  rw [R.topMeasure_apply K φ f c hA.measurableSet inter_subset_left, c.e.image_source_inter_eq']
  refine lt_of_lt_of_le ?_ (lintegral_mono_set inter_subset_left (s := (c.e.target ∩ c.e.symm ⁻¹' S) ∩
    (fun v => c.topDens K φ f (c.e.symm v)) ⁻¹' Ioi (c.topDens K φ f (c.e.symm (c.e y)) / 2)))
  refine lt_of_lt_of_le ?_ (setLIntegral_mono' hO.measurableSet
    (f := fun _ => ENNReal.ofReal (c.topDens K φ f (c.e.symm (c.e y)) / 2))
    fun v hv => ENNReal.ofReal_le_ofReal (le_of_lt hv.2))
  rw [setLIntegral_const]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne'
    (hO.measure_pos _ ⟨c.e y, mem_over c.e hi hyS, half_lt_self hpos⟩).ne'

open ProjSpace in

theorem topInt_jac (N : ℕ) (K : CanonLB (PSpace.str k N) N) (R : AnRead (PSpace.str k N) σ N) :
    0 < R.topInt K ((ProjAn.fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) ∧
      R.topInt K ((ProjAn.fsO1 k σ N).pow (N + 1)) (secVal _ σ (K.jacSec (coord k N))) < ⊤ := by
  have hs := (Weight.isSmooth_fsBasis (R := R) (O1_isLB k N) (coord k N)
    (iSup_nonzeroLocus_coord k N) 1 (by simp)).zpow ((N + 1 : ℕ) : ℤ)
  refine ⟨?_, topInt_lt_top K hs (R.secVal_mem_holSec _)⟩
  let y : CxPts (PSpace.str k N) σ := projPt σ ⟨fun _ => 1, (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span ⟨0, rfl⟩)⟩
  obtain ⟨_, h⟩ := ProjAn.noCommonZero_jac k σ N K _ y (mem_pick (K.isLB_adj (O1_isLB k N) _) y)
  exact topInt_pos K hs (R.secVal_mem_holSec _) h

def X (a : Fin D) : CxPts (CanonLB.affStr k D) σ → ℂ :=
  ev _ σ ⊤ (CanonLB.polyFn (MvPolynomial.X a))

def origin : CxPts (CanonLB.affStr k D) σ :=
  ofHom (isAffineOpen_top _) ((MvPolynomial.eval₂Hom σ fun _ => 0).comp
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).hom.hom) fun a => by
    have := RingHom.congr_fun (CanonLB.polyFn_comp k D) a
    rw [← this]
    simp [CanonLB.polyFn]

theorem exists_std (y : CxPts (CanonLB.affStr k D) σ) :
    ∃ c : AlgChart (CanonLB.affStr k D) σ D, y ∈ c.e.source ∧
      ∀ z ∈ c.e.source, ∀ a, c.e z a = X a z := by
  have he : MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a)) = CanonLB.polyFn :=
    MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans
      (RingHom.congr_fun (CanonLB.polyFn_comp k D) a).symm) fun a => MvPolynomial.eval₂Hom_X' _ _ a
  have het : (MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
      (fun a => CanonLB.polyFn (MvPolynomial.X a))).Etale := by
    rw [he]
    exact RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv)
  obtain ⟨⟨e, U, hU, x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale
    (isAffineOpen_top _) _ het (mem_ptsIn_top (y := y))
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, h₂⟩

theorem holo_X (R : AnRead (CanonLB.affStr k D) σ D) (a : Fin D) : R.HoloOn univ (X a) :=
  holoOn_ev_of_subset _ fun _ _ => mem_ptsIn_top


def sq (t : ℝ) (z : CxPts (CanonLB.affStr k D) σ) : ℝ := t * ∑ a, Complex.normSq (X a z)

theorem smooth_sq (R : AnRead (CanonLB.affStr k D) σ D) (t : ℝ) :
    (Weight.ofFun (sq t)).IsSmooth R := Weight.isSmooth_ofFun fun i =>
  contDiffOn_const.mul (ContDiffOn.sum (f := fun a v => Complex.normSq (X a ((R.chart i).e.symm v)))
    fun a _ => by
      simp only [Complex.normSq_eq_norm_sq]
      exact (contDiffOn_real (isOpen_over _ isOpen_univ) (holo_X R a i)).norm_sq ℂ)




end GlobalTheory.AnReadModel
