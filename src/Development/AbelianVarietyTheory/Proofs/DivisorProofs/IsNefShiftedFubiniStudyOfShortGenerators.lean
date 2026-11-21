import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinearStatement

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem smallSec_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ t hw ht j hj τ y
  obtain ⟨N, n', b, g, A, c, gw, hF, hgw, hb, hφ⟩ := hM.fs
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ :=
    ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp τ⟩
  refine (le_of_eq (GlobalTheory.HermLB.nsq_shift L (fun _ => t) (fun _ => rfl)
    (GlobalTheory.CxPts.secVal p _ (s ⟨w j, hj⟩)) y)).trans ?_
  set i := GlobalTheory.CxPts.pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y with hi_def
  have hi := GlobalTheory.CxPts.mem_pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y
  rw [GlobalTheory.Weight.nsq_eq _ (GlobalTheory.CxPts.secVal_mem _) hi, GlobalTheory.CxPts.secVal_apply, hφ σ i y]
  set ℓ : W → ℂ := fun x => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) with hℓ
  have hlin : ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) →
      ℓ x = ∑ k, σ (β k : K) * ℓ (u k) := fun m β u x hx =>
    GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hi m β u x hx
  have hbd := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n' b g A c gw σ ℓ hF hgw hb hlin ⟨w j, hj⟩
  set S := ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hev' : GlobalTheory.CxPts.ev p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) ((s ⟨w j, hj⟩).f i) y = ℓ ⟨w j, hj⟩ := rfl
  rw [hev']
  have hNm0 : 0 ≤ Nm σ (w j) := by
    rw [← hF.norm σ (w j)]; exact Real.sqrt_nonneg _
  have hNm : Nm σ (w j) ≤ abelian₂ := hw.le j σ
  have hLam0 : 0 < abelian₂ := lt_of_lt_of_le one_pos hw.one_le
  have hLt : abelian₂ ≤ Real.exp t := (Real.log_le_iff_le_exp hLam0).1 ht
  have hLam2 : abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ 1 := by
    have h1 : abelian₂ ^ 2 ≤ Real.exp t ^ 2 := pow_le_pow_left₀ hLam0.le hLt 2
    have h2 : Real.exp t ^ 2 * Real.exp (-(2 * t)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    calc abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ Real.exp t ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := h2
  rcases hS0.eq_or_lt with h0 | hpos
  · have : ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ 0 := by simpa [← h0] using hbd
    have hz : ‖ℓ ⟨w j, hj⟩‖ ^ 2 = 0 := le_antisymm this (sq_nonneg _)
    rw [hz]; simp
  · rw [Real.exp_neg, Real.exp_log hpos]
    have h3 : ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ ≤ abelian₂ ^ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ Nm σ (w j) ^ 2 * S := hbd
        _ ≤ abelian₂ ^ 2 * S := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNm0 hNm 2) hS0
    calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ * Real.exp (-(2 * t)) ≤ abelian₂ ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ 1 := hLam2

end GlobalTheory.ImageModel
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  atlas_forward_decl GlobalTheory.ImageModel.smallSec_shift_of_isShortGen
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelSemi

open GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem semiPos_of_isModelOf : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  intro τ
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := ⟨_, extEmb_comp τ⟩
  let M : Matrix (Fin n) (Fin N) ℂ := fun k a => ∑ m, σ (c k m) * A σ m a
  have hz : Weight.NoCommonZero fun a =>
      ∑ j, M j a • secVal p (σ.comp (algebraMap (𝓞 K) K)) (s (gw j)) := by
    intro i y hy
    by_contra! h0
    have hS : ∑ a, ‖∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have h1 := h0 a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [show (∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)) = 0 from h1]
      simp
    obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
    have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
    have hb := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
      (fun m β u x hx => GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
    rw [hS, mul_zero] at hb
    exact hne (by
      have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
      exact norm_eq_zero.1 this)
  have key : (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ = (combWeight L.isLB (fun k => s (gw k)) M hz).φ :=
    funext fun i => funext fun y => (hφ σ i y).trans (combWeight_φ L.isLB (fun k => s (gw k)) M hz i y).symm
  intro i ch y hy ξ
  have := semiPosReg_combWeight L.isLB (fun k => s (gw k)) M hz D i ch y hy ξ
  rw [key]
  exact this

end GlobalTheory.ImageModelSemi
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imageModel_metrics_semiPositive : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  atlas_forward_decl GlobalTheory.ImageModelSemi.semiPos_of_isModelOf
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem horizontal_of_small : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), GlobalTheory.IsArithVar p D → ∀ (L : GlobalTheory.HermLB p), (∀ x : X, ∃ u ∈ L.smallSec, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) → ∀ (Z : AlgebraicGeometry.Scheme.{0}) (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z] [AlgebraicGeometry.IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 → ∃ (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec (L.restr i).B r), 0 ≤ (L.restr i).curveDeg hr := by
  intro k _ X p D hX L hL Z i _ _ _ hc hd
  have hZ : GlobalTheory.IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  obtain ⟨u, hu1, hu⟩ := hL (i (genericPoint Z))
  have hu' : genericPoint Z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact hu
  have h0 : ∀ σ (y : GlobalTheory.CxPts (i ≫ p) σ), y ∈ GlobalTheory.CxPts.ptsIn _ σ
      (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
    rw [GlobalTheory.CxPts.mem_ptsIn]
    have e := hZ.under_eq_genericPoint y
    simp only [GlobalTheory.Cartier.under] at e
    rw [e]
    exact hu'
  refine ⟨_, GlobalTheory.Cartier.isRatSec_ratOfSec _ hu', ?_⟩
  rw [GlobalTheory.HermLB.curveDeg_sec (L := L) i _ hu' h0]
  refine sub_nonneg.2 (le_trans ?_ (finsum_nonneg fun z => mul_nonneg
    (by exact_mod_cast GlobalTheory.Cartier.mult_divOfSec_nonneg z) (Real.log_natCast_nonneg _)))
  rw [← neg_nonneg, ← finsum_neg_distrib]
  refine finsum_nonneg fun σ => ?_
  rw [← finsum_neg_distrib]
  refine finsum_nonneg fun y => ?_
  have h1 := hu1 σ (GlobalTheory.Points.PtsOver.map i rfl _ y)
  have h2 := GlobalTheory.Weight.nsq_nonneg (L.φ σ) (GlobalTheory.CxPts.secVal _ σ u) (GlobalTheory.Points.PtsOver.map i rfl _ y)
  have h3 := Real.log_nonpos h2 h1
  linarith

theorem isNef_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s n w abelian₂ t hM hev hS ht
  have hw : ∀ j, w j ∈ W := fun j => (hS.gen _).2 (Submodule.subset_span ⟨j, rfl⟩)
  have hX : GlobalTheory.IsArithVar p D := hM.arith
  have hg := GlobalTheory.T.exists_nonzero_shortGenerator_section_imageModel K V Ω Nm W ev D X p L ψ s hM hev n w abelian₂ hS
  have hs := GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy K V Ω Nm W ev D X p L ψ s hM hev n w abelian₂ t hS ht
  refine ⟨(GlobalTheory.T.imageModel_metrics_semiPositive K V Ω Nm W ev D X p L ψ s hM hev).shift _ _, ?_, ?_⟩
  · refine GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX _ (GlobalTheory.isGenerated_of_finite (fun j => s ⟨w j, hw j⟩) ?_)
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨j, hj, hx⟩ := hg x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx⟩
  · intro Z i _ _ _ hc hd
    exact horizontal_of_small _ X p D hX _ (fun x => by
      obtain ⟨j, hj, hx⟩ := hg x
      exact ⟨_, hs j hj, hx⟩) Z i hc hd

end GlobalTheory.ImageModel
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  atlas_forward_decl GlobalTheory.ImageModel.isNef_shift_of_isShortGen
end
